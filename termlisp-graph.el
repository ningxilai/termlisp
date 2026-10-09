;;; termlisp-graph.el --- Term graph rewriting core -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A term is a graph of mutable nodes (head + children + state + memo).
;; Children are shared node references (hash-consing on build).  Rules
;; rewrite nodes in place; reduction is strict and phase/priority ordered.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

;; Clause-based rules are dispatched by `termlisp-case', which builds on this
;; file; the declarations avoid a circular `require' at load time.
(declare-function tl-graph-apply-crule "termlisp-case" (node rule))
(declare-function tl-graph-crule-applicable-p "termlisp-case" (node rule))
(declare-function tl-pat-dispatch-heads "termlisp-case" (pat))

(cl-defstruct (tl-node (:constructor tl-make-node (head &optional children application)))
  "A term graph node.
HEAD is a symbol/atom operator (or a literal value for leaves).
CHILDREN is a list of child `tl-node's (shared).
APPLICATION is non-nil when the node was written as an application `(HEAD ...)',
distinguishing a nullary application `(a)' from the atom `a'.
STATE is a control marker (:idle, :active, :done).
MEMO is the node's rewritten replacement, or nil.

The remaining slots are for graph unification (see `termlisp-graph-unify'):
VAR marks a unification variable node, BIND is its union-find parent
(nil for a representative), and RANK orders unions.  They are disjoint
from STATE/MEMO, which serve term rewriting."
  head children (application nil) (state :idle) memo
  (var nil) (bind nil) (rank 0))

(cl-defstruct (tl-graph (:constructor tl-make-graph (root table)))
  "A term graph: ROOT node plus a sharing TABLE (sexp-key -> node)."
  root table)

(defconst tl-graph-opaque-heads '(quote function)
  "Heads whose subterms are never rewritten or descended into (opaque data).")

(defun tl-graph-build (sexp)
  "Build a term graph from SEXP, sharing structurally identical subterms.
A subterm whose head is in `tl-graph-opaque-heads' becomes a single opaque
leaf holding the whole subterm, so deep quoted data is neither traversed
nor rebuilt."
  (let ((table (make-hash-table :test #'equal)))
    (cl-labels ((build (x)
                  (or (gethash x table)
                      (let ((node (cond
                                   ((and (consp x)
                                         (memq (car x) tl-graph-opaque-heads))
                                    (tl-make-node x nil nil))
                                   ((consp x)
                                    (tl-make-node (car x)
                                                  (mapcar #'build (cdr x))
                                                  t))
                                   (t (tl-make-node x nil nil)))))
                        (puthash x node table)
                        node))))
      (tl-make-graph (build sexp) table))))

(defun tl-node->sexp (node)
  "Render NODE (and its children) back to an s-expression.
An application node renders as `(HEAD ...)', including nullary `(HEAD)';
a non-application node renders as its atom HEAD."
  (if (tl-node-application node)
      (cons (tl-node-head node) (mapcar #'tl-node->sexp (tl-node-children node)))
    (tl-node-head node)))

(cl-defstruct (tl-grule (:constructor tl-make-grule (name phase priority pattern template &optional guard clauses)))
  "A term-graph rewrite rule.
NAME identifies the rule; PHASE and PRIORITY order its application.
PATTERN is matched against a node, TEMPLATE instantiated to rewrite it.
GUARD, when non-nil, is called with the bindings and must return non-nil.

A clause-based rule leaves PATTERN and TEMPLATE nil and stores a list of
`(PATTERN . TEMPLATE)' CLAUSES instead (see `tl-make-crule'); its decision
tree is compiled lazily into COMPILED and memoised on the rule."
  name phase priority pattern template guard clauses compiled)

(defun tl-make-crule (name phase priority clauses &optional guard)
  "Construct a clause-based term-graph rewrite rule.
CLAUSES is a list of `(PATTERN . TEMPLATE)' whose PATTERNs come from
`tl-pat-parse' (see `termlisp-case').  The rule is applied by compiling the
clauses into a decision tree once and dispatching the node through it, so
variadic rules can be written with list patterns and `(prest NAME)' instead
of `(:rest)'/`(:splice)'/function templates."
  (tl-make-grule name phase priority nil nil guard clauses))

(defconst tl-graph--match-ok (list (cons 'tl-graph-match-ok t))
  "Sentinel binding alist returned for a match with no variables.
Distinguishes a successful match with an empty binding set from failure.
A proper alist so guards may safely iterate its entries.")

(defun tl-graph--pvar-p (x)
  "Return non-nil if X is a pattern variable (a symbol named \"$...\")."
  (and (symbolp x)
       (> (length (symbol-name x)) 0)
       (eq (aref (symbol-name x) 0) ?$)))

(defun tl-graph--rest-p (x)
  "Return non-nil if X is a `(:rest $name)' pattern element."
  (and (consp x) (eq (car x) :rest) (tl-graph--pvar-p (cadr x))))

(defun tl-graph--splice-p (x)
  "Return non-nil if X is a `(:splice $name)' template element."
  (and (consp x) (eq (car x) :splice) (tl-graph--pvar-p (cadr x))))

(defun tl-graph--bind-rest (pattern nodes bindings)
  "Extend BINDINGS with the rest variable of PATTERN bound to NODES.
If the variable is already bound, the existing list must be `equal'."
  (let* ((var (cadr pattern))
         (cell (assq var bindings)))
    (cond ((null cell) (cons (cons var nodes) bindings))
          ((equal (cdr cell) nodes) bindings)
          (t nil))))

(defun tl-graph-match (pattern node bindings)
  "Match PATTERN against NODE, extending BINDINGS.  Return bindings or nil."
  (cond
   ((tl-graph--pvar-p pattern)
    (let ((cell (assq pattern bindings)))
      (if cell (if (eq (cdr cell) node) bindings nil)
        (cons (cons pattern node) bindings))))
   ((consp pattern)
    (when (and (tl-node-application node)
               (eq (tl-node-head node) (car pattern)))
      (tl-graph-match-seq (cdr pattern) (tl-node-children node) bindings)))
   (t
    (when (and (not (tl-node-application node))
               (eq (tl-node-head node) pattern))
      (or bindings tl-graph--match-ok)))))

(defun tl-graph-match-seq (patterns nodes bindings)
  "Match PATTERNS against NODES in order, extending BINDINGS.
A final `(:rest $name)' element captures the remaining NODES as a list."
  (let ((ok t))
    (while (and patterns ok)
      (cond
       ((tl-graph--rest-p (car patterns))
        (unless (null (cdr patterns))
          (signal 'termlisp-eval-error
                  '("A :rest pattern must be the last list element")))
        (setq bindings (tl-graph--bind-rest (car patterns) nodes bindings))
        (unless bindings (setq ok nil))
        (setq patterns nil nodes nil))
       ((null nodes) (setq ok nil))
       (t
        (setq bindings (tl-graph-match (car patterns) (car nodes) bindings))
        (unless bindings (setq ok nil))
        (setq patterns (cdr patterns) nodes (cdr nodes)))))
    (when (and ok (null patterns) (null nodes))
      (or bindings tl-graph--match-ok))))

(defun tl-graph-instantiate-list (templates bindings)
  "Instantiate TEMPLATES in order, splicing `(:splice $name)' elements."
  (let (out)
    (dolist (template templates)
      (if (tl-graph--splice-p template)
          (let ((cell (assq (cadr template) bindings)))
            (unless cell
              (signal 'termlisp-eval-error
                      (list (format "Unbound splice variable: %S"
                                    (cadr template)))))
            (dolist (node (cdr cell)) (push node out)))
        (push (tl-graph-instantiate template bindings) out)))
    (nreverse out)))

(defun tl-graph--function-template-p (template)
  "Return non-nil if TEMPLATE is a function template.
A literal `(lambda ...)' form is data, not a template, even though
`functionp' accepts it."
  (and (functionp template)
       (not (symbolp template))
       (not (and (consp template) (eq (car template) 'lambda)))))

(defun tl-graph-instantiate (template bindings)
  "Instantiate TEMPLATE into a node, reusing nodes bound in BINDINGS.
TEMPLATE may be a variable, a list template, or a function of BINDINGS
returning either a node or a further template sexp."
  (cond
   ((tl-graph--function-template-p template)
    (let ((result (funcall template bindings)))
      (if (tl-node-p result)
          result
        (tl-graph-instantiate result bindings))))
   ((tl-graph--pvar-p template)
    (let ((cell (assq template bindings)))
      (if cell
          (cdr cell)
        (signal 'termlisp-eval-error
                (list (format "Unbound template variable: %S" template))))))
   ((consp template)
    (tl-make-node (car template)
                  (tl-graph-instantiate-list (cdr template) bindings)
                  t))
   (t (tl-make-node template nil nil))))

(defun tl-graph--commit (node rule new)
  "Replace NODE's contents with NEW.  Return t, or signal on no progress.
Shared by the pattern/template path and the clause-based path so both
enforce the same in-place-update and non-progressing-rewrite contract."
  (if (and (eq (tl-node-head node) (tl-node-head new))
           (eq (tl-node-application node) (tl-node-application new))
           (equal (tl-node-children node) (tl-node-children new)))
      (signal 'termlisp-eval-error
              (list (format "Non-progressing rewrite: %S" (tl-grule-name rule))))
    (setf (tl-node-head node) (tl-node-head new))
    (setf (tl-node-application node) (tl-node-application new))
    (setf (tl-node-children node) (tl-node-children new))
    t))

(defun tl-graph-apply (node rule)
  "If RULE matches NODE, rewrite NODE in place.  Return t, or nil if no match.
A clause-based rule (see `tl-make-crule') is dispatched through its compiled
case tree; otherwise PATTERN/TEMPLATE are used as before.
Signals `termlisp-eval-error' if the rewrite makes no progress."
  (if (tl-grule-clauses rule)
      (tl-graph-apply-crule node rule)
    (let ((bindings (tl-graph-match (tl-grule-pattern rule) node nil)))
      (when (and bindings
                 (or (null (tl-grule-guard rule))
                     (funcall (tl-grule-guard rule) bindings)))
        (tl-graph--commit node rule
                          (tl-graph-instantiate (tl-grule-template rule)
                                                bindings))))))

(defconst tl-graph-phases
  '(:surface :normalize :desugar :context :control :load :action :backend)
  "Reduction phases, applied in order.  Rules only move forward.")

(defun tl-graph--preorder (node &optional seen)
  "Return NODE and its descendants in pre-order, without revisiting nodes.
Does not descend into opaque subterms (`tl-graph-opaque-heads')."
  (let ((seen (or seen (make-hash-table :test #'eq))))
    (unless (gethash node seen)
      (puthash node t seen)
      (cons node
            (unless (memq (tl-node-head node) tl-graph-opaque-heads)
              (mapcan (lambda (c) (tl-graph--preorder c seen))
                      (tl-node-children node)))))))

(defun tl-graph--rules-for (phase rules)
  "Rules of PHASE, sorted by ascending priority."
  (sort (cl-remove-if-not (lambda (r) (eq (tl-grule-phase r) phase)) rules)
        (lambda (a b) (< (tl-grule-priority a) (tl-grule-priority b)))))

(defun tl-graph--rule-heads (rule)
  "Return the head values RULE may match, or `:generic'.
A clause-based rule dispatches on the heads of its clauses' patterns, so it
is indexed under their union; a clause that is irrefutable (a variable,
wildcard or rest pattern) makes the whole rule generic.  A pattern/template
rule indexes under its pattern's head, or is generic for a variable pattern."
  (if (tl-grule-clauses rule)
      (let ((heads nil))
        (catch 'generic
          (dolist (clause (tl-grule-clauses rule))
            (let ((hs (tl-pat-dispatch-heads (car clause))))
              (if (eq hs :generic)
                  (throw 'generic :generic)
                (dolist (head hs)
                  (cl-pushnew head heads :test #'equal)))))
          heads))
    (let ((pattern (tl-grule-pattern rule)))
      (cond ((tl-graph--pvar-p pattern) :generic)
            ((consp pattern) (list (car pattern)))
            (t (list pattern))))))

(defun tl-graph--merge-by-pos (a b pos)
  "Merge rule lists A and B, ordered by their position recorded in POS."
  (let (out)
    (while (and a b)
      (if (< (gethash (car a) pos) (gethash (car b) pos))
          (setq out (cons (car a) out) a (cdr a))
        (setq out (cons (car b) out) b (cdr b))))
    (while a (setq out (cons (car a) out) a (cdr a)))
    (while b (setq out (cons (car b) out) b (cdr b)))
    (nreverse out)))

(defun tl-graph--rule-dispatch (rules)
  "Index priority-ordered RULES by the node head they can match.
Return `(GENERIC . TABLE)': GENERIC is the ordered list of rules that may
match any head; TABLE maps a head to the ordered list of rules indexed under
it, with GENERIC merged in so a single lookup yields every rule to try."
  (let ((generic nil)
        (specific (make-hash-table :test #'equal))
        (pos (make-hash-table :test #'eq))
        (i 0))
    (dolist (rule rules)
      (puthash rule i pos)
      (setq i (1+ i))
      (let ((heads (tl-graph--rule-heads rule)))
        (if (eq heads :generic)
            (push rule generic)
          (dolist (head heads)
            (puthash head (cons rule (gethash head specific)) specific)))))
    (setq generic (nreverse generic))
    (let ((table (make-hash-table :test #'equal)))
      (maphash (lambda (head rs)
                 (puthash head
                          (tl-graph--merge-by-pos (nreverse rs) generic pos)
                          table))
               specific)
      (cons generic table))))

(defun tl-graph--step (graph dispatch)
  "Apply one highest-priority leftmost-outermost rewrite.  Return t if any.
DISPATCH is a `(GENERIC . TABLE)' index from `tl-graph--rule-dispatch'; only
the rules indexed under a node's head (plus the generic ones) are tried.
The graph is walked in pre-order with early exit, so no full node list is
built and the scan stops at the first applicable rule."
  (let ((generic (car dispatch))
        (table (cdr dispatch))
        (seen (make-hash-table :test #'eq)))
    (cl-labels ((walk (node)
                  (unless (gethash node seen)
                    (puthash node t seen)
                    (catch 'applied
                      (dolist (rule (or (gethash (tl-node-head node) table)
                                        generic))
                        (when (tl-graph-apply node rule)
                          (throw 'applied t)))
                      (unless (memq (tl-node-head node) tl-graph-opaque-heads)
                        (catch 'descend
                          (dolist (child (tl-node-children node))
                            (when (walk child)
                              (throw 'descend t)))))))))
      (walk (tl-graph-root graph)))))

(defun tl-graph-rewrite (graph rules &optional fuel)
  "Strictly reduce GRAPH to normal form using RULES, phase by phase.
Signals `termlisp-eval-error' when FUEL (default 10000) is exhausted."
  (let ((remaining (or fuel 10000)))
    (dolist (phase tl-graph-phases graph)
      (let ((dispatch (tl-graph--rule-dispatch (tl-graph--rules-for phase rules))))
        (unless (and (null (car dispatch))
                     (zerop (hash-table-count (cdr dispatch))))
          (let ((progress t))
            (while progress
              (when (<= remaining 0)
                (signal 'termlisp-eval-error '("TGR fuel exhausted")))
              (setq remaining (1- remaining))
              (setq progress (tl-graph--step graph dispatch)))))))))

(defun tl-graph-rewrite-sexp (sexp rules &optional fuel)
  "Build a graph from SEXP, strictly reduce it with RULES, and render it back."
  (tl-node->sexp (tl-graph-root (tl-graph-rewrite (tl-graph-build sexp) rules fuel))))

(defun tl-graph-normal-form-p (graph rules)
  "Return non-nil if no rule applies anywhere in GRAPH."
  (let* ((dispatch (tl-graph--rule-dispatch rules))
         (generic (car dispatch))
         (table (cdr dispatch)))
    (catch 'reducible
      (dolist (node (tl-graph--preorder (tl-graph-root graph)))
        (dolist (rule (or (gethash (tl-node-head node) table) generic))
          (when (if (tl-grule-clauses rule)
                    (tl-graph-crule-applicable-p node rule)
                  (let ((bindings (tl-graph-match (tl-grule-pattern rule) node nil)))
                    (and bindings
                         (or (null (tl-grule-guard rule))
                             (funcall (tl-grule-guard rule) bindings)))))
            (throw 'reducible nil))))
      t)))

(provide 'termlisp-graph)
;;; termlisp-graph.el ends here
