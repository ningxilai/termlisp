;;; termlisp-graph.el --- Term graph rewriting core -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A term is a graph of nodes (head + children + state + memo).
;; Children are shared node references (hash-consing on build).  A rule
;; computes a reduct and the walk installs it with `copy-tl-node', so a
;; node that is reachable from more than one place -- which every node of
;; a *type* is -- is never edited behind the caller's back.  Reduction is
;; strict and phase/priority ordered.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

;; Clause-based rules are dispatched by `termlisp-case', which builds on this
;; file; the declarations avoid a circular `require' at load time.
(declare-function tl-graph-crule-reduce "termlisp-case" (node rule))
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
(nil for a representative), and RANK orders unions.  KIND is the node's
kind arity when known (see `termlisp-kinds'): 0 for a proper type, n>0 for
a type constructor expecting n arguments, nil when unknown.  They are
disjoint from STATE/MEMO, which serve term rewriting.

RIGID distinguishes a *bound* variable from an ordinary one.  A `Pi'
binder introduces a variable that is already fixed by its binder, so
traversal and substitution still act on it (VAR is set) but unification
may only ever match it against itself -- binding it would be unsound.

LEVEL records the generalization scope a variable was introduced in (see
`tl-current-level'): nil for a variable that predates them all, and
otherwise an integer that grows the deeper the scope sits.  It is what
lets generalization ask \"was this variable already in scope here?\"
without walking the environment, and what lets unification refuse to
hand an outer variable an inner one."
  head children (application nil) (state :idle) memo
  (var nil) (bind nil) (rank 0) (kind nil) (rigid nil) (level nil))

(cl-defstruct (tl-graph (:constructor tl-make-graph (root table)))
  "A term graph: ROOT node plus a sharing TABLE (sexp-key -> node)."
  root table)

(defconst tl-graph-opaque-heads '(quote function)
  "Heads whose subterms are never rewritten or descended into (opaque data).")

(defvar tl-graph-whnf nil
  "Function of one node returning its weak head normal form, or nil.
A host that reduces *while it matches* binds this: the type layer cannot
tell that `plus Zero n' is a `Succ' without reducing it first, so a clause
whose argument is not yet in constructor form would otherwise be missed and
the type reported as unequal.  Nil means no reduction, which keeps a plain
syntactic rewrite purely structural.")

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

(defvar tl--display-names nil
  "Display-name table for one rendering, or nil when no rendering is in force.
The value is a cons cell whose CDR is an alist of (NODE . NAME), grown
by `tl-node-display'.  It is the cell rather than the alist that is
tested, because an empty alist and no alist are both nil -- and a
rendering has to register the first name it hands out against a table
that is still empty, or nothing after it can ever be told apart.

Identity here is `eq' on the node, so two distinct variables that share
a print name come out differently in one message -- exactly as Common
Lisp qualifies a symbol with its package when that is not the package
on `*package*'.

This exists so that nothing has to read a name to decide what a variable
*is*.  A name is what a variable is called and nothing more; the
substitution that decides what it is compares nodes.  Where that
distinction is kept, a name may be copied freely -- a freshened binder
keeps its name and takes a new node -- and the messages that read kinds
back say `Π(a : *).' instead of `Π(t897 : *).', without the copy being
mistaken for the original anywhere.")

(defun tl-node-display (node)
  "Return NODE's display name within the current rendering.
Only a variable is ever qualified: two variables that share a name may
be two different variables, while two constructor names that share one
are one constructor, and marking the second `Nat' as `Nat'' would say
something untrue about the type.  The first variable seen with a given
name keeps it; a later distinct one is primed -- `a', then `a'', then
`a''' -- and only within the rendering that asked.  With no table in
force the node's own name comes back unchanged, which is all that
happens outside a message."
  (let ((name (tl-node-head node)))
    (if (or (null tl--display-names) (not (tl-node-var node)))
        name
      (or (cdr (assq node (cdr tl--display-names)))
          (let ((taken (mapcar #'cdr (cdr tl--display-names)))
                (candidate name)
                (n 0))
            (while (member candidate taken)
              (setq n (1+ n)
                    candidate (intern (format "%s%s" name (make-string n ?')))))
            (setcdr tl--display-names
                    (cons (cons node candidate) (cdr tl--display-names)))
            candidate)))))

(defmacro tl-with-display-names (&rest body)
  "Evaluate BODY with a fresh display-name table in force.
One table per rendering: a message shows one kind or one type, and two
variables with the same name inside that one rendering are two different
variables worth telling apart.  Across renderings nothing is carried, so
no name is ever qualified on a stability the table cannot promise."
  (declare (indent 0) (debug t))
  ;; `(cons nil nil)' rather than nil: an empty table, which is to say
  ;; a table that is already present and not yet populated.
  `(let ((tl--display-names (cons nil nil)))
     ,@body))

(defun tl-node->sexp (node)
  "Render NODE (and its children) back to an s-expression.
An application node renders as `(HEAD ...)', including nullary `(HEAD)';
a non-application node renders as its atom HEAD, qualified by
`tl-node-display' when a display-name table is in force."
  (if (tl-node-application node)
      (cons (tl-node-head node) (mapcar #'tl-node->sexp (tl-node-children node)))
    (tl-node-display node)))

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

(defun tl-graph--check-progress (node rule new)
  "Signal `termlisp-eval-error' when rewriting NODE to NEW changes nothing.
A rule that matches and then reproduces what it matched would loop forever,
so non-progress is a defect in the rule rather than a property of the term.
A term no rule applies to simply stays where it is: only a rule that has
been committed to and then produces nothing is a bug."
  (when (and (eq (tl-node-head node) (tl-node-head new))
             (eq (tl-node-application node) (tl-node-application new))
             (equal (tl-node-children node) (tl-node-children new)))
    (signal 'termlisp-eval-error
            (list (format "Non-progressing rewrite: %S" (tl-grule-name rule))))))

(defun tl-graph-reduce (node rule)
  "Return RULE's reduct for NODE, or nil when the rule does not apply.
NODE and everything sharing it are left alone, and the caller decides
where the reduct goes.  Reduction over a *type* has to be pure, because
the same node is reachable from every type that mentions it -- rewriting
it in place would edit a signature as a side effect of comparing two
unrelated types.

Only the hand-written PATTERN/TEMPLATE path checks that a rule made
progress.  A rule built from a function's clauses does not: reproducing
what it matched is what a definition that calls itself does, and the answer
to that is the fuel in the host's own budget rather than an error class that
belongs to evaluating source."
  (if (tl-grule-clauses rule)
      (tl-graph-crule-reduce node rule)
    (let ((bindings (tl-graph-match (tl-grule-pattern rule) node nil)))
      (when (and bindings
                 (or (null (tl-grule-guard rule))
                     (funcall (tl-grule-guard rule) bindings)))
        (let ((new (tl-graph-instantiate (tl-grule-template rule) bindings)))
          (tl-graph--check-progress node rule new)
          new)))))

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

(defun tl-graph--rebuild (node children)
  "Return a copy of NODE carrying CHILDREN, leaving NODE itself untouched.
Copying rather than mutating is what lets `tl-graph--step' rewrite a term
that is shared: VAR/BIND/RIGID/LEVEL and KIND describe the term and must
survive the copy, while HEAD, APPLICATION and CHILDREN are the parts a rule
is allowed to replace."
  (let ((new (copy-tl-node node)))
    (setf (tl-node-children new) children)
    new))

(defun tl-graph--step (graph dispatch)
  "Apply one highest-priority leftmost-outermost rewrite.  Return t if any.
DISPATCH is a `(GENERIC . TABLE)' index from `tl-graph--rule-dispatch'; only
the rules indexed under a node's head (plus the generic ones) are tried.
The graph is walked in pre-order with early exit, so no full node list is
built and the scan stops at the first applicable rule.

Rewriting is copy-on-write: `tl-graph-reduce' never modifies the node it is
handed, and only the path back to the root is rebuilt.  A type node is
shared by every type that mentions it, so mutating one in place would
rewrite a signature while comparing two other types."
  (let ((generic (car dispatch))
        (table (cdr dispatch))
        (seen (make-hash-table :test #'eq)))
    (cl-labels ((walk (node)
                  (unless (gethash node seen)
                    (puthash node t seen)
                    (catch 'step
                      (dolist (rule (or (gethash (tl-node-head node) table)
                                        generic))
                        (let ((new (tl-graph-reduce node rule)))
                          (when new (throw 'step new))))
                      (unless (memq (tl-node-head node) tl-graph-opaque-heads)
                        (let ((children (tl-node-children node))
                              (out nil)
                              (moved nil))
                          (dolist (child children)
                            (let ((re (walk child)))
                              (if re
                                  (progn (push re out) (setq moved t))
                                (push child out))))
                          (when moved
                            (throw 'step
                                   (tl-graph--rebuild node (nreverse out))))))
                      nil))))
      (let ((new (walk (tl-graph-root graph))))
        (when new
          (setf (tl-graph-root graph) new)
          t)))))

(defun tl-graph-rewrite (graph rules &optional fuel fuel-signal)
  "Strictly reduce GRAPH to normal form using RULES, phase by phase.
Signals FUEL-SIGNAL (default `termlisp-eval-error') when FUEL (default
10000) is exhausted.  A host rewriting *source* reports an evaluation
error; a host normalising a *type* passes its own class instead, because a
type-level function that will not stop is a type error and has no business
being reported as one about evaluation."
  (let ((remaining (or fuel 10000))
        (condition (or fuel-signal 'termlisp-eval-error)))
    (dolist (phase tl-graph-phases graph)
      (let ((dispatch (tl-graph--rule-dispatch (tl-graph--rules-for phase rules))))
        (unless (and (null (car dispatch))
                     (zerop (hash-table-count (cdr dispatch))))
          (let ((progress t))
            (while progress
              (when (<= remaining 0)
                (signal condition '("TGR fuel exhausted")))
              (setq remaining (1- remaining))
              (setq progress (tl-graph--step graph dispatch)))))))))

(defun tl-graph-rewrite-sexp (sexp rules &optional fuel fuel-signal)
  "Build a graph from SEXP, strictly reduce it with RULES, and render it back.
FUEL and FUEL-SIGNAL are `tl-graph-rewrite''s: how many steps may be taken,
and the error class to report when they run out."
  (tl-node->sexp (tl-graph-root
                  (tl-graph-rewrite (tl-graph-build sexp) rules
                                    fuel fuel-signal))))

(provide 'termlisp-graph)
;;; termlisp-graph.el ends here
