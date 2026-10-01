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

(cl-defstruct (tl-node (:constructor tl-make-node (head &optional children)))
  "A term graph node.
HEAD is a symbol/atom operator (or a literal value for leaves).
CHILDREN is a list of child `tl-node's (shared).
STATE is a control marker (:idle, :active, :done).
MEMO is the node's rewritten replacement, or nil."
  head children (state :idle) memo)

(cl-defstruct (tl-graph (:constructor tl-make-graph (root table)))
  "A term graph: ROOT node plus a sharing TABLE (sexp-key -> node)."
  root table)

(defun tl-graph-build (sexp)
  "Build a term graph from SEXP, sharing structurally identical subterms."
  (let ((table (make-hash-table :test #'equal)))
    (cl-labels ((build (x)
                  (or (gethash x table)
                      (let ((node (if (consp x)
                                      (tl-make-node (car x) (mapcar #'build (cdr x)))
                                    (tl-make-node x nil))))
                        (puthash x node table)
                        node))))
      (tl-make-graph (build sexp) table))))

(defun tl-node->sexp (node)
  "Render NODE (and its children) back to an s-expression."
  (if (tl-node-children node)
      (cons (tl-node-head node) (mapcar #'tl-node->sexp (tl-node-children node)))
    (tl-node-head node)))

(cl-defstruct (tl-grule (:constructor tl-make-grule (name phase priority pattern template &optional guard)))
  "A term-graph rewrite rule.
NAME identifies the rule; PHASE and PRIORITY order its application.
PATTERN is matched against a node, TEMPLATE instantiated to rewrite it.
GUARD, when non-nil, is called with the bindings and must return non-nil."
  name phase priority pattern template guard)

(defconst tl-graph--match-ok (list (cons 'tl-graph-match-ok t))
  "Sentinel binding alist returned for a match with no variables.
Distinguishes a successful match with an empty binding set from failure.
A proper alist so guards may safely iterate its entries.")

(defun tl-graph--pvar-p (x)
  "Return non-nil if X is a pattern variable (a symbol named \"$...\")."
  (and (symbolp x)
       (> (length (symbol-name x)) 0)
       (eq (aref (symbol-name x) 0) ?$)))

(defun tl-graph-match (pattern node bindings)
  "Match PATTERN against NODE, extending BINDINGS.  Return bindings or nil."
  (cond
   ((tl-graph--pvar-p pattern)
    (let ((cell (assq pattern bindings)))
      (if cell (if (eq (cdr cell) node) bindings nil)
        (cons (cons pattern node) bindings))))
   ((consp pattern)
    (when (eq (tl-node-head node) (car pattern))
      (tl-graph-match-seq (cdr pattern) (tl-node-children node) bindings)))
   (t
    (when (and (eq (tl-node-head node) pattern)
               (null (tl-node-children node)))
      (or bindings tl-graph--match-ok)))))

(defun tl-graph-match-seq (patterns nodes bindings)
  "Match PATTERNS against NODES in order, extending BINDINGS."
  (let ((ok t))
    (while (and patterns ok)
      (if (null nodes)
          (setq ok nil)
        (setq bindings (tl-graph-match (car patterns) (car nodes) bindings))
        (unless bindings (setq ok nil))
        (setq patterns (cdr patterns) nodes (cdr nodes))))
    (when (and ok (null patterns) (null nodes))
      (or bindings tl-graph--match-ok))))

(defun tl-graph-instantiate (template bindings)
  "Instantiate TEMPLATE into a node, reusing nodes bound in BINDINGS."
  (cond
   ((tl-graph--pvar-p template)
    (let ((cell (assq template bindings)))
      (if cell
          (cdr cell)
        (signal 'termlisp-eval-error
                (list (format "Unbound template variable: %S" template))))))
   ((consp template)
    (tl-make-node (car template)
                  (mapcar (lambda (sub) (tl-graph-instantiate sub bindings))
                          (cdr template))))
   (t (tl-make-node template nil))))

(defun tl-graph-apply (node rule)
  "If RULE matches NODE, rewrite NODE in place.  Return t, or nil if no match.
Signals `termlisp-eval-error' if the rewrite makes no progress."
  (let ((bindings (tl-graph-match (tl-grule-pattern rule) node nil)))
    (when (and bindings
               (or (null (tl-grule-guard rule))
                   (funcall (tl-grule-guard rule) bindings)))
      (let ((new (tl-graph-instantiate (tl-grule-template rule) bindings)))
        (if (and (eq (tl-node-head node) (tl-node-head new))
                 (equal (tl-node-children node) (tl-node-children new)))
            (signal 'termlisp-eval-error
                    (list (format "Non-progressing rewrite: %S" (tl-grule-name rule))))
          (setf (tl-node-head node) (tl-node-head new))
          (setf (tl-node-children node) (tl-node-children new))
          t)))))

(defconst tl-graph-phases
  '(:surface :normalize :desugar :context :control :load :action :backend)
  "Reduction phases, applied in order.  Rules only move forward.")

(defun tl-graph--preorder (node &optional seen)
  "Return NODE and its descendants in pre-order, without revisiting nodes."
  (let ((seen (or seen (make-hash-table :test #'eq))))
    (unless (gethash node seen)
      (puthash node t seen)
      (cons node (mapcan (lambda (c) (tl-graph--preorder c seen))
                         (tl-node-children node))))))

(defun tl-graph--rules-for (phase rules)
  "Rules of PHASE, sorted by ascending priority."
  (sort (cl-remove-if-not (lambda (r) (eq (tl-grule-phase r) phase)) rules)
        (lambda (a b) (< (tl-grule-priority a) (tl-grule-priority b)))))

(defun tl-graph--step (graph rules)
  "Apply one highest-priority leftmost-outermost rewrite.  Return t if any."
  (catch 'applied
    (dolist (node (tl-graph--preorder (tl-graph-root graph)))
      (dolist (rule rules)
        (when (tl-graph-apply node rule)
          (throw 'applied t))))
    nil))

(defun tl-graph-rewrite (graph rules &optional fuel)
  "Strictly reduce GRAPH to normal form using RULES, phase by phase.
Signals `termlisp-eval-error' when FUEL (default 10000) is exhausted."
  (let ((remaining (or fuel 10000)))
    (dolist (phase tl-graph-phases graph)
      (let ((prules (tl-graph--rules-for phase rules))
            (progress t))
        (while progress
          (when (<= remaining 0)
            (signal 'termlisp-eval-error '("TGR fuel exhausted")))
          (setq remaining (1- remaining))
          (setq progress (tl-graph--step graph prules)))))))

(defun tl-graph-rewrite-sexp (sexp rules &optional fuel)
  "Build a graph from SEXP, strictly reduce it with RULES, and render it back."
  (tl-node->sexp (tl-graph-root (tl-graph-rewrite (tl-graph-build sexp) rules fuel))))

(defun tl-graph-normal-form-p (graph rules)
  "Return non-nil if no rule applies anywhere in GRAPH."
  (catch 'reducible
    (dolist (node (tl-graph--preorder (tl-graph-root graph)))
      (dolist (rule rules)
        (let ((bindings (tl-graph-match (tl-grule-pattern rule) node nil)))
          (when (and bindings
                     (or (null (tl-grule-guard rule))
                         (funcall (tl-grule-guard rule) bindings)))
            (throw 'reducible nil)))))
    t))

(provide 'termlisp-graph)
;;; termlisp-graph.el ends here
