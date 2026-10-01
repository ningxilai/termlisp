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

(cl-defstruct (tl-grule (:constructor tl-make-grule (name phase priority pattern template &optional guard)))
  "A term-graph rewrite rule.
NAME identifies the rule; PHASE and PRIORITY order its application.
PATTERN is matched against a node, TEMPLATE instantiated to rewrite it.
GUARD, when non-nil, is called with the bindings and must return non-nil."
  name phase priority pattern template guard)

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
      bindings))))

(defun tl-graph-match-seq (patterns nodes bindings)
  "Match PATTERNS against NODES in order, extending BINDINGS."
  (let ((ok t))
    (while (and patterns ok)
      (if (null nodes)
          (setq ok nil)
        (setq bindings (tl-graph-match (car patterns) (car nodes) bindings))
        (unless bindings (setq ok nil))
        (setq patterns (cdr patterns) nodes (cdr nodes))))
    (when (and ok (null patterns) (null nodes)) bindings)))

(defun tl-graph-instantiate (template bindings)
  "Instantiate TEMPLATE into a node, reusing nodes bound in BINDINGS."
  (cond
   ((tl-graph--pvar-p template)
    (cdr (assq template bindings)))
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

(provide 'termlisp-graph)
;;; termlisp-graph.el ends here
