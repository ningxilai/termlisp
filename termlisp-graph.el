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

(provide 'termlisp-graph)
;;; termlisp-graph.el ends here
