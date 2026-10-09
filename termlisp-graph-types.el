;;; termlisp-graph-types.el --- HM types on the term graph -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A graph-backed Hindley-Milner type representation, replacing alist
;; substitutions with in-place unification (see `termlisp-graph-unify').
;; A type is a `tl-node': a type constructor application `(C a b)' is a
;; compound node, a bare constructor `Int' is a leaf node, and a type
;; variable is a variable node.  `tl-tcon' remains the surface syntax and
;; is converted in and out at the boundary.
;;
;; Following Coalton, the occurs check is off by default, so recursive
;; (equirecursive) types are representable.  Generalization/instantiation
;; copy the graph, replacing quantified variable nodes with fresh ones.

;;; Code:

(require 'cl-lib)
(require 'termlisp-types)
(require 'termlisp-graph-unify)
(require 'termlisp-free-vars)

(defvar tl-gtype--default-occurs-check nil
  "Whether type unification rejects cyclic bindings by default.")

(defun tl-gtype-from-tcon (ty)
  "Convert surface type TY (a `tl-tcon') to a type node."
  (cond
   ((tl-tcon-p ty)
    (let ((args (tl-tcon-args ty)))
      (if args
          (tl-make-node (tl-tcon-name ty) (mapcar #'tl-gtype-from-tcon args) t)
        (tl-make-node (tl-tcon-name ty)))))
   (t (tl-make-var-node))))

(defun tl-gtype-to-tcon (node &optional map)
  "Render type NODE back to a `tl-tcon', sharing variables via MAP."
  (let ((map (or map (make-hash-table :test #'eq))))
    (cl-labels ((go (n)
                  (let ((n (tl-gnode-deref n)))
                    (cond
                     ((tl-node-var-p n)
                      (or (gethash n map)
                          (puthash n (tl-fresh-tvar) map)))
                     ((tl-node-application n)
                      (tl-tcon (tl-node-head n)
                               (mapcar #'go (tl-node-children n))))
                     (t (tl-tcon (tl-node-head n) nil))))))
      (go node))))

(defun tl-gtype-unify (a b &optional occurs-check)
  "Unify type nodes A and B, in place.  Return t or nil (rolled back)."
  (tl-gnode-unify a b (if (null occurs-check)
                          tl-gtype--default-occurs-check
                        occurs-check)))

(defun tl-gtype-quantify (node)
  "Return (QUANTIFIED . NODE): the free variable nodes of NODE."
  (cons (tl-free-tvars node) node))

(defun tl-gtype-instantiate (quantified node)
  "Copy NODE, replacing each variable node in QUANTIFIED with a fresh one.
Non-quantified variables and shared compounds are reused."
  (let ((map (make-hash-table :test #'eq)))
    (dolist (v quantified)
      (puthash v (tl-make-var-node (tl-node-head v)) map))
    (cl-labels ((copy (n)
                  (let ((n (tl-gnode-deref n)))
                    (cond
                     ((tl-node-var-p n)
                      (or (gethash n map) n))
                     ((tl-node-application n)
                      (tl-make-node (tl-node-head n)
                                    (mapcar #'copy (tl-node-children n)) t))
                     (t n)))))
      (copy node))))

(provide 'termlisp-graph-types)
;;; termlisp-graph-types.el ends here
