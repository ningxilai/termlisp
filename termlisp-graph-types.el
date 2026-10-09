;;; termlisp-graph-types.el --- HM types on the term graph -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A graph-backed Hindley-Milner type representation, replacing alist
;; substitutions with in-place unification (see `termlisp-graph-unify').
;; A type is a `tl-node': a type constructor application `(C a b)' is a
;; compound node, a bare constructor `Int' is a leaf node, and a type
;; variable is a variable node.  `tl-tcon'/'tl-lvar' remain the surface
;; syntax and are converted in and out at the boundary.
;;
;; Following Coalton, the occurs check is off by default, so recursive
;; (equirecursive) types are representable.  Generalization/instantiation
;; copy the graph, replacing quantified variable nodes with fresh ones.

;;; Code:

(require 'cl-lib)
(require 'termlisp-types)
(require 'termlisp-graph-unify)

(defvar tl-gtype--default-occurs-check nil
  "Whether type unification rejects cyclic bindings by default.")

(defun tl-gtype-from-tcon (ty &optional map)
  "Convert surface type TY to a type node, sharing variables via MAP.
TY is a `tl-tcon' or `tl-lvar'; MAP maps a `tl-lvar' to its node."
  (let ((map (or map (make-hash-table :test #'eq))))
    (cl-labels ((go (ty)
                  (cond
                   ((tl-lvar-p ty)
                    (or (gethash ty map)
                        (puthash ty (tl-make-var-node (tl-lvar-id ty)) map)))
                   ((tl-tcon-p ty)
                    (let ((args (tl-tcon-args ty)))
                      (if args
                          (tl-make-node (tl-tcon-name ty) (mapcar #'go args) t)
                        (tl-make-node (tl-tcon-name ty)))))
                   (t (tl-make-var-node)))))
      (go ty))))

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

(defun tl-gtype-free-vars (node)
  "Return the unbound variable nodes reachable from NODE."
  (let ((seen (make-hash-table :test #'eq))
        (stack (list node))
        (vars nil))
    (while stack
      (let ((n (tl-gnode-deref (pop stack))))
        (unless (gethash n seen)
          (puthash n t seen)
          (cond
           ((tl-node-var-p n) (push n vars))
           ((tl-node-application n)
            ;; A higher-kinded head variable `(f a)' is a free variable too.
            (when (tl-node-p (tl-node-head n))
              (let ((h (tl-gnode-deref (tl-node-head n))))
                (when (tl-node-var-p h) (push h vars))))
            (dolist (c (tl-node-children n)) (push c stack)))))))
    vars))

(defun tl-gtype-unify (a b &optional occurs-check)
  "Unify type nodes A and B, in place.  Return t or nil (rolled back)."
  (tl-gnode-unify a b (if (null occurs-check)
                          tl-gtype--default-occurs-check
                        occurs-check)))

(defun tl-gtype-quantify (node)
  "Return (QUANTIFIED . NODE): the free variable nodes of NODE."
  (cons (tl-gtype-free-vars node) node))

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
