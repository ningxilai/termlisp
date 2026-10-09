;;; termlisp-free-vars.el --- Free type variables of a type graph -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; The set of unbound type variables reachable from a type node.  A
;; higher-kinded *head* variable such as `f' in `(f a)' counts too.  This
;; drives generalization, context reduction and instance resolution, so it
;; lives in its own module rather than in the graph <-> surface bridges.

;;; Code:

(require 'cl-lib)
(require 'termlisp-graph-unify)

(defun tl-free-tvars (type)
  "Return the list of unbound type variables occurring in TYPE.
The traversal is cycle-safe (equirecursive types) and follows the head of
each application, so a variable head `(f a)' contributes `f'."
  (let ((seen (make-hash-table :test #'eq))
        (stack (list type))
        (vars nil))
    (while stack
      (let ((n (tl-gnode-deref (pop stack))))
        (unless (gethash n seen)
          (puthash n t seen)
          (cond
           ((tl-node-var-p n) (push n vars))
           ((tl-node-application n)
            (when (tl-node-p (tl-node-head n))
              (let ((h (tl-gnode-deref (tl-node-head n))))
                (when (tl-node-var-p h) (push h vars))))
            (dolist (c (tl-node-children n)) (push c stack)))))))
    vars))

(provide 'termlisp-free-vars)
;;; termlisp-free-vars.el ends here
