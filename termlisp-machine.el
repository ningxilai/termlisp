;;; termlisp-machine.el --- Runtime objects and value helpers -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Runtime values are: atoms (symbol/number/string), constructor values
;; (a symbol for nullary, or a list `(Con field...)'), closures, function
;; objects, and thunks.  Constructor fields are stored as thunks (lazy).

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(defvar termlisp--current-env nil
  "Dynamically bound evaluation context during `tl-run'.
Defined in termlisp-eval.el.")

(cl-defstruct (tl-thunk (:constructor tl-make-thunk (expr env)))
  expr env (forced-p nil) (value nil) (busy-p nil))

(cl-defstruct (tl-closure (:constructor tl-make-closure (params body env)))
  params body env)

(cl-defstruct (tl-function (:constructor tl-make-function (clauses)))
  clauses)

(defun tl-value-equal (a b force)
  "Compare runtime values A and B structurally, forcing thunks with FORCE."
  (let ((a (funcall force a))
        (b (funcall force b)))
    (cond
     ((and (consp a) (consp b))
      (and (tl-value-equal (car a) (car b) force)
           (tl-value-equal (cdr a) (cdr b) force)))
     ((or (consp a) (consp b)) nil)
     (t (equal a b)))))

(defun tl-true-value-p (v)
  "Return non-nil if V is the boolean constructor `True'."
  (eq v 'True))

(defun tl-lookup (name env)
  "Look up NAME in local ENV, then in the current environment's globals."
  (or (assq name env)
      (assq name (tl-env-globals termlisp--current-env))))

(provide 'termlisp-machine)
;;; termlisp-machine.el ends here
