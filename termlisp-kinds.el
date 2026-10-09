;;; termlisp-kinds.el --- Kind (arity) checking -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A lightweight kind system: a type constructor has a *kind arity*, the
;; number of type arguments it takes (0 for a proper type such as `Int',
;; 1 for `List', 2 for `->' and `Pair').  A kind error is an application
;; of a known constructor at the wrong arity, or a type variable used at
;; two different arities (e.g. both `f a' and `f a b').
;;
;; Type *variables* are given kinds too: a variable appearing in head
;; position with N arguments is inferred to have kind arity N, recorded in
;; the node's KIND slot, and shared head variables must agree.  This makes
;; higher-kinded variables (`f : * -> *') first class.
;;
;; Unknown heads are accepted, so the checker is safe to run over the
;; Aldor oracle's types (which mention domain names we do not register).
;; Variadic constructors (`Record', `Union') are exempt.

;;; Code:

(require 'cl-lib)
(require 'termlisp-types)

(defconst tl-builtin-kinds
  '((Int . 0) (DoubleFloat . 0) (MachineInteger . 0) (SingleInteger . 0)
    (AldorInteger . 0) (Bool . 0) (Boolean . 0) (Character . 0)
    (String . 0) (Unit . 0)
    (-> . 2) (List . 1) (Array . 1) (PrimitiveArray . 1) (Vector . 1)
    (Generator . 1) (Ref . 1) (Store . 1))
  "Arity of the prelude/known type constructors.")

(defconst tl-variadic-kinds '(Record Union Comma)
  "Constructors whose arity is not fixed.")

(defun tl-register-kind (env name arity)
  "Record that constructor NAME has kind arity ARITY in ENV."
  (puthash name arity (tl-env-kind-env env)))

(defun tl-kind-of (env name)
  "Return the arity of type constructor NAME in ENV, or nil if unknown."
  (or (gethash name (tl-env-kind-env env))
      (cdr (assq name tl-builtin-kinds))))

(defun tl-kind-check-bare-var (var kinds)
  "VAR is used as a proper type; error when its kind arity is non-zero."
  (let ((k (or (gethash var kinds) (tl-node-kind var))))
    (when (and k (/= k 0))
      (signal 'termlisp-type-error
              (list (format "Kind error: %S has kind arity %d but is used as a type"
                            var k))))
    0))

(defun tl-kind-head-arity (env head n kinds)
  "Kind arity of HEAD applied to N arguments, or nil if HEAD is unknown.
For a variable HEAD, infer or check its arity against N."
  (if (tl-node-var-p head)
      (let ((prev (or (gethash head kinds) (tl-node-kind head))))
        (cond ((null prev)
               (puthash head n kinds)
               (setf (tl-node-kind head) n)
               n)
              ((/= prev n)
               (signal 'termlisp-type-error
                       (list (format "Kind error: %S used at arities %d and %d"
                                     head prev n))))
              (t prev)))
    (tl-kind-of env head)))

(defun tl-kind-walk-application (env head args n kinds)
  "Check application of HEAD to ARGS (N of them), each a proper type."
  (let ((hkind (tl-kind-head-arity env head n kinds)))
    (dolist (a args)
      (let ((ak (tl-kind-walk env a kinds)))
        (when (and ak (/= ak 0))
          (signal 'termlisp-type-error
                  (list (format "Kind error: %S is applied to non-type %S"
                                (if (symbolp head) head "type variable") a))))))
    (cond ((null hkind) nil)
          ((memq head tl-variadic-kinds) 0)
          ((>= hkind n) (- hkind n))
          (t (signal 'termlisp-type-error
                     (list (format "Kind error: %S applied to %d argument(s), expects %d"
                                   (if (symbolp head) head "type variable")
                                   n hkind)))))))

(defun tl-kind-walk (env ty kinds)
  "Check well-kindedness of TY; return its own kind arity (or nil).
KINDS is a hash of variable node -> inferred arity, threaded through the
walk and also written to each variable's KIND slot.  Signal
`termlisp-type-error' on a kind error."
  (let ((ty (tl-type-deref ty)))
    (cond
     ((tl-tvar-p ty) (tl-kind-check-bare-var ty kinds))
     ((tl-tcon-p ty)
      (let* ((head (tl-type-deref (tl-tcon-name ty)))
             (args (tl-tcon-args ty))
             (n (length args)))
        (if (null args)
            (if (tl-node-var-p head)
                (tl-kind-check-bare-var head kinds)
              (tl-kind-of env head))
          (tl-kind-walk-application env head args n kinds))))
     (t 0))))

(defun tl-kind-check (env ty)
  "Check well-kindedness of the type node TY in ENV.
Signal `termlisp-type-error' when a known constructor is applied at the
wrong arity, a type variable is used inconsistently, or TY is not a
proper type (has residual kind arity).  Unknown constructors are
accepted.  Return TY."
  (let ((k (tl-kind-walk env ty (make-hash-table :test #'eq))))
    (when (and k (not (zerop k))
               (not (memq (tl-tcon-name (tl-type-deref ty)) tl-variadic-kinds)))
      (signal 'termlisp-type-error
              (list (format "Kind error: %S is not a proper type (residual arity %d)"
                            ty k)))))
  ty)

(defun tl-kind-check-scheme (env scheme)
  "Check the type of SCHEME (a `tl-tscheme') for well-kindedness."
  (when (tl-tscheme-p scheme)
    (tl-kind-check env (tl-tscheme-type scheme))))

(provide 'termlisp-kinds)
;;; termlisp-kinds.el ends here
