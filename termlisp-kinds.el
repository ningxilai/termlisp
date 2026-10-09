;;; termlisp-kinds.el --- Kind (arity) checking -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A lightweight kind system: a type constructor has an arity (its number
;; of type parameters), and a kind error is an application of a known
;; constructor at the wrong arity.  Unknown heads are accepted, so the
;; checker is safe to run over the Aldor oracle's types (which mention
;; domain names we do not register).  Variadic constructors (`Record',
;; `Union') are exempt.

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

(defun tl-kind-check (env ty)
  "Check well-kindedness of the type node TY in ENV.
Signal `termlisp-type-error' when a known constructor is applied at the
wrong arity; unknown constructors are accepted."
  (let ((ty (tl-type-deref ty)))
    (cond
     ((tl-tvar-p ty) t)
     ((tl-tcon-p ty)
      (let ((name (tl-tcon-name ty))
            (args (tl-tcon-args ty)))
        (unless (memq name tl-variadic-kinds)
          (let ((arity (tl-kind-of env name)))
            (when (and arity (/= arity (length args)))
              (signal 'termlisp-type-error
                      (list (format "Kind error: %S applied to %d argument(s), expects %d"
                                    name (length args) arity))))))
        (cl-every (lambda (a) (tl-kind-check env a)) args)))
     (t t))))

(defun tl-kind-check-scheme (env scheme)
  "Check the type of SCHEME (a `tl-tscheme') for well-kindedness."
  (when (tl-tscheme-p scheme)
    (tl-kind-check env (tl-tscheme-type scheme))))

(provide 'termlisp-kinds)
;;; termlisp-kinds.el ends here
