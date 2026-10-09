;;; termlisp-kinds.el --- Kind inference -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A small kind system over the same term graph used for types.  A kind is
;; a node: `*` (the kind of proper types) is the leaf `tl-kind-star', a
;; function kind `karr k1 k2' is a compound, and a kind variable is an
;; ordinary unification variable node.  Hence kind unification reuses the
;; graph unifier (`tl-gnode-unify' with the occurs check on).
;;
;; A type constructor has a kind: `Int : *', `List : * -> *',
;; `-> : * -> * -> *', and a datatype's kind is inferred from its
;; constructor field types.  Kind inference also gives *type variables*
;; kinds: a variable used as a proper type has kind `*', and one applied to
;; N arguments acquires `k1 -> ... -> kN -> r'.  The kind is stored in the
;; type node's KIND slot, so it is available to unification and copied on
;; instantiation.
;;
;; Kind inference is lenient about unknown heads (they get a fresh kind
;; variable), so it is safe to run over the Aldor oracle's types.

;;; Code:

(require 'cl-lib)
(require 'termlisp-types)

(defconst tl-kind-star (tl-make-node '* nil nil)
  "The kind of proper types.")

(defconst tl-builtin-kinds
  '((Int . 0) (DoubleFloat . 0) (MachineInteger . 0) (SingleInteger . 0)
    (AldorInteger . 0) (Bool . 0) (Boolean . 0) (Character . 0)
    (String . 0) (Unit . 0)
    (-> . 2) (List . 1) (Array . 1) (PrimitiveArray . 1) (Vector . 1)
    (Generator . 1) (Ref . 1) (Store . 1))
  "Arity of the prelude/known type constructors, from which kinds derive.")

(defun tl-kstar () tl-kind-star)
(defun tl-karr (a b) (tl-make-node 'karr (list a b) t))
(defun tl-karr-p (k)
  (let ((k (tl-kind-deref k)))
    (and (tl-node-p k) (eq (tl-node-head k) 'karr))))

(defun tl-karity (n)
  "Return the kind of a constructor taking N type arguments."
  (if (<= n 0) tl-kind-star (tl-karr tl-kind-star (tl-karity (1- n)))))

(defun tl-kind-var () (tl-make-var-node 'kind))
(defun tl-kind-deref (k) (if (tl-node-p k) (tl-gnode-deref k) k))

(defun tl-kind-star-p (k)
  (eq (tl-kind-deref k) tl-kind-star))

(defun tl-kind-unify (a b)
  "Unify kinds A and B (occurs-checked).  Return non-nil on success."
  (and (tl-node-p a) (tl-node-p b) (tl-gnode-unify a b t)))

(defun tl-register-kind (env name arity)
  "Record that constructor NAME has kind arity ARITY in ENV."
  (puthash name (tl-karity arity) (tl-env-kind-env env)))

(defun tl-kind-of (env name)
  "Return the kind of type constructor NAME in ENV, or nil if unknown."
  (or (gethash name (tl-env-kind-env env))
      (let ((a (cdr (assq name tl-builtin-kinds))))
        (and a (tl-karity a)))))

(defun tl-register-datatype-kind (env name params)
  "Register NAME's kind from its parameter variables' inferred kinds.
PARAMS is the list of parameter type-variable nodes; a parameter whose kind
is unknown contributes a fresh kind variable."
  (let ((k tl-kind-star))
    (dolist (p (reverse params))
      (let ((pk (let ((raw (and (tl-node-p p) (tl-node-kind p))))
                  (if raw (tl-kind-deref raw) (tl-kind-var)))))
        (setq k (tl-karr pk k))))
    (puthash name k (tl-env-kind-env env))))

(defun tl-kind-infer (env ty)
  "Infer the kind of type TY in ENV, unifying as it goes.
Return a kind node.  Storing the kind in each variable's KIND slot makes
repeated inference consistent; unknown heads get a fresh kind variable."
  (let ((ty (tl-type-deref ty)))
    (cond
     ((tl-tvar-p ty)
      (or (tl-node-kind ty)
          (let ((k (tl-kind-var))) (setf (tl-node-kind ty) k) k)))
     ((tl-tcon-p ty)
      (let ((head (tl-type-deref (tl-tcon-name ty)))
            (args (tl-tcon-args ty)))
        (if (null args)
            (if (tl-node-var-p head)
                (or (tl-node-kind head)
                    (let ((k (tl-kind-var))) (setf (tl-node-kind head) k) k))
              (or (tl-kind-of env head)
                  (let ((k (tl-kind-var))) k)))
          (let* ((arg-ks (mapcar (lambda (a) (tl-kind-infer env a)) args))
                 (res (tl-kind-var))
                 (want (let ((k res))
                         (dolist (ak (reverse arg-ks)) (setq k (tl-karr ak k)))
                         k))
                 (hk (cond ((tl-node-var-p head)
                            (or (tl-node-kind head)
                                (let ((k (tl-kind-var)))
                                  (setf (tl-node-kind head) k) k)))
                           ((tl-kind-of env head))
                           (t (tl-kind-var)))))
            (unless (tl-kind-unify hk want)
              (signal 'termlisp-type-error
                      (list (format "Kind error: %S applied to %d argument(s)"
                                    (if (symbolp head) head "type variable")
                                    (length args)))))
            res))))
     (t tl-kind-star))))

(defun tl-kind-check (env ty)
  "Check that TY is a well-kinded proper type in ENV.  Return TY."
  (let ((k (tl-kind-infer env ty)))
    (unless (tl-kind-unify k tl-kind-star)
      (signal 'termlisp-type-error
              (list (format "Kind error: %S is not a proper type" ty)))))
  ty)

(defun tl-kind-check-scheme (env scheme)
  "Check the type of SCHEME (a `tl-tscheme') for well-kindedness."
  (when (tl-tscheme-p scheme)
    (tl-kind-check env (tl-tscheme-type scheme))))

(provide 'termlisp-kinds)
;;; termlisp-kinds.el ends here
