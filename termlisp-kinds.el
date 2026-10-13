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

(defun tl-karr (a b) (tl-make-node 'karr (list a b) t))
(defun tl-karr-p (k)
  (let ((k (tl-kind-deref k)))
    (and (tl-node-p k) (eq (tl-node-head k) 'karr))))

(defun tl-karity (n)
  "Return the kind of a constructor taking N type arguments."
  (if (<= n 0) tl-kind-star (tl-karr tl-kind-star (tl-karity (1- n)))))

(defun tl-kind-var () (tl-make-var-node 'kind))
(defun tl-kind-deref (k) (if (tl-node-p k) (tl-gnode-deref k) k))

(defun tl-kind-freshen (k)
  "Return K with every kind variable replaced by a fresh one.
A datatype's kind is a scheme: `Eq' ranges over every element type and
over every pair of values in it, and its free variables are what say
so.  Each application has to decide those for itself, so the registered
kind is copied rather than unified against.  Unifying in place would let
the first use to mention `Eq' -- its own declaration, even -- fix the
kinds for every use after it."
  (cond ((not (tl-node-p k)) k)
        ((tl-node-var-p k) (tl-kind-var))
        ((eq (tl-node-head k) 'karr)
         (let ((cs (tl-node-children k)))
           (tl-karr (tl-kind-freshen (car cs)) (tl-kind-freshen (cadr cs)))))
        (t k)))

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
PARAMS is the list of parameter type-variable nodes.

A parameter a constructor field has pinned keeps that kind: a field's
type must be a proper type, so `a' in `(Mk a)' is `*'.  A parameter an
index has pinned keeps that too: `n' in `(Vec a (Succ n))' is the
universe `Nat', because `Succ' says so.

A parameter nothing has pinned is left free rather than defaulted to
`*'.  Such a parameter appears only in index position -- `x' and `y' in
`Refl : (Eq a x x)' are the reason this matters -- and an index ranges
over the values of some type, which at the kind level means a universe
leaf such as `Nat', not `*'.  Defaulting it would reject `(Eq Nat Zero
Zero)' for being applied to a value where a type was expected, and
there is nothing in the declaration to say which it should be.  Leaving
it free lets each application decide, and an application that decides
inconsistently is a kind error there rather than a silent success."
  (let ((k tl-kind-star))
    (dolist (p (reverse params))
      (let* ((raw (and (tl-node-p p) (tl-node-kind p)))
             (deref (and raw (tl-kind-deref raw)))
             (pk (if (or (null deref) (tl-node-var-p deref))
                     (tl-kind-var)
                   deref)))
        (setq k (tl-karr pk k))))
    (puthash name k (tl-env-kind-env env))))

(defun tl-kind-universe (name)
  "Return the kind that lifts datatype NAME to the type level.
This is a leaf kind named NAME, and it is deliberately distinct from
`tl-kind-star': `Nat' written as a type has kind `*', while `Nat'
written as a universe is the kind of `Zero'.  One name, two levels --
exactly the double duty Haskell's DataKinds gives it."
  (tl-make-node name nil nil))

(defun tl--lifted-field-kind (env datatype field)
  "Kind FIELD contributes when a constructor of DATATYPE is lifted in ENV.
A field written as DATATYPE itself contributes the universe rather than
`*', which is what gives Peano-style constructors `Succ : Nat -> Nat'.
Any other field keeps the kind it already has as a proper type."
  (let ((f (tl-type-deref field)))
    (if (and (tl-tcon-p f)
             (null (tl-tcon-args f))
             (eq (tl-tcon-name f) datatype))
        (tl-kind-universe datatype)
      (condition-case nil (tl-kind-infer env field) (error (tl-kind-var))))))

(defun tl-register-lifted-constructors (env name ctors)
  "Register in ENV the type-level kinds of NAME's constructors CTORS.
CTORS is an alist of (CONSTRUCTOR . FIELD-TYPES) over already-parsed field
types.  Each constructor is lifted to

    field1 -> ... -> fieldN -> Universe

so that declaring `(datatype Nat (Zero) (Succ Nat))' puts `Zero : Nat'
and `Succ : Nat -> Nat' in the kind environment.  That is what makes an
index expression such as `(Vec a (Succ n))' well-kinded, and -- because
kinds unify -- what makes `(Vec a String)' a kind error rather than a
silent success."
  (let ((universe (tl-kind-universe name)))
    (dolist (ca ctors)
      (let ((k universe))
        (dolist (f (reverse (cdr ca)))
          (setq k (tl-karr (tl--lifted-field-kind env name f) k)))
        (puthash (car ca) k (tl-env-kind-env env))))))

(defun tl-kind-infer (env ty)
  "Infer the kind of type TY in ENV, unifying as it goes.
Return a kind node.  Storing the kind in each variable's KIND slot makes
repeated inference consistent; unknown heads get a fresh kind variable."
  (let ((ty (tl-type-deref ty)))
    (cond
     ((tl-tvar-p ty)
      (or (tl-node-kind ty)
          (let ((k (tl-kind-var))) (setf (tl-node-kind ty) k) k)))
     ;; `Pi' is a dependent function type, not an ordinary constructor
     ;; application: its three children are a binder and two types, so
     ;; the arity rule below would hand it a three-argument kind.  Both
     ;; domain and codomain are proper types.  The binder's own kind is
     ;; whatever its uses demand -- `Vec a n' is what pins `n' to `Nat'
     ;; -- so infer and store it, but do not check it.
     ((and (tl-tcon-p ty) (eq (tl-node-head ty) 'Pi)
           (= (length (tl-tcon-args ty)) 3))
      (let ((a (tl-tcon-args ty)))
        (tl-kind-infer env (nth 0 a))
        (tl-kind-check env (nth 1 a))
        (tl-kind-check env (nth 2 a))
        tl-kind-star))
     ;; A type-level lambda has the kind of the function it denotes.
     ((and (tl-tcon-p ty) (eq (tl-node-head ty) 'lambda)
           (= (length (tl-tcon-args ty)) 2))
      (let ((a (tl-tcon-args ty)))
        (tl-kind-check env (nth 1 a))
        (tl-karr (tl-kind-infer env (nth 0 a)) tl-kind-star)))
     ((tl-tcon-p ty)
      (let ((head (tl-type-deref (tl-tcon-name ty)))
            (args (tl-tcon-args ty)))
        (if (null args)
            (if (tl-node-var-p head)
                (or (tl-node-kind head)
                    (let ((k (tl-kind-var))) (setf (tl-node-kind head) k) k))
              (or (tl-kind-freshen (tl-kind-of env head))
                  (tl-kind-var)))
          (let* ((arg-ks (mapcar (lambda (a) (tl-kind-infer env a)) args))
                 (res (tl-kind-var))
                 (want (let ((k res))
                         (dolist (ak (reverse arg-ks)) (setq k (tl-karr ak k)))
                         k))
                 (hk (cond ((tl-node-var-p head)
                            (or (tl-node-kind head)
                                (let ((k (tl-kind-var)))
                                  (setf (tl-node-kind head) k) k)))
                           ;; A registered kind is a scheme: copy it, so
                           ;; this application decides its variables
                           ;; without deciding them for the next one.
                           ((tl-kind-freshen (tl-kind-of env head)))
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
