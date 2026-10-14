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
;;
;; Two kinds go beyond that.  `kuniv T', written `univ(T)', is the kind of
;; the *values* of T -- `Zero' is `Nat'-kinded because it is a `Nat', and
;; the universe leaf is what says which datatype a value came from.  `kpi
;; x k1 k2', written `Π(x : k1).  k2', binds a parameter so that k2 may
;; mention it: `(x : (univ a))' then states that x comes out of a, which
;; is the dependency `Eq' needs and three independent kind variables
;; cannot say.  Kinds are therefore dependent, and a datatype parameter's
;; kind is read in the declaration's own scope so the binder and the
;; constructor schemes refer to one variable rather than two that merely
;; resemble each other.
;;
;; A constructor's fields are values rather than types, so a lifted
;; constructor's argument kind is `univ' of the field's type: `Succ : Nat
;; -> Nat' as before, `VCons : univ(a) -> univ((Vec a n)) -> Vec' now.
;; That is where an index in `Eq''s kind finally meets a constructor --
;; the same `xs' is `Vec Nat n'-kinded in one and the tail of `VCons' in
;; the other -- and the two spellings of one fact either reconcile or
;; raise the kind error that says they do not.

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
    (and (tl-node-p k) (not (tl-node-var k)) (eq (tl-node-head k) 'karr))))

(defun tl-kpi (binder domain body)
  "Build the dependent kind `Π(BINDER : DOMAIN).  BODY'.
A `karr' whose codomain may not mention its domain says nothing about
which *values* the domain admits; a `kpi' can, because BINDER stands for
the type the argument turned out to be.  That is the whole difference:
`(Eq a x y)' needs `x' to be taken from `a', and an arrow from `*' to
`*' would let `x' come from anywhere at all.  BINDER is an ordinary type
variable node -- it is substituted, not solved, so nothing may unify it
away; see `tl-kind-infer'."
  (tl-make-node 'kpi (list binder domain body) t))

(defun tl-kpi-p (k)
  (let ((k (tl-kind-deref k)))
    (and (tl-node-p k) (not (tl-node-var k)) (eq (tl-node-head k) 'kpi))))

(defun tl-kpi-binder (k) (nth 0 (tl-node-children (tl-kind-deref k))))
(defun tl-kpi-domain (k) (nth 1 (tl-node-children (tl-kind-deref k))))
(defun tl-kpi-body (k)   (nth 2 (tl-node-children (tl-kind-deref k))))

(defun tl-kuniv (type)
  "Build the kind of the values of TYPE: `univ(TYPE)'.
This is the level shift the universe leaves already imply but could not
express: `Zero' has kind `Nat' because a constructor said so, but
nothing could say *every* value of `a' has kind `a''s universe, because
that sentence mentions `a' and a kind written before `a' is known
cannot.  `kpi' binds it and `tl-kuniv' uses it, and together they are
the dependent kind: `Π(a : *).  univ(a) -> univ(a) -> *'."
  (tl-make-node 'univ (list type) t))

(defun tl-kuniv-p (k)
  (let ((k (tl-kind-deref k)))
    (and (tl-node-p k) (not (tl-node-var k)) (eq (tl-node-head k) 'univ))))

(defun tl-kuniv-type (k) (car (tl-node-children (tl-kind-deref k))))

(defun tl-kind-universe-p (k)
  "Non-nil when K is a universe leaf such as `Nat'.
A universe leaf is a leaf the way `*' is -- no children, not written as
an application -- but it is named after a datatype rather than after
properness, and that name is what makes it the kind of one datatype's
values and of no others."
  (and (tl-node-p k)
       (not (tl-node-var k))
       (null (tl-node-application k))
       (null (tl-node-children k))
       (not (eq (tl-node-head k) '*))))

(defun tl-kind->sexp (k)
  "Render kind K as an s-expression, for error messages.
Kinds have no surface syntax of their own to fall back on -- they are
inferred -- so a message that has to show one renders the shape it has
in the graph: `*', `Nat', `(karr a b)', `(kpi x a b)', `(univ T)'."
  (let ((k (tl-kind-deref k)))
    (cond
     ((not (tl-node-p k)) k)
     ((tl-node-var k) 'kind-variable)           ; an undecided kind
     ((not (tl-node-application k)) (tl-node-head k))
     (t (cons (tl-node-head k) (mapcar #'tl-kind->sexp
                                       (tl-node-children k)))))))

(defun tl-kind-parse (sexp &optional vars)
  "Parse surface kind SEXP into a kind node.

Kinds are written only where a datatype parameter is annotated, and the
spelling is deliberately the same one types use, because the two answer
the same question at different levels:

  *                   the kind of a proper type
  K1 -> K2            (also `(karr K1 K2)')  a type constructor's kind
  Nat                 the universe `Nat' is the kind of -- the values
  (univ TYPE)         the universe of an arbitrary TYPE

The last is the one that makes a kind *dependent*.  A bare universe
leaf says which datatype's values a parameter ranges over; `univ' says
it about a parameter that has not been decided yet, which is how
`(x : (univ a))' states that `x' comes out of `a' -- the sentence an
arrow from `*' to `*' cannot say, and the reason `Eq Nat Int Zero' is a
kind error.

VARS, when given, is the list of parameters the annotation may mention.
A name that is not one of them is a typo, and the cost of not saying so
is a kind that speaks about a type nothing will ever decide: the binder
is not in the declaration, so no application can substitute for it, and
every use is refused for a reason that appears nowhere in the message."
  (cl-labels ((check (x)
                (cond
                 ((and (symbolp x) (tl-type-var-symbol-p x))
                  (unless (memq x vars)
                    (signal
                     'termlisp-type-error
                     (list (format
                            "Kind annotation mentions %S, which is not a parameter of this datatype (parameters: %S)"
                            x vars)))))
                 ;; Only the arguments are walked: a form's head is its
                 ;; operator, and `univ' is lowercase-initial for the
                 ;; same reason a datatype name is uppercase-initial --
                 ;; it was chosen, not inherited.
                 ((consp x) (mapc #'check (cdr x))))))
    (when vars (check sexp))
    (cond
     ((eq sexp '*) tl-kind-star)
     ((and (consp sexp) (eq (car sexp) 'univ) (= (length sexp) 2))
      ;; The argument is a *type*, and parses as one -- it is checked
      ;; against the parameter it mentions the way any type is.
      (tl-kuniv (tl-type-parse* (cadr sexp))))
     ((and (consp sexp) (eq (car sexp) 'karr) (= (length sexp) 3))
      (tl-karr (tl-kind-parse (cadr sexp) vars) (tl-kind-parse (caddr sexp) vars)))
     ((and (consp sexp) (eq (car sexp) '->) (cdr sexp) (cddr sexp))
      ;; Right-associative, exactly as an arrow type reads.
      (let ((k (tl-kind-parse (car (last sexp)) vars)))
        (dolist (p (reverse (butlast sexp)))
          (setq k (tl-karr (tl-kind-parse p vars) k)))
        k))
     ((consp sexp)
      (signal 'termlisp-type-error (list (format "Bad kind: %S" sexp))))
     ;; A bare name is a universe: `(n : Nat)' says `n' ranges over the
     ;; values of `Nat', which is what a kind variable used to be left to
     ;; discover at every use.
     ((symbolp sexp) (tl-kind-universe sexp))
     (t (signal 'termlisp-type-error (list (format "Bad kind: %S" sexp)))))))

(defun tl-karity (n)
  "Return the kind of a constructor taking N type arguments."
  (if (<= n 0) tl-kind-star (tl-karr tl-kind-star (tl-karity (1- n)))))

(defun tl-kind-var () (tl-make-var-node 'kind))
(defun tl-kind-deref (k) (if (tl-node-p k) (tl-gnode-deref k) k))

(defun tl-kind-freshen-term (ty memo)
  "Return the type TY with each of its variables replaced by a fresh one.
MEMO maps an old variable to its new one, so a variable appearing twice
comes back as *the same* copy twice -- which is the entire requirement
when the two appearances are a binder and the body that speaks of it.
Rigid variables are left alone: they are fixed by a binder elsewhere
and copying one would make two spellings of one thing compare unequal.
The kind slots inside TY are not touched; they belong to whatever
application put them there."
  (tl-map-type
   (lambda (tv)
     (if (tl-node-rigid tv)
         tv
       (or (gethash tv memo)
           (let ((v (tl-fresh-tvar)))
             (puthash tv v memo)
             v))))
   ty))

(defun tl-kind-freshen (k &optional memo)
  "Return K with every variable replaced by a fresh one.
A datatype's kind is a scheme: `Eq' ranges over every element type and
over every pair of values in it, and its free variables are what say
so.  Each application has to decide those for itself, so the registered
kind is copied rather than unified against.  Unifying in place would let
the first use to mention `Eq' -- its own declaration, even -- fix the
kinds for every use after it.

MEMO carries the copies across one traversal, and the variables copied
are not only kind variables.  A `univ' holds a *type*, and the type's
variables decide what the `univ' means -- `univ(a)' for `VCons' says
which element type the values came from -- so an un-copied `a' would be
solved by the first application and the next application would inherit
the answer.  `Vec' would learn `Nat' from one use and refuse `Vec Bool'
from then on.  Copying them, with the binder copied in the same map so
the body still points at it, is what makes a scheme a scheme."
  (let ((memo (or memo (make-hash-table :test #'eq))))
    (cond ((not (tl-node-p k)) k)
          ((and (tl-node-var-p k) (not (tl-node-rigid k)))
           (or (gethash k memo)
               (let ((v (tl-kind-var))) (puthash k v memo) v)))
          ((eq (tl-node-head k) 'karr)
           (let ((cs (tl-node-children k)))
             (tl-karr (tl-kind-freshen (car cs) memo)
                      (tl-kind-freshen (cadr cs) memo))))
          ;; A `kpi' is freshened in its two kinds and in its binder,
          ;; the three through one map so that the binder in the body is
          ;; still the binder at the head.  It is substituted rather
          ;; than solved at every application -- see `tl-kind-infer' --
          ;; so nothing here has to make it unifiable.
          ((eq (tl-node-head k) 'kpi)
           (let* ((cs (tl-node-children k))
                  (b (nth 0 cs))
                  (nb (if (or (not (tl-node-var-p b)) (tl-node-rigid b))
                          b
                        (or (gethash b memo)
                            (let ((v (tl-fresh-tvar)))
                              (puthash b v memo)
                              v)))))
             (tl-kpi nb
                     (tl-kind-freshen (nth 1 cs) memo)
                     (tl-kind-freshen (nth 2 cs) memo))))
          ((eq (tl-node-head k) 'univ)
           (tl-kuniv (tl-kind-freshen-term
                      (car (tl-node-children k)) memo)))
          (t k))))

(defun tl-kind-star-p (k)
  (eq (tl-kind-deref k) tl-kind-star))

(defun tl-kind-whnf (k)
  "Return K with its head in weak head normal form.
`univ(T)' for a type constructor `T' *is* that constructor's universe
leaf -- the values of `Nat' are `Nat'-kinded -- and reducing it here
rather than leaving the equivalence to the comparison is what lets an
error name `Nat' instead of `univ Nat'.

The universe belongs to the constructor and not to the application, so
`univ((Vec Nat n))' is `Vec' as surely as `univ(Vec)' is.  A vector's
values are `Vec'-kinded whichever `n' they carry; the index is what
makes them vectors and not what makes them the right *kind*.  Restricting
this to a nullary argument would have left `(Vec Nat n)' stuck and
`VCons' unable to meet the kind `Eq' asks of the same value, which is
two spellings of one fact failing to agree.

A `univ' whose argument has no constructor head -- `univ(a)' with `a' a
parameter not yet decided, or a literal, which names no datatype at all
-- has no leaf to become and stays put.  That is the form the
comparison has to read, and it is why `tl-kuniv-unify' exists at all."
  (let ((k (tl-kind-deref k)))
    (if (tl-kuniv-p k)
        (let ((ty (tl-type-deref (tl-kuniv-type k))))
          (if (and (tl-node-p ty)
                   (not (tl-node-var ty))
                   (symbolp (tl-node-head ty)))
              (tl-kind-universe (tl-node-head ty))
            k))
      k)))

(defun tl-kind-unify (a b)
  "Unify kinds A and B (occurs-checked).  Return non-nil on success.

`univ(T)' is deliberately *not* left to the graph unifier.  Structurally
it is an application headed `univ', and a universe leaf is a leaf headed
by a datatype, so the unifier would compare the two heads and call them
unequal -- which is the answer, but only by accident, and it would give
the same answer for the wrong reason whenever the two agreed.  Reading
it directly is what makes the distinction load-bearing: `univ(T)' is the
kind of T's *values*, so it agrees with T's own universe leaf, with
another `univ' of the same type, and with an undecided kind variable.
It does not agree with `*', which is the kind of the *type* -- and
that, and not any amount of structural fussing, is why `Eq Nat Int
Zero' is rejected: `Int' arrives with `*', where an index of `Nat' has
to arrive with `Nat'."
  (let ((a (tl-kind-whnf a))
        (b (tl-kind-whnf b)))
    (cond
     ((not (and (tl-node-p a) (tl-node-p b))) nil)
     ((tl-kuniv-p a) (tl-kuniv-unify a b))
     ((tl-kuniv-p b) (tl-kuniv-unify b a))
     (t (tl-gnode-unify a b t)))))

(defun tl-kuniv-unify (k other)
  "Unify the kind `univ(T)' K with OTHER.  Return non-nil on success."
  (let ((other (tl-kind-deref other))
        (ty (tl-kuniv-type k)))
    (cond
     ;; An undecided position takes the universe whole, and the type
     ;; inside it is then whatever this position is later found to be.
     ((tl-node-var-p other) (tl-gnode-unify other k t))
     ;; Two universes of the same operator agree when their types do.
     ((tl-kuniv-p other) (tl-gnode-unify ty (tl-kuniv-type other) t))
     ;; A universe leaf NAMES the datatype whose values it holds, so
     ;; this is the one place the element type and the index are held to
     ;; each other.  An undecided element type is solved rather than
     ;; refused: `(Eq a x x)' in `Refl''s result has to leave `a' open,
     ;; and it is the leaf that tells the checker which datatype it is
     ;; a value of once anything else has decided.
     ((tl-kind-universe-p other)
      (let ((leaf (tl-node-head other))
            (t2 (tl-type-deref ty)))
        (if (tl-node-var-p t2)
            (tl-gnode-unify t2 (tl-tcon leaf nil) t)
          (and (null (tl-node-children t2))
               (eq (tl-tcon-name t2) leaf)))))
     ;; `*', an arrow, a binder, or another datatype's universe: the
     ;; position was offered one thing and asked for another.  There is
     ;; no third thing it could be, so there is nothing to fall through
     ;; to.
     (t nil))))

(defun tl-register-kind (env name arity)
  "Record that constructor NAME has kind arity ARITY in ENV."
  (puthash name (tl-karity arity) (tl-env-kind-env env)))

(defun tl-kind-of (env name)
  "Return the kind of type constructor NAME in ENV, or nil if unknown."
  (or (gethash name (tl-env-kind-env env))
      (let ((a (cdr (assq name tl-builtin-kinds))))
        (and a (tl-karity a)))))

(defun tl-register-datatype-kind (env name params &optional kinds)
  "Register NAME's kind from its parameter variables' inferred kinds.
PARAMS is the list of parameter type-variable nodes.  KINDS, when given,
is an alist mapping a parameter node to the kind its declaration
annotated it with; an annotated parameter is bound with `kpi' instead of
`karr', which is what makes the resulting kind depend on the parameters
to its left.

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
inconsistently is a kind error there rather than a silent success.

That last sentence is the looseness an annotation exists to close.  A
free parameter lets each of `Eq's three arguments decide *for itself*,
so `Eq Nat Int Zero' decides `Nat', `*' and `Nat' and all three decisions
are individually consistent -- the parameter kinds never mention one
another.  `(datatype (Eq (a : *) (x : (univ a)) (y : (univ a))) ...)'
makes them mention each other: `kpi' binds `a' and the bodies of the
other two speak about it, so `x' and `y' have to be values of whatever
`a' turned out to be.  One declaration, one dependency, and the pair
that used to be checked separately is checked together."
  (let ((k tl-kind-star))
    (dolist (p (reverse params))
      (let* ((ann (and kinds (cdr (assq p kinds))))
             (raw (and (null ann) (tl-node-p p) (tl-node-kind p)))
             (deref (and raw (tl-kind-deref raw)))
             (pk (cond (ann ann)
                       ((or (null deref) (tl-node-var-p deref)) (tl-kind-var))
                       (t deref))))
        (setq k (if ann (tl-kpi p pk k) (tl-karr pk k)))))
    (puthash name k (tl-env-kind-env env))))

(defun tl-kind-universe (name)
  "Return the kind that lifts datatype NAME to the type level.
This is a leaf kind named NAME, and it is deliberately distinct from
`tl-kind-star': `Nat' written as a type has kind `*', while `Nat'
written as a universe is the kind of `Zero'.  One name, two levels --
exactly the double duty Haskell's DataKinds gives it."
  (tl-make-node name nil nil))

(defun tl--lifted-field-kind (env field)
  "Kind FIELD contributes when a constructor is lifted in ENV.
A constructor's arguments are values, not types: `Succ' takes a `Nat',
`VCons' takes a `Vec a n', and what such an argument *is* at the type
level is the universe of its field's type.  Spelling that as `univ'
says it in general.

The old spelling said it only for a field written as the datatype being
lifted, which is why `Succ : Nat -> Nat' was right while
`VCons : * -> * -> Vec' was not: a vector's second field is a vector,
so the value that goes there is `Vec'-kinded, and calling it a proper
type was never contradicted only because nothing else had an opinion
about the same value.  An index in `Eq''s kind is exactly that other
opinion -- `xs' is `Vec Nat n'-kinded there -- and two opinions about
one value are either reconciled or they are a kind error."
  (let ((f (tl-type-deref field)))
    (if (and (tl-node-p f)
             (not (tl-node-var f))
             (null (tl-node-application f))
             (null (tl-node-children f)))
        ;; A nullary constructor is its own universe: `Zero' is taken
        ;; from `Nat' precisely as `tl-kind-universe' spells it, so this
        ;; branch is the old special case with the datatype being lifted
        ;; no longer the only name it applies to.
        (tl-kind-universe (tl-node-head f))
      (condition-case nil
          (tl-kuniv field)
        ;; A field that cannot be turned into a type here -- a literal,
        ;; or something whose head could not be read -- leaves the
        ;; argument free, and the application that supplies a value will
        ;; decide it, as it did before this kind existed.
        (error (condition-case nil (tl-kind-infer env field)
                  (error (tl-kind-var))))))))

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
          (setq k (tl-karr (tl--lifted-field-kind env f) k)))
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
                 (hk (cond ((tl-node-var-p head)
                            (or (tl-node-kind head)
                                (let ((k (tl-kind-var)))
                                  (setf (tl-node-kind head) k) k)))
                           ;; A registered kind is a scheme: copy it, so
                           ;; this application decides its variables
                           ;; without deciding them for the next one.
                           ((tl-kind-freshen (tl-kind-of env head)))
                           (t (tl-kind-var))))
                 (ks arg-ks)
                 (left args)
                 (n 0)
                 (err nil))
            ;; Walk the head's kind against the arguments one at a time
            ;; instead of building the whole expected spine and unifying
            ;; it in one go.  The two agree whenever the head's kind is a
            ;; plain chain of arrows, and they stop agreeing the moment
            ;; it opens with a `kpi', because a dependent binder is not
            ;; matched *by* an arrow -- it is applied *to* an argument.
            ;;
            ;; That application is the entire point.  The binder stands
            ;; for the type this very argument turned out to be, and
            ;; substituting it is what lets the rest of the kind mention
            ;; it.  `Eq : Π(a:*). univ(a) -> univ(a) -> *' asked of
            ;; `Eq Nat Zero Zero' becomes `univ(Nat) -> univ(Nat) -> *'
            ;; right here, and every later check measures against `Nat'
            ;; because of it.  Asked of `Eq Nat Int Zero' it becomes the
            ;; very same kind, and `Int' arrives carrying `*' where
            ;; `univ(Nat)' asks for `Nat' -- so that program stops, and
            ;; stops naming the argument that did it.
            (while (and (null err) ks (or (tl-kpi-p hk) (tl-karr-p hk)))
              (setq n (1+ n)
                    ;; Dereference before reading children, not just
                    ;; before the test above.  A head's kind is read
                    ;; straight out of its KIND slot, and a slot holds a
                    ;; *variable* that some earlier inference has since
                    ;; bound to a chain -- so the predicate can be true
                    ;; of a node whose own children are empty.  Reading
                    ;; them off the underef'd variable would hand back
                    ;; nil for the domain, and nil then fails to unify
                    ;; with anything, which is the kind error nobody
                    ;; asked for.
                    hk (tl-kind-deref hk))
              (let* ((dependent (tl-kpi-p hk))
                     (dom (tl-kind-whnf
                           (if dependent (tl-kpi-domain hk)
                             (car (tl-node-children hk)))))
                     (offered (tl-kind-whnf (car ks))))
                (if (not (tl-kind-unify dom offered))
                    (setq err (list (format
                                     (concat "Kind error: %S argument %d is a %S"
                                             " where a %S is required")
                                     (if (symbolp head) head "type variable")
                                     n
                                     (tl-kind->sexp offered)
                                     (tl-kind->sexp dom))))
                  (setq hk (if dependent
                               (tl-gnode-subst (tl-kpi-body hk)
                                               (tl-kpi-binder hk)
                                               (car left))
                             (nth 1 (tl-node-children hk)))
                        ks (cdr ks)
                        left (cdr left)))))
            ;; A head whose kind is unknown has no chain to walk, so it
            ;; takes the whole spine at once -- the shape the old code
            ;; always built, reached now only when the head is genuinely
            ;; undecided.
            (when (and (null err) ks (tl-node-var-p (tl-kind-deref hk)))
              (let* ((res (tl-kind-var))
                     (w res))
                (dolist (ak (reverse ks)) (setq w (tl-karr ak w)))
                (if (tl-kind-unify (tl-kind-deref hk) w)
                    (setq hk res ks nil)
                  (setq err (list "Kind error: recursive kind")))))
            ;; Arguments left over with nowhere to go: too many.
            (when (and (null err) ks)
              (setq err (list (format "Kind error: %S applied to %d argument(s)"
                                      (if (symbolp head) head "type variable")
                                      (length args)))))
            (when err (signal 'termlisp-type-error err))
            ;; What comes back is the head's kind with its arguments
            ;; taken off: `*' for a fully applied type constructor, an
            ;; arrow or a binder for a partial one -- which is exactly
            ;; what a partial application means, and why it is not a
            ;; proper type.
            hk))))
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
