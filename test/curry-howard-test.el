;;; curry-howard-test.el --- propositional layer and type-check safety -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Stages 0, 1 and 2(a) of the Curry-Howard roadmap.  Stage 0 is `Void',
;; `Either' and `absurd'; Stage 1 is the indexed families (GADT) built
;; on them -- `Vec', `Fin' and the type-level `Refl' -- together with the
;; cases that must keep being rejected.  Stage 2(a) opens the type
;; language to terms: `Pi' binders, type-level lambda, literals and term
;; applications, all on the same term graph the unifier already used.

;;; Code:

(require 'test-support)

;;; Stage 0: Void, Either and absurd

(tl-test-eval tl-ch-prelude-loads-with-void "1" "1" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-void-usable-in-a-signature "(: f (Void -> Int)) (define (f x) 1) (f Void)" "1" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-right-infers "(Right \"s\")" "(Right s)" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-left-in-a-signature "(: g (Either Int String)) (define (g) (Left 1)) (g)" "(Left 1)" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-right-in-a-signature "(: g (Either Int String)) (define (g) (Right \"x\")) (g)" "(Right x)" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-destructure-left "(define (from-left (Left x)) x) (from-left (Left 7))" "7" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-destructure-right "(define (from-right (Right x)) x) (from-right (Right 7))" "7" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-map-over-left "(define (el f (Left x)) (Left (f x))) (el (lambda (n) (+ n 1)) (Left 1))" "(Left 2)" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-map-over-right "(define (er f (Right x)) (Right (f x))) (er (lambda (n) (+ n 1)) (Right 1))" "(Right 2)" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-two-eithers-unify-in-a-list "(list (Left 1) (Right 2))" "(Cons (Left 1) (Cons (Right 2) Nil))" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-void-int-result "(: q (Void -> Int)) (define (q v) (absurd v)) q" "q" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-void-bool-result-polymorphic-result "(: r (Void -> Bool)) (define (r v) (absurd v)) r" "r" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-void-a-where-a-inferred "(define (q v) (absurd v)) q" "q" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-not-void-void-void "(: not-void (Void -> Void)) (define (not-void v) v) not-void" "not-void" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-conjunction-implies-disjunction "(define (air (Pair a b)) (Left a)) (define (w p) (air p)) (w (Pair True False))" "(Left True)" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-disjunction-implies-pair-is-conjunction "(define (proj-a (Pair a b)) a) (proj-a (Pair True False))" "True" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-double-negation-void-void-void "(: nn (Void -> (Void -> Void))) (define (nn v) (lambda (w) v)) nn" "nn" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-either-mixed-with-a-non-either-rejected "(list (Left 1) 42)" "Cannot apply Cons" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-absurd-rejects-a-non-void-argument "(absurd 1)" "Cannot apply absurd" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-absurd-rejects-bool-at-a-call-site "(: q (Void -> Int)) (define (q v) (absurd v)) (q 1)" "Cannot apply q" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-absurd-s-error-path-type-check-off "(absurd Void)" "absurd: Void has no values")

;;; Type-checker rejection safety

(tl-test-reject tl-typecheck-bind-maybe-monad-list-step "(bind (Just 1) (lambda (x) (Cons x Nil)))" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-do-mixing-maybe-and-list "(do (x <- (Just 1)) (y <- (Cons 1 Nil)) (return x))" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-identity-cannot-be-a-monadic-step "(bind (Just 1) (lambda (x) x))" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-bind-applied-to-a-dictionary "(bind MaybeDict (Just 1) maybe-return)" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-signature-demands-the-wrong-ctor "(: g (Either Int String)) (define (g) (Just 1)) g" "does not match its signature" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-arithmetic-across-types "(+ 1 True)" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-string-op-on-a-number "(string->list 42)" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-list-element-mismatch "(list 1 True)" "Cannot apply" '(:type-check t :elaborate t))
(tl-test-reject tl-typecheck-absurd-on-a-non-void "(absurd 1)" "Cannot apply absurd" '(:type-check t :elaborate t))
(tl-test-eval tl-typecheck-bind-maybe-step "(bind (Just 1) (lambda (x) (Just (+ x 1))))" "(Just 2)" '(:type-check t :elaborate t))
(tl-test-eval tl-typecheck-bind-list-step "(bind (Cons 1 Nil) (lambda (x) (Cons (* x 10) Nil)))" "(Cons 10 Nil)" '(:type-check t :elaborate t))
(tl-test-eval tl-typecheck-two-bind-do "(do (x <- (Just 1)) (y <- (Just 2)) (return (+ x y)))" "(Just 3)" '(:type-check t :elaborate t))
(tl-test-eval tl-typecheck-fmap-list-of-maybe-is-well-typed "(fmap (lambda (x) (Just x)) (Cons 1 Nil))" "(Cons (Just 1) Nil)" '(:type-check t :elaborate t))
(tl-test-eval tl-typecheck-either-pattern-match "(define (fl (Left x)) x) (fl (Left 7))" "7" '(:type-check t :elaborate t))


;;; Structural registration

;; These three cannot be expressed through `tl-test-eval': they read the
;; environment directly rather than evaluating a form.

(defun tl-ch--typed-env ()
  "Return a fresh prelude environment with checking and elaboration enabled."
  (termlisp-load-prelude (termlisp-make-env '(:type-check t :elaborate t))))

(ert-deftest tl-ch-void-registered-as-a-datatype ()
  "Void must be registered as a datatype carrying no constructors."
  (let ((spec (gethash 'Void (tl-env-datatypes (tl-ch--typed-env)))))
    (should spec)
    (should (null (plist-get spec :constructors)))))

(ert-deftest tl-ch-void-has-arity-zero-kind ()
  "Void must live at the kind of a plain type, not at a function kind."
  (let ((kind (gethash 'Void (tl-env-kind-env (tl-ch--typed-env)))))
    (should (or (eq kind 0)
                (and (numberp kind) (= kind 0))
                (and (not (numberp kind))
                     (condition-case nil
                         (progn (termlisp-value->string kind) t)
                       (error nil)))))))

(ert-deftest tl-ch-no-constructor-produces-void ()
  "Void must stay uninhabited: no datatype constructor may return it."
  (let* ((env (tl-ch--typed-env))
         (makers (cl-loop for name being the hash-keys of (tl-env-constructors env)
                          using (hash-values ty)
                          when (eq ty 'Void)
                          collect name)))
    (should-not makers)))

;;; Stage 1: indexed families (GADT)

;; A constructor written `: RESULT' declares its own result type, and
;; the datatype's kind records what each index is allowed to be.  Both
;; halves are asserted here: the kinds structurally, the index
;; refinement by the errors it produces.

(defun tl-ch--kind-text (k)
  "Render kind K as text, following the graph's bindings."
  (let ((k (tl-kind-deref k)))
    (cond ((eq k tl-kind-star) "*")
          ((and (tl-node-p k) (eq (tl-node-head k) 'karr))
           (let ((cs (tl-node-children k)))
             (format "(%s -> %s)" (tl-ch--kind-text (car cs))
                     (tl-ch--kind-text (cadr cs)))))
          ;; A parameter nothing has constrained renders as `?', which is
          ;; what makes an index parameter visible: it ranges over
          ;; universes as well as over proper types.
          ((and (tl-node-p k) (tl-node-var-p k)) "?")
          ((tl-node-p k) (format "%S" (tl-node-head k)))
          (t (format "%S" k)))))

(defun tl-ch--kind-string (env name)
  "Return the kind of type constructor NAME in ENV, as text."
  (let ((k (tl-kind-of env name)))
    (if k (tl-ch--kind-text k) "nil")))

(defun tl-ch--scheme-text (env name)
  "Return constructor NAME's scheme in ENV, as text."
  ;; `tl-type-to-datum' hands back a sexp; printing it is what makes the
  ;; index expressions matchable with a regexp below.
  (format "%S"
          (tl-type-to-datum
           (tl-tscheme-type (gethash name (tl-env-type-env env))))))

(ert-deftest tl-ch-lifted-constructors-have-universe-kinds ()
  "A datatype promotes its constructors into its own universe."
  (let ((env (tl-ch--typed-env)))
    (should (equal (tl-ch--kind-string env 'Nat) "*"))
    (should (equal (tl-ch--kind-string env 'Zero) "Nat"))
    (should (equal (tl-ch--kind-string env 'Succ) "(Nat -> Nat)"))
    (should (equal (tl-ch--kind-string env 'Bool) "*"))
    (should (equal (tl-ch--kind-string env 'True) "Bool"))))

(ert-deftest tl-ch-indexed-datatype-kinds ()
  "An indexed family records the kind its index must satisfy."
  (let ((env (tl-ch--typed-env)))
    (should (equal (tl-ch--kind-string env 'Vec) "(* -> (Nat -> *))"))
    (should (equal (tl-ch--kind-string env 'Fin) "(Nat -> *)"))))

(ert-deftest tl-ch-equal-s-kind-is-fully-general ()
  "`Eq' indexes by values, so nothing has constrained its parameters.
`Vec' fixes its index to `Nat' because `Succ' says so.  `Refl' is
nullary and says nothing at all, so `Eq' ranges over every element type
and every pair of values in it -- which is what lets one declaration
mean equality on naturals, on lists, on anything."
  (let ((env (tl-ch--typed-env)))
    (should (equal (tl-ch--kind-string env 'Eq) "(? -> (? -> (? -> *)))"))))

(ert-deftest tl-ch-constructor-schemes-carry-indices ()
  "A constructor returns at its own index, not at the datatype's parameters."
  (let ((env (tl-ch--typed-env)))
    ;; VNil is pinned at Zero and VCons at one past its tail's index --
    ;; neither can come back out as `Vec' applied to bare parameters.
    (should (string-match-p "(Vec .*Zero)" (tl-ch--scheme-text env 'VNil)))
    (should (string-match-p "(Vec .* (Succ .*))" (tl-ch--scheme-text env 'VCons)))
    (should (string-match-p "(Fin (Succ .*))" (tl-ch--scheme-text env 'FZ)))
    ;; An ordinary constructor still defaults to the datatype's
    ;; parameters: `Maybe' applied to a variable, with no index smuggled
    ;; into the result.
    (should (string-match-p "(Maybe .*)" (tl-ch--scheme-text env 'Just)))
    (should-not (string-match-p "Zero\\|Succ" (tl-ch--scheme-text env 'Just)))))

(ert-deftest tl-ch-split-ctor-checks-its-marker ()
  "A stray `:' is an error rather than a silently truncated constructor."
  (should (equal (tl-split-ctor '(C a b)) '((a b))))
  (should (equal (tl-split-ctor '(C a : R)) '((a) . R)))
  (should-error (tl-split-ctor '(C :)) :type 'termlisp-type-error)
  (should-error (tl-split-ctor '(C a : R S)) :type 'termlisp-type-error))

(tl-test-eval tl-ch-vec-empty-annotated
  "(: v (Vec Int Zero)) (define v VNil) v" "VNil" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-vec-one-annotated
  "(: v (Vec Int (Succ Zero))) (define v (VCons 1 VNil)) v"
  "(VCons 1 VNil)" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-vec-index-of-the-wrong-sort
  "(: v (Vec Int String))" "Kind error" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-vec-cons-at-the-empty-index
  "(: v (Vec Int Zero)) (define v (VCons 1 VNil)) v"
  "does not match its signature" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-vec-pattern-refines-the-index
  "(define (vhd (VCons x xs)) x) (vhd (VCons 7 VNil))"
  "7" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-vec-pattern-on-the-empty-vector
  "(define (vhd (VCons x xs)) x) (vhd VNil)"
  "Cannot apply vhd to VNil" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-fin-at-a-successor
  "(: f (Fin (Succ Zero))) (define f FZ) f" "FZ" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-fin-at-zero
  "(: f (Fin Zero)) (define f FZ) f"
  "does not match its signature" '(:type-check t :elaborate t))
;; `Eq' takes an element type and two values in it, so the one-parameter
;; application that Stage 1's placeholder allowed is a partial
;; application now -- well-formed syntax, but not a type.
(tl-test-reject tl-ch-eq-applied-to-too-few-arguments
  "(: r (Eq Int)) (define r (Refl)) r"
  "is not a proper type" '(:type-check t :elaborate t))

;;; Stage 2 (a): terms in types -- the unified term graph

;; Until now a type could be built only from type constructors: the parser
;; structurally excluded anything that was a term.  These cases open that
;; up -- `Pi' binders, type-level lambda, literals and term applications
;; inside a type -- and pin the two properties that make the representation
;; sound: a binder's variable is *rigid* (unification may match it only
;; against itself), and it is still a variable (substitution reaches it).

(tl-test-type tl-ch-pi-binder-in-an-arrow-chain
              '((n : Nat) -> (Vec a n) -> a)
              '((n : Nat) -> (-> (Vec %1 n) %1)))
(tl-test-type tl-ch-plain-arrow-stays-an-arrow '(Int -> Int) '(-> Int Int))
(tl-test-type tl-ch-arrow-inside-a-constructor
              '(List (Int -> Int)) '(List (-> Int Int)))
(tl-test-type tl-ch-numeric-literal-in-a-type '(Vec a 3) '(Vec %1 3))
(tl-test-type tl-ch-string-literal-in-a-type '(Vec a "s") '(Vec %1 "s"))
;; A lower-case head is a *term* application, not a type constructor --
;; this is the `n + m' that `append' will be indexed by.
(tl-test-type tl-ch-term-application-in-a-type
              '(Vec a (plus n m)) '(Vec %1 (plus %2 %3)))
(tl-test-type tl-ch-type-level-lambda
              '(lambda (n) (Vec a n)) '(lambda (n) (Vec %1 n)))

(ert-deftest tl-ch-pi-round-trips-through-the-reader ()
  "A rendered `Pi' must parse back to the same type.
Without this the REPL would show a type the reader could not re-read."
  (let* ((src '((n : Nat) -> (Vec a n) -> a))
         (d1 (tl-type-to-datum (tl-type-parse src))))
    (should (equal (tl-type-to-datum (tl-type-parse d1)) d1))))

(ert-deftest tl-ch-pi-binder-scopes-over-its-codomain ()
  "Both occurrences of `n' must be the very same node.
Sharing is what lets a later unification see them as one thing; two
distinct nodes that merely render alike would silently fail to unify."
  (let* ((pi (tl-type-parse '((n : Nat) -> (Vec a n))))
         (args (tl-tcon-args pi)))
    (should (eq (nth 1 (tl-tcon-args (nth 2 args))) (nth 0 args)))))

(ert-deftest tl-ch-pi-binder-is-rigid-but-still-a-variable ()
  "A binder must be unsubstitutable-by-unification, substitutable-by-elaboration.
The two are deliberately separate: without rigidity, unifying
`((n : Nat) -> Vec a n)' with `((n : Nat) -> Vec Int Zero)' would let a
caller rewrite the very type `n' was declared over.  Without `var' being
set, instantiating the binder could not reach it at all."
  (let* ((pi (tl-type-parse '((n : Nat) -> (Vec a n))))
         (binder (nth 0 (tl-tcon-args pi))))
    (should (tl-node-rigid binder))
    (should (tl-node-var-p binder))
    ;; A name the binder does not mention stays an ordinary variable.
    (should-not (tl-node-rigid (nth 0 (tl-tcon-args (nth 2 (tl-tcon-args pi))))))))

(ert-deftest tl-ch-rigid-binder-refuses-to-unify-with-a-term ()
  "A dependent function type may not be forced onto one that ignores its binder."
  (let ((a (tl-type-parse '((n : Nat) -> (Vec a n))))
        (b (tl-type-parse '((n : Nat) -> (Vec Int Zero)))))
    (should-not (car (tl-unify-types a b nil)))))

(ert-deftest tl-ch-two-pis-unify-up-to-the-binder-name ()
  "Two dependent function types are equal up to what their binders are called."
  (let ((a (tl-type-parse '((n : Nat) -> (Vec a n))))
        (b (tl-type-parse '((m : Nat) -> (Vec a m)))))
    (should (car (tl-unify-types a b nil)))))

(ert-deftest tl-ch-pi-unification-binds-the-shared-variable ()
  "A variable discovered inside the codomain must bind in the original type.
The comparison works on a re-spelled copy; if that copy shared nothing,
unifying `(n : Nat) -> Vec a n' with `(m : Nat) -> Vec Int m' would leave
`a' unbound and the caller none the wiser."
  (let ((a (tl-type-parse '((n : Nat) -> (Vec a n))))
        (b (tl-type-parse '((m : Nat) -> (Vec Int m)))))
    (should (car (tl-unify-types a b nil)))
    (should (equal (tl-test--alpha (tl-type-to-datum a))
                   '((n : Nat) -> (Vec Int n))))))

(ert-deftest tl-ch-ordinary-variables-still-bind ()
  "Opening the parser up to terms must not disturb ordinary unification."
  (let ((a (tl-type-parse '(List a)))
        (b (tl-type-parse '(List Int))))
    (should (car (tl-unify-types a b nil)))))

(ert-deftest tl-ch-pi-is-a-proper-type ()
  "A `Pi' must kind as `*', and its domain and codomain must be types."
  (should (tl-kind-check (tl-ch--typed-env)
                         (tl-type-parse '((n : Nat) -> (Vec a n) -> a)))))

(ert-deftest tl-ch-pi-binder-kind-is-pinned-by-its-use ()
  "Using `n' as `Vec's index is what fixes its kind to `Nat'.
The binder's kind is left open on purpose: it is whatever its uses
demand, and only a use can say what that is."
  (let* ((ty (tl-type-parse '((n : Nat) -> (Vec a n) -> a)))
         (binder (nth 0 (tl-tcon-args ty))))
    ;; Kind-checking is what runs the uses, so it comes first: until a
    ;; use has been seen the binder's kind is not merely unknown, it has
    ;; not been looked for.
    (tl-kind-check (tl-ch--typed-env) ty)
    (should (tl-node-kind binder))
    (should (tl-kind-unify (tl-node-kind binder) (tl-kind-universe 'Nat)))))

(ert-deftest tl-ch-pi-over-a-function-typed-domain-is-well-kinded ()
  "A binder may range over a function: `(f : Nat -> Nat) -> ...' is legitimate."
  (should (tl-kind-check (tl-ch--typed-env)
                         (tl-type-parse '((n : (Nat -> Nat)) -> a)))))

;;; Stage 2 (c) + (e): reduction in the checker, bidirectional elaboration

;; Definitional equality compared types structurally, so `plus Zero n'
;; and `n' were two different types however they were spelled -- and an
;; indexed family's clauses could not be checked at all, since they share
;; no unifier.  These cases pin the reduction hook in the unifier, the
;; implicit binders that make `append' a two-argument function, and the
;; per-clause check that lets such a definition be written down.

(ert-deftest tl-ch-definitional-equality-reduces-an-index ()
  "`Vec Int Zero' and `Vec Int (plus Zero Zero)' are one type.
The second is the first with a type-level function written into its
index, and nothing but reduction can see that they are the same."
  (let* ((env (tl-ch--typed-env))
         (tl-nbe-reduce-env env)
         (a (tl-type-parse '(Vec Int Zero)))
         (b (tl-type-parse '(Vec Int (plus Zero Zero)))))
    (should (car (tl-unify-types a b nil)))))

(ert-deftest tl-ch-no-reduction-without-an-environment ()
  "With nothing to unfold a function against the two stay distinct.
This is what keeps ordinary Hindley-Milner checking clear of any
evaluator: unification stays structural unless something supplies the
definitions to reduce against."
  (let ((a (tl-type-parse '(Vec Int Zero)))
        (b (tl-type-parse '(Vec Int (plus Zero Zero)))))
    (should-not (car (tl-unify-types a b nil)))))

(ert-deftest tl-ch-reduction-that-does-nothing-is-not-a-proof ()
  "A pair that has not moved after being reduced is simply not equal.
Dropping it instead of failing would let the `seen' guard take the repeat
for a recursive type equating itself -- which is how a two-domain
definition once satisfied a four-domain signature, and every definition
with it."
  (let* ((env (tl-ch--typed-env))
         (tl-nbe-reduce-env env)
         (a (tl-type-parse 'Int))
         (b (tl-type-parse '(plus Zero Zero))))
    (should-not (car (tl-unify-types a b nil)))))

(ert-deftest tl-ch-unification-reads-arguments-left-to-right ()
  "`Vec a (plus n m)' may only be compared after `Vec a n' fixed `n'.
Children came off the worklist in reverse, so a function's result type
was compared before its argument types and the type-level function had
nothing to match on."
  (let* ((env (tl-ch--typed-env))
         (tl-nbe-reduce-env env)
         (a (tl-type-parse '(-> (Vec t (Succ k)) (-> (Vec t m)
                                                     (Vec t (Succ (plus k m)))))))
         (b (tl-type-parse '(-> (Vec t n) (-> (Vec t m2)
                                              (Vec t (plus n m2)))))))
    (should (car (tl-unify-types a b nil)))))

;;; Signature binders: implicit parameters and explicit arguments

(tl-test-type tl-ch-an-ordinary-segment-is-never-a-binder
              '(-> a b) '(-> %1 %2))
(tl-test-type tl-ch-several-names-over-one-domain
              '(-> (n m : Nat) (Vec a n))
              '((n : Nat) -> ((m : Nat) -> (Vec %1 n))))

(defun tl-ch--arrow-count (ty)
  "Return how many arrow and Pi nodes TY renders with.
Both spell one arrow operand per `(', so counting them in the rendered
datum is one test that does not care which struct either happens to be."
  (let* ((d (tl-test--alpha (tl-type-to-datum ty)))
         (s (format "%S" d))
         (n 0) (start 0))
    (while (string-match "(->" s start)
      (setq n (1+ n) start (match-end 0)))
    n))

(ert-deftest tl-ch-a-mentioned-binder-becomes-implicit ()
  "`Vec a n -> Vec a m -> Vec a (plus n m)' takes two arguments, not four.
`n' and `m' are fixed by the vectors themselves, so a signature that
binds them must not ask the caller to pass them: they are quantified
alongside every other variable of the type."
  (let ((env (tl-ch--typed-env)))
    (termlisp-eval
     "(: appd (-> (n m : Nat) (Vec a n) (Vec a m) (Vec a (plus n m))))" env)
    (should (= 2 (tl-ch--arrow-count
                  (tl-tscheme-type (gethash 'appd (tl-env-type-env env))))))))

(ert-deftest tl-ch-an-unmentioned-binder-stays-an-argument ()
  "`(n : Nat) -> Nat' names nothing the type uses, so the argument stays.
Dropping it would silently change the arity of every definition written
against the signature, and the name carried no information to begin with
-- that is precisely why nothing mentioned it."
  (let ((env (tl-ch--typed-env)))
    (termlisp-eval "(: keep (-> (n : Nat) Nat)) (define (keep n) Zero) keep"
                   env)
    (should (equal (tl-test--alpha (tl-type-to-datum
                                    (tl-tscheme-type
                                     (gethash 'keep (tl-env-type-env env)))))
                   '(-> Nat Nat)))))

;;; A binder's domain may be written as it reads

;; `:' used to be looked for exactly one token from the end of the
;; binder, so a domain containing a bare `->' or a bare application came
;; back as something else entirely: `(f : a -> b)' split at that arrow
;; into `f : a' and `b', and `f' was then parsed applied to the keyword
;; `:'.  Nothing complained at the point of writing -- the nonsense type
;; only surfaced later as a stray kind error, if it surfaced at all.
;; The domain now runs from the `:' to the end, so both spellings below
;; and their parenthesised spellings agree.

(tl-test-type tl-ch-a-domain-arrow-binds-the-name
              '(-> (f : a -> b) Int)
              '((f : (-> %1 %2)) -> Int))

(tl-test-type tl-ch-a-domain-application-binds-the-name
              '(-> (xs : Vec a n) Nat)
              '((xs : (Vec %1 %2)) -> Nat))

(tl-test-type tl-ch-a-parenthesised-domain-still-binds-the-name
              '(-> (xs : (Vec a n)) Nat)
              '((xs : (Vec %1 %2)) -> Nat))

;; The combinator every arithmetic proof needs, written the way it
;; reads.  `f' is mentioned by the codomain but no later argument fixes
;; it, so the Pi stays and `cong' takes the function as well: a plain
;; arrow would strand every `(f x)' in its own codomain on a binder that
;; was no longer there.  What the proof argument alone could not say --
;; which function -- is now the caller's to say, and the theorem it is
;; used in decides whether that is a cost.
(tl-test-eval tl-ch-cong-takes-the-function-its-codomain-mentions
  "(: cong (-> (a : *) (b : *) (x : a) (y : a) (f : a -> b)
                (Eq a x y) (Eq b (f x) (f y))))
   (define (cong f Refl) Refl)
   (: step (-> (n : Nat) (Vec Nat n) (Eq Nat (plus n Zero) n)
                        (Eq Nat (Succ (plus n Zero)) (Succ n))))
   (define (step VNil ih) (cong Succ ih))
   (step VNil Refl)"
  "Refl" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-cong-will-not-take-the-proof-alone
  "(: cong (-> (a : *) (b : *) (x : a) (y : a) (f : a -> b)
                (Eq a x y) (Eq b (f x) (f y))))
   (define (cong Refl) Refl) cong"
  "does not match its signature" '(:type-check t :elaborate t))

;;; `append': the stage-2 deliverable

(tl-test-eval tl-ch-append-typechecks
  "(: appd (-> (n m : Nat) (Vec a n) (Vec a m) (Vec a (plus n m))))
   (define (appd VNil ys) ys)
   (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))
   appd" "appd" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-append-runs
  "(: appd (-> (n m : Nat) (Vec Int n) (Vec Int m) (Vec Int (plus n m))))
   (define (appd VNil ys) ys)
   (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))
   (appd (VCons 1 VNil) (VCons 2 VNil))"
  "(VCons 1 (VCons 2 VNil))" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-append-rejects-a-different-element-type
  "(: appd (-> (n m : Nat) (Vec Int n) (Vec Int m) (Vec Int (plus n m))))
   (define (appd VNil ys) ys)
   (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))
   (appd (VCons 1 VNil) (VCons \"two\" VNil))"
  "Cannot apply appd" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-append-rejects-the-wrong-result-index
  "(: appd (-> (n m : Nat) (Vec Int n) (Vec Int m) (Vec Int Zero)))
   (define (appd VNil ys) ys)
   (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))"
  "does not match its signature" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-append-rejects-the-wrong-arity
  "(: appd (-> (n m : Nat) (Vec Int n) (Vec Int m) (Vec Int (plus n m))))
   (define (appd VNil) VNil)"
  "does not match its signature" '(:type-check t :elaborate t))
;; Checking each clause against its own instance of the signature must
;; not weaken ordinary definitions.
(tl-test-reject tl-ch-clauses-still-agree-without-a-signature
  "(define (f VNil) 1) (define (f (VCons x xs)) \"s\") f"
  "inconsistent type" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-an-ordinary-signature-is-still-enforced
  "(: g (-> Int String)) (define (g) 1) g"
  "does not match its signature" '(:type-check t :elaborate t))

;;; A theorem proved by induction

;; Stage 3's test is not that `Eq' exists but that a statement about an
;; indexed family can be proved by cases on that family itself, with the
;; induction hypothesis doing work no amount of computing could do.
;; `lenAppend' needs both halves and neither substitutes for the other:
;; the base case is decided by `vapp' reducing, the step by what comes
;; back from the recursive call.  Its signature is also the first thing
;; written here that needed the *third* answer of
;; `tl-signature-binders' -- `xs' and `ys' are mentioned by the
;; codomain and fixed by nothing after them, so only keeping their Pi
;; gives the theorem the two vectors it is about.

;; A congruence rule is a lemma, not a primitive -- the prelude stops at
;; `sym' and `trans' -- so the theorems below carry their own, proved by
;; matching `Refl'.
(defconst tl-ch--cong
  "(: cong (-> (a : *) (b : *) (x : a) (y : a) (f : a -> b)
                (Eq a x y) (Eq b (f x) (f y))))
   (define (cong f Refl) Refl)"
  "The congruence rule, as a theorem rather than a primitive.
Matching the proof against `Refl' refines the two indices to one term,
and the body's `Refl' then covers the statement.")

(defconst tl-ch--len-append
  (concat tl-ch--cong "
   (: vapp (-> (a : *) (n : Nat) (m : Nat)
                (Vec a n) (Vec a m) (Vec a (plus n m))))
   (define (vapp VNil ys) ys)
   (define (vapp (VCons x xs) ys) (VCons x (vapp xs ys)))
   (: lenV (-> (a : *) (n : Nat) (Vec a n) Nat))
   (define (lenV VNil) Zero)
   (define (lenV (VCons x xs)) (Succ (lenV xs)))
   (: lenAppend (-> (a : *) (n : Nat) (m : Nat)
                     (xs : Vec a n) (ys : Vec a m)
                     (Eq Nat (lenV (vapp xs ys))
                            (plus (lenV xs) (lenV ys)))))
   (define (lenAppend VNil ys) Refl)
   (define (lenAppend (VCons x xs) ys) (cong Succ (lenAppend xs ys)))")
  "Vector append and its length, the stage-3 theorem proved by induction.")

(tl-test-eval tl-ch-the-base-case-is-decided-by-reduction
  (concat tl-ch--len-append " (lenAppend VNil VNil)")
  "Refl" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-the-step-is-decided-by-the-hypothesis
  (concat tl-ch--len-append " (lenAppend (VCons Zero VNil) VNil)")
  "Refl" '(:type-check t :elaborate t))

;; The step case with the recursive call replaced by `Refl'.  Nothing
;; computes `lenV (vapp (VCons x xs) ys)' down to `plus (lenV (VCons x
;; xs)) (lenV ys)' -- what is left over is exactly the statement for the
;; tail, so without the hypothesis the two sides are one constructor and
;; an unstuck `plus' apart, and no proof is there to be written.
(tl-test-reject tl-ch-the-induction-hypothesis-cannot-be-skipped
  "(: vapp (-> (a : *) (n : Nat) (m : Nat)
                (Vec a n) (Vec a m) (Vec a (plus n m))))
   (define (vapp VNil ys) ys)
   (define (vapp (VCons x xs) ys) (VCons x (vapp xs ys)))
   (: lenV (-> (a : *) (n : Nat) (Vec a n) Nat))
   (define (lenV VNil) Zero)
   (define (lenV (VCons x xs)) (Succ (lenV xs)))
   (: broken (-> (a : *) (n : Nat) (m : Nat)
                  (xs : Vec a n) (ys : Vec a m)
                  (Eq Nat (lenV (vapp xs ys))
                         (plus (lenV xs) (lenV ys)))))
   (define (broken VNil ys) Refl)
   (define (broken (VCons x xs) ys) Refl) broken"
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-a-false-theorem-is-not-provable
  "(: bad (-> (n : Nat) (Vec Nat n) (Eq Nat (plus n Zero) (Succ n))))
   (define (bad VNil) Refl) (bad VNil)"
  "does not match its signature" '(:type-check t :elaborate t))

;;; Congruence, by matching rather than by a primitive

;; `lenAppend' was the first theorem proved by induction, but it works by
;; the constructor's own arithmetic: `plus' commutes past `Succ' on its
;; own.  Anything about a *container* needs to step under its head --
;; and that is congruence, which `cong' provides only when the two
;; spellings of the goal happen to line up (a constructor applied to
;; everything it takes, say).  It does not line up for a `Vec' element,
;; so congruence is derived here instead of imported: matching the
;; hypothesis against `Refl' refines `xs' to `ys', and once it has,
;; both sides of the goal are literally the same term.

(tl-test-eval tl-ch-congruence-under-a-vector-head
  "(: cng (-> (n : Nat) (x : Nat) (xs : Vec Nat n) (ys : Vec Nat n)
               (Eq (Vec Nat n) xs ys)
               (Eq (Vec Nat (Succ n)) (VCons x xs) (VCons x ys))))
   (define (cng x Refl) Refl)
   (cng Zero Refl)"
  "Refl" '(:type-check t :elaborate t))

;; Writing the hypothesis as a plain variable works just as well, and
;; that is worth pausing on: nothing refined `xs' to `ys' this time, so
;; the body got two indices *it* had to choose.  What makes the choice
;; legal is the argument itself -- `h : Eq (Vec Nat n) xs ys' says the
;; two are one, and unification is free to say which.  The same body
;; with the hypothesis argument withdrawn is refused, because there the
;; choice is the body's alone (`tl-ch-a-universal-index-cannot-be-invented').
(tl-test-eval tl-ch-the-hypothesis-argument-licenses-the-tie
  "(: cng (-> (n : Nat) (x : Nat) (xs : Vec Nat n) (ys : Vec Nat n)
               (Eq (Vec Nat n) xs ys)
               (Eq (Vec Nat (Succ n)) (VCons x xs) (VCons x ys))))
   (define (cng x h) Refl) cng"
  "cng" '(:type-check t :elaborate t))

;; `map id = id', and `map (f . g) = map f . map g'.  Both step under a
;; `VCons', and the inductive case is `cng' applied to the induction
;; hypothesis -- the shape every container theorem takes.

;; `cong' is not in the prelude, so these theorems carry their own --
;; the same rule `lenAppend' uses, proved by matching `Refl' exactly as
;; below.
(defconst tl-ch--vec-mp
  (concat tl-ch--cong "
   (: mp (-> (a : *) (b : *) (n : Nat) (a -> b) (Vec a n) (Vec b n)))
   (define (mp f VNil) VNil)
   (define (mp f (VCons x xs)) (VCons (f x) (mp f xs)))
   (: cng (-> (n : Nat) (x : Nat) (xs : Vec Nat n) (ys : Vec Nat n)
               (Eq (Vec Nat n) xs ys)
               (Eq (Vec Nat (Succ n)) (VCons x xs) (VCons x ys))))
   (define (cng x Refl) Refl)")
  "Congruence under a vector head, plus the `map' it proves theorems about.")

(tl-test-eval tl-ch-map-of-the-identity-is-the-identity
  (concat tl-ch--vec-mp "
   (: t (-> (n : Nat) (xs : Vec Nat n)
             (Eq (Vec Nat n) (mp (lambda (y) y) xs) xs)))
   (define (t VNil) Refl)
   (define (t (VCons x xs)) (cng x (t xs)))
   (t VNil)")
  "Refl" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-map-fusion-holds
  (concat tl-ch--vec-mp "
   (: fus (-> (n : Nat) (f : Nat -> Nat) (g : Nat -> Nat) (xs : Vec Nat n)
               (Eq (Vec Nat n)
                   (mp f (mp g xs))
                   (mp (lambda (y) (f (g y))) xs))))
   (define (fus f g VNil) Refl)
   (define (fus f g (VCons x xs)) (cng (f (g x)) (fus f g xs)))
   (fus (lambda (y) y) (lambda (y) y) VNil)")
  "Refl" '(:type-check t :elaborate t))

;;; A signature's binder decision runs the whole chain

;; `tl-signature-binders' judges each leading binder by whether
;; anything *after* it fixes the value down.  It used to stop at the
;; first binder that stayed explicit, which meant one explicit argument
;; froze every binder behind it: `(x : Nat) -> (n : Nat) -> Vec Nat n ->
;; Eq Nat x x' leaves `n' fixed by the vector after all, but the walk
;; never got there, so `n' came out an argument the caller had to pass
;; for no reason the type gave.  Keeping a Pi says nothing about the
;; binders behind it, so the walk goes on.
(tl-test-eval tl-ch-a-fixed-binder-behind-an-explicit-one-stays-implicit
  "(: p (-> (x : Nat) (n : Nat) (v : Vec Nat n) (Eq Nat x x)))
   (define (p x v) Refl)
   (p Zero VNil)"
  "Refl" '(:type-check t :elaborate t))

;; The other arity is then refused, which is what makes the first test
;; an arity test and not merely a proof that happens to be accepted.
(tl-test-reject tl-ch-an-explicit-binder-does-not-freeze-the-rest
  "(: p (-> (x : Nat) (n : Nat) (v : Vec Nat n) (Eq Nat x x)))
   (define (p x n v) Refl) p"
  "does not match its signature" '(:type-check t :elaborate t))

;;; The commutativity of addition

;; The first theorem here that a *previous* theorem has to carry.  The
;; step case needs `plus n (Succ m) = Succ (plus n m)' to move the goal
;; off its stuck right-hand side, and the base case needs
;; `plus m Zero = m' -- which is itself an induction, and is `Refl' at
;; no `m'.  `cong', `sym' and `trans' join the two.
(tl-test-eval tl-ch-addition-is-commutative
  (concat tl-ch--cong "
   (: pzr (-> (n : Nat) (Eq Nat (plus n Zero) n)))
   (define (pzr Zero) Refl)
   (define (pzr (Succ n)) (cong Succ (pzr n)))
   (: psa (-> (n : Nat) (m : Nat)
               (Eq Nat (plus n (Succ m)) (Succ (plus n m)))))
   (define (psa Zero m) Refl)
   (define (psa (Succ n) m) (cong Succ (psa n m)))
   (: com (-> (n : Nat) (m : Nat) (Eq Nat (plus n m) (plus m n))))
   (define (com Zero m) (sym (pzr m)))
   (define (com (Succ n) m)
     (trans (cong Succ (com n m)) (sym (psa m n))))
   (com Zero Zero)")
  "Refl" '(:type-check t :elaborate t))

;;; Holes: the program asks, the REPL answers

(defun tl-ch--goals (src)
  "Return the goal lines SRC leaves, or nil when it leaves none.
A form with holes signals `termlisp-hole' before it is run, so this is
how a test asks what the checker would have said."
  (let ((env (tl-ch--typed-env)))
    (condition-case e
        (progn (termlisp-eval src env) nil)
      (termlisp-hole (cadr e)))))

(ert-deftest tl-ch-a-hole-in-a-number-slot-is-a-number ()
  "The context decides what a hole must be, and the goal says so.
`(+ 1 _)' is the simplest term in which a hole's type is not its own
business: it is whatever the surrounding term demanded."
  (should (equal (tl-ch--goals "(+ 1 _)") '("hole 1 : Int"))))

(ert-deftest tl-ch-two-holes-are-two-goals ()
  "Each hole is reported separately, in the order they were written."
  (should (equal (tl-ch--goals "(+ _ _)") '("hole 1 : Int" "hole 2 : Int"))))

(ert-deftest tl-ch-an-unconstrained-hole-stays-open ()
  "A hole nothing pins is reported as an open variable, not as a type.
The element of `(VCons _ VNil)' is whatever the caller's vector says,
and the goal must not pretend otherwise."
  (should (equal (tl-ch--goals "(VCons _ VNil)") '("hole 1 : t1"))))

(ert-deftest tl-ch-a-hole-inside-a-definition-is-still-a-goal ()
  "Holes are collected wherever they appear, not only at the top level."
  (should (equal (tl-ch--goals "(define (f x) (+ x _)) f") '("hole 1 : Int"))))

(ert-deftest tl-ch-a-hole-is-never-run ()
  "A form with holes must not be evaluated.
There is no value in the positions the program declined to fill, and
running it would answer `got _' about a variable that was never meant
to have one."
  (should-error (termlisp-eval "(+ 1 _)" (tl-ch--typed-env))
                :type 'termlisp-hole))

(ert-deftest tl-ch-a-hole-does-not-hide-a-real-error ()
  "Goals are reported only when inference itself succeeded."
  (should-error (termlisp-eval "(+ 1 \"s\")" (tl-ch--typed-env))
                :type 'termlisp-type-error))

(ert-deftest tl-ch-goals-are-not-type-errors ()
  "A caller handling type errors must not find a goal arriving inside it.
A hole is a question, not a mistake."
  (should-error (termlisp-eval "(+ 1 _)" (tl-ch--typed-env))
                :type 'termlisp-hole)
  (let ((env (tl-ch--typed-env)))
    (should-not (condition-case e
                    (progn (termlisp-eval "(+ 1 _)" env) nil)
                  (termlisp-type-error t)
                  (termlisp-hole nil)))))

(ert-deftest tl-ch-a-pattern-wildcard-is-not-a-hole ()
  "`_' in a pattern has always meant \"match anything, bind nothing\".
Opening term position up to holes must not disturb it: the wildcard
still matches, still binds nothing, and leaves no goal behind."
  (should (equal (tl-test--render "(define (f _ x) x) (f 1 2)"
                                  '(:type-check t :elaborate t))
                 "2"))
  (should-not (tl-ch--goals "(define (f _ x) x) (f 1 2)")))

;;; An unknown name is an error, a forward reference is not

;; Inference used to give every unresolved symbol a fresh variable.  An
;; unbound head constrains nothing, so `(nosuch 1)' typechecked and then
;; evaluated to a stuck form -- and so did every argument mismatch
;; downstream of it.  What keeps `(state-ap)' in the prelude working is
;; not that leniency but its scope: the allowance now belongs to names
;; some later form in the same unit really does declare.

(tl-test-reject tl-ch-an-unknown-head-is-rejected "(nosuch 1)"
                "Unknown symbol: nosuch" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-an-unknown-bare-name-is-rejected "nosuch"
                "Unknown symbol: nosuch" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-an-unknown-inside-a-lambda-is-rejected
                "(lambda (x) (nosuch x))"
                "Unknown symbol: nosuch" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-an-unknown-argument-is-rejected "(+ nosuch 1)"
                "Unknown symbol: nosuch" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-a-forward-reference-in-one-input-works
              "(define (f x) (g x)) (define (g x) (+ x 1)) (f 41)"
              "42" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-a-forward-referenced-datatype-works
              "(define (mk x) (Leaf x)) (datatype Tree (Leaf Int)) (mk 1)"
              "(Leaf 1)" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-one-form-cannot-forward-reference
                "(define (f x) (g x))"
                "Unknown symbol: g" '(:type-check t :elaborate t))

;; A datatype name in term position still denotes itself -- that is what
;; the README's `(f Void)' relies on -- but now with its own type
;; rather than an unconstrained one, so it is checked where it is used.
(tl-test-eval tl-ch-a-type-name-as-a-witness-checks
              "(: f (Void -> Int)) (define (f x) 1) (f Void)"
              "1" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-a-type-name-cannot-stand-for-any-type "(car Bool)"
                "Cannot apply" '(:type-check t :elaborate t))

;; The batch driver and the evaluator must agree about what a signature
;; means.  This one used to reject every definition whose result index
;; was a computed one, because it never told the unifier what to reduce
;; a type-level function against -- `termlisp-eval-form' has always done
;; so, and `append' is written in exactly that style.
(ert-deftest tl-ch-batch-driver-reduces-a-computed-index ()
  "`termlisp-typecheck-def' checks `append' the way `termlisp-eval' does."
  (let ((env (termlisp-load-prelude
              (termlisp-make-env '(:type-check t :elaborate t)))))
    (termlisp-typecheck-def
     env
     "(: appd (-> (n m : Nat) (Vec a n) (Vec a m) (Vec a (plus n m))))
      (define (appd VNil ys) ys)
      (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))")
    (should (gethash 'appd (tl-env-type-env env)))))

(ert-deftest tl-ch-batch-driver-still-rejects-a-wrong-index ()
  "Enabling reduction has not made the batch driver merely permissive."
  (let ((env (termlisp-load-prelude
              (termlisp-make-env '(:type-check t :elaborate t)))))
    (should-error
     (termlisp-typecheck-def
      env
      "(: appd (-> (n m : Nat) (Vec a n) (Vec a m) (Vec Int Zero)))
       (define (appd VNil ys) ys)
       (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))")
     :type 'termlisp-type-error)))

;;; Propositional equality

;; `Eq a x y' is inhabited exactly when `x' and `y' are the same value of
;; type `a'.  No eliminator is needed to earn that: `Refl' returns at
;; `x' twice, so unifying its result with `Eq a x y' binds `x' once and
;; then insists the two occurrences agree.

(tl-test-eval tl-ch-eq-refl-inhabits-the-reflexive-index
              "(: r (Eq Nat Zero Zero -> Int)) (define (r p) 1) (r Refl)"
              "1" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-eq-refl-does-not-inhabit-a-mismatch
                "(: r (Eq Nat Zero (Succ Zero) -> Int)) (define (r p) 1) (r Refl)"
                "Cannot apply" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-eq-checks-the-element-type
                "(: r (Eq Nat Int Zero -> Int)) (define (r p) 1) (r Refl)"
                "Cannot apply" '(:type-check t :elaborate t))

;; The index need not be written in canonical form: what matters is that
;; both sides reduce to the same value.
(tl-test-eval tl-ch-eq-agrees-after-reduction
              "(: r (Eq Nat (plus Zero Zero) Zero -> Int)) (define (r p) 1) (r Refl)"
              "1" '(:type-check t :elaborate t))

;; One declaration serves every element type, because nothing in it
;; constrains which.
(tl-test-eval tl-ch-eq-is-not-confined-to-naturals
              "(: r (Eq Bool True True -> Int)) (define (r p) 1) (r Refl)"
              "1" '(:type-check t :elaborate t))
(tl-test-reject tl-ch-eq-still-sees-a-bool-mismatch
                "(: r (Eq Bool True False -> Int)) (define (r p) 1) (r Refl)"
                "Cannot apply" '(:type-check t :elaborate t))

;; Symmetry and transitivity need no eliminator.  Matching a proof
;; against `Refl' refines the index to the reflexive case, which is
;; exactly when the result type holds, so `sym' is one clause and `trans'
;; two.
(tl-test-eval tl-ch-eq-sym-turns-the-index-around
              "(sym Refl)" "Refl" '(:type-check t :elaborate t))
(tl-test-eval tl-ch-eq-trans-joins-two-proofs
              "(trans Refl Refl)" "Refl" '(:type-check t :elaborate t))

;; Both stay total where nothing is provable.  `Eq Nat Zero (Succ Zero)'
;; admits no proof at all, so a function from one is vacuously correct --
;; which is the point of a proposition being empty rather than merely
;; being rejected at the call.
(tl-test-eval tl-ch-eq-sym-is-total-over-an-empty-proposition
              "(: bad (Eq Nat Zero (Succ Zero) -> Eq Nat (Succ Zero) Zero))
               (define (bad p) (sym p))
               bad"
              "bad" '(:type-check t :elaborate t))

;;; Transport along an equality

;; The briefing predicted that `subst' and `rewrite' would need a
;; universe, because the library signatures quantify over a motive --
;;
;;     subst : (p : a -> *) -> Eq a x y -> p x -> p y
;;
;; -- and a motive is a type of types, so stage 4 would gate on it.
;; That prediction was wrong twice over.  The motive is never
;; quantified over: it is read off the value's own type, so
;; `Vec Nat n -> Vec Nat m' already says everything a motive would have
;; said.  ACL2 does exactly this -- `fertilize-clause1' substitutes one
;; side of an equality for the other through the goal and deletes the
;; hypothesis, with the goal standing in for the motive -- and has no
;; universe either, which `doc.lisp:1888-1896' records as deliberate.
;;
;; And no new machinery is needed: the signature's indices are flexible
;; binders, so unification itself performs the transport.

(tl-test-eval tl-ch-a-vector-moves-between-indices
  "(: cast (-> (n : Nat) (m : Nat) (Eq Nat n m) (Vec Nat n) (Vec Nat m)))
   (define (cast Refl xs) xs)
   (cast Refl (VCons Zero (VCons (Succ Zero) VNil)))"
  "(VCons Zero (VCons (Succ Zero) VNil))" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-a-proof-built-elsewhere-drives-a-transport
  "(: refl-thm (-> (n : Nat) (Eq Nat n n)))
   (define (refl-thm n) Refl)
   (: cast (-> (n : Nat) (m : Nat) (Eq Nat n m) (Vec Nat n) (Vec Nat m)))
   (define (cast Refl xs) xs)
   (cast (refl-thm Zero) VNil)"
  "VNil" '(:type-check t :elaborate t))

;; An implicit binder is not a parameter, and what makes one implicit is
;; that some *later argument* fixes its value: `n' here is pinned by the
;; `Vec Nat n' the caller has to pass anyway, so `tl-signature-binders'
;; drops the Pi and leaves `n' for unification to find -- which is what
;; lets `pinh' take only its proof.  A definition that takes `n' anyway
;; has the wrong arity.  A binder no later argument fixes is the other
;; case, and there the Pi stays: `tl-ch-a-mentioned-but-unfixed-binder-
;; stays-a-parameter' below is the same rule seen from that side.
(tl-test-reject tl-ch-an-implicit-binder-is-not-a-parameter
  "(: pinh (-> (n : Nat) (Vec Nat n) (Eq Nat n n)))
   (define (pinh n h) Refl) pinh"
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-an-implicit-binder-arrives-by-inference
  "(: pinh (-> (n : Nat) (Vec Nat n) (Eq Nat n n)))
   (define (pinh h) Refl) (pinh VNil)"
  "Refl" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-a-mentioned-but-unfixed-binder-stays-a-parameter
  "(: refl-thm (-> (n : Nat) (Eq Nat n n)))
   (define (refl-thm n) Refl) (refl-thm Zero)"
  "Refl" '(:type-check t :elaborate t))

;;; A proof that fails must say where

;; Credibility in stage 3 comes from two things, and only one of them is
;; "a proof can be checked".  The other is that a proof which does not
;; check names the difference.  `Eq Nat Zero (Succ Zero)' and
;; `Eq Nat (Succ Zero) Zero' agree everywhere but one index; printing
;; both types is most of what fixing the proof needs.

(tl-test-reject tl-ch-a-failed-proof-names-both-types
  "(: h (Eq Nat Zero (Succ Zero) -> Eq Nat (Succ Zero) Zero))
   (define (h p) p) h"
  "the signature says" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-an-index-disagreement-is-visible
  "(: f (-> (n : Nat) (Vec Nat (Succ n)) (Vec Nat (Succ n))))
   (define (f n) VNil) f"
  "Vec Nat Zero" '(:type-check t :elaborate t))

;; A variable name has to survive the trip.  `format' with `%S' would
;; write the symbol `?3' as `\?3', because a bare one reads back as a
;; character constant -- correct for source, noise for a message.
(tl-test-reject tl-ch-a-mismatch-note-keeps-names-readable
  "(: h (Eq Nat Zero (Succ Zero) -> Eq Nat (Succ Zero) Zero))
   (define (h p) p) h"
  "(Eq Nat Zero (Succ Zero))" '(:type-check t :elaborate t))

;;; The proof path is strict

;; Oracle mode tolerates a failed unification and clauses that share no
;; common type.  A proof may tolerate neither: both turn a mistake into
;; an unconstrained variable rather than an error, which is the one
;; failure a Curry-Howard system must not have.  Nothing on the typed
;; path sets those flags today -- the only binder is `tl-typecheck-ir',
;; which no evaluator, loader or REPL entry point reaches -- but a
;; guarantee resting on nobody happening to set a variable is not a
;; guarantee, so `tl-typecheck-form' now binds them off.

(defvar tl-ch--seen-flags nil
  "Oracle flags observed by `tl-ch--record-flags'.")

(defun tl-ch--record-flags (orig &rest args)
  "Advice: record the oracle flags ORIG runs under, then run it with ARGS."
  (push (cons tl-type-lenient tl-type-lenient-clauses) tl-ch--seen-flags)
  (apply orig args))

(ert-deftest tl-ch-the-typed-path-binds-the-oracle-flags-off ()
  "Checking a form binds oracle tolerance off, not merely finds it off.
`tl-typecheck-form' is what every top-level form on the typed path goes
through, so that is where the binding has to live."
  (let ((env (termlisp-make-env '(:type-check t :elaborate t))))
    (setq tl-ch--seen-flags nil)
    (advice-add 'tl-infer-define-clauses :around #'tl-ch--record-flags)
    (unwind-protect
        (termlisp-eval "(define (probe x) x)" env)
      (advice-remove 'tl-infer-define-clauses #'tl-ch--record-flags))
    (should (equal tl-ch--seen-flags '((nil . nil))))))

(tl-test-reject tl-ch-the-oracle-does-not-soften-a-proof
  "(: o (-> Nat Nat)) (define (o Zero) Zero) (define (o (Succ x)) \"s\") o"
  "does not match its signature" '(:type-check t :elaborate t))

;;; A universally quantified index is not the body's to choose

;; The indices the signature quantifies over are the caller's, not the
;; body's: `Eq Nat x y' with both free is a claim about *every* pair, and
;; `Refl' cannot prove it.  Until now it could, because a case-(c) Pi
;; binder was collected by `tl-free-tvars', quantified by
;; `tl-register-signature', and then re-created *flexible* by
;; `tl-instantiate-scheme' -- losing the rigidity it had.  `Refl' bound
;; both sides to the same term, `Bool' inhabited `Void', and the answer
;; had become `t' rather than a check.
;;
;; A clause's own keepers are now skolems, so the same three shapes are
;; refused.  What `sym', `trans' and `cong' rely on is preserved, because
;; only a binder *nothing else fixes* is skolemised -- and the false
;; theorems all have that shape.

(tl-test-reject tl-ch-a-universal-index-cannot-be-invented
  "(: f (-> (x : Nat) (y : Nat) (Eq Nat x y)))
   (define (f x y) Refl) f"
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-an-index-mentioned-once-cannot-be-invented
  "(: h (-> (x : Nat) (Eq Nat Zero x)))
   (define (h x) Refl) h"
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-an-index-that-occurs-in-the-goal-cannot-be-invented
  "(: g (-> (x : Nat) (Eq Nat x (Succ x))))
   (define (g x) Refl) g"
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-an-invented-index-is-rejected-through-a-lambda
  "(: f (-> (x : Nat) (y : Nat) (Eq Nat x y)))
   (define (f x) (lambda (y) Refl)) f"
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-an-invented-index-cannot-be-used-at-a-type-parameter
  "(: k (-> (a : *) (x : a) (y : a) (Eq a x y)))
   (define (k a x y) Refl) k"
  "does not match its signature" '(:type-check t :elaborate t))

;; The reflexive claim stays provable, and so does the one that is true
;; only *because* the hypothesis ties the two indices together -- the
;; distinction the whole change rests on.

(tl-test-eval tl-ch-the-reflexive-case-is-still-provable
  "(: w (-> (x : Nat) (Eq Nat x x)))
   (define (w x) Refl) (w Zero)"
  "Refl" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-an-index-tied-by-the-hypothesis-is-still-provable
  "(: b (-> (a : *) (x : a) (y : a) (Eq a x y) (Eq a y x)))
   (define (b h) Refl) (b Refl)"
  "Refl" '(:type-check t :elaborate t))

;;; Datatype kinds

;; A constructor's field and its result are kind-checked where the
;; declaration is written, so a malformed one is an error there rather
;; than at the first use, much later.  What stays lenient is a head that
;; does not exist yet -- a datatype this one is mutually recursive with,
;; or one an oracle has not declared -- because that head takes a fresh
;; kind variable, which unifies with anything.

(ert-deftest tl-kind-a-result-takes-the-datatype-s-own-arity ()
  "`(Bad a a)' applies a one-parameter datatype to two arguments."
  (should-error (termlisp-eval "(datatype (Bad a) (Mk : (Bad a a)))"
                               (termlisp-make-env))
                :type 'termlisp-type-error))

(ert-deftest tl-kind-a-parameterless-type-cannot-be-applied ()
  "`Int' has no parameters, so `(Bad a Int Int)' over-applies it."
  (should-error
   (termlisp-eval "(datatype Nat (Zero) (Succ Nat))
                   (datatype (Bad a) (Mk a : (Bad a Int Int)))"
                  (termlisp-make-env))
   :type 'termlisp-type-error))

(ert-deftest tl-kind-mutually-recursive-declarations-are-accepted ()
  "`Odd' has no kind yet when `Even' is read, and must not need one."
  (let ((env (termlisp-make-env)))
    (termlisp-eval
     "(datatype (Even n) (EZ : (Even Zero)) (ES (Odd n) : (Even (Succ n))))
      (datatype (Odd n) (OS (Even n) : (Odd (Succ n))))"
     env)
    (should (tl-kind-of env 'Even))
    (should (tl-kind-of env 'Odd))))

(ert-deftest tl-kind-an-undeclared-head-is-left-unchecked ()
  "An oracle datatype may mention a head nothing has declared."
  (should (termlisp-eval "(datatype (Oracle a) (Mk : (NothingDeclared a)))"
                         (termlisp-make-env))))

(ert-deftest tl-kind-a-name-shared-with-its-constructor-still-kinds ()
  "A datatype and its constructor may share a name, and kind apart.
In `(Pair a b)' the name `Pair' is both, and in a result type it means
the datatype -- which takes `*' where the lifted constructor takes the
datatype's own universe, so the two must not be read as one kind."
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype (Pair a b) (Mk a b))" env)
    (tl-kind-check env (tl-type-parse '(Pair Int String)))
    (termlisp-eval "(datatype (Self a) (Self : (Self a)))" env)
    (should (tl-kind-of env 'Self))))

;;; Exhaustiveness and redundancy (G7)

;; Coverage checking is opt-in: `head', `tail' and `if' in the bundled
;; prelude are partial on purpose, so the default environment must leave
;; them -- and anything else written that way -- alone.
(defconst tl-ch-cov-opts '(:type-check t :elaborate t :coverage t)
  "Options that switch coverage checking on for a test.")

(tl-test-covers tl-ch-cov-exhaustive-bool
                "(define (f True) 1) (define (f False) 2) f"
                tl-ch-cov-opts)

(tl-test-coverage-reject tl-ch-cov-missing-constructor-names-itself
                         "(define (f True) 1) f"
                         "no case for False" tl-ch-cov-opts)

(tl-test-covers tl-ch-cov-a-wildcard-always-covers
                "(define (f x) 1) f" tl-ch-cov-opts)

(tl-test-coverage-reject tl-ch-cov-redundant-clause
                         "(define (f True) 1) (define (f x) 2) (define (f False) 3) f"
                         "clause 3 is unreachable" tl-ch-cov-opts)

;; An `or' matches the union of its alternatives, so a row carrying one
;; stands for one row per alternative rather than for none of them.
(tl-test-covers tl-ch-cov-or-pattern-covers-the-union
                "(define (f (or True False)) 1) f" tl-ch-cov-opts)
(tl-test-coverage-reject tl-ch-cov-or-pattern-still-leaves-a-gap
                         "(define (f (or True False)) 1) (define (f x) 2) f"
                         "unreachable" tl-ch-cov-opts)

;; The witness must name what is actually missing, at the depth it is
;; missing at: a one-element list, not merely "some Cons".
(tl-test-covers tl-ch-cov-nested-list-is-exhaustive
                "(define (f Nil) 1) (define (f (Cons x Nil)) 2) (define (f (Cons x (Cons y zs))) 3) f"
                tl-ch-cov-opts)
(tl-test-coverage-reject tl-ch-cov-nested-list-witness-names-the-depth
                         "(define (f Nil) 1) (define (f (Cons x (Cons y zs))) 3) f"
                         "(Cons _ Nil)" tl-ch-cov-opts)

;; A guard is a runtime predicate the checker cannot evaluate, so it
;; contributes nothing to coverage -- and the report says so, because the
;; guarded row might well have closed the gap.
(tl-test-coverage-reject tl-ch-cov-a-guard-is-never-credited
                         "(define (f (guard x True)) 1) f"
                         "coverage undecidable here" tl-ch-cov-opts)

;; Literals are never enumerable as a type, so an all-literal column can
;; never be shown complete even over the integers it happens to list.
(tl-test-coverage-reject tl-ch-cov-a-literal-column-is-never-coverable
                         "(define (f (:literal 1)) 1) f"
                         "no case for _" tl-ch-cov-opts)
(tl-test-covers tl-ch-cov-a-literal-with-a-wildcard-covers
                "(define (f (:literal 1)) 1) (define (f x) 2) f"
                tl-ch-cov-opts)

;; Several parameters are several columns, and a witness names one per.
(tl-test-covers tl-ch-cov-two-parameters
                "(define (f True False) 1) (define (f True x) 2) (define (f x y) 3) f"
                tl-ch-cov-opts)
(tl-test-coverage-reject tl-ch-cov-two-parameters-leave-one-open
                         "(define (f True False) 1) (define (f True x) 2) f"
                         "no case for False _" tl-ch-cov-opts)

;; Off by default, so a partial function is not an error just because
;; the checker exists -- it still runs.
(tl-test-eval tl-ch-cov-off-leaves-a-partial-function-alone
              "(define (f True) 1) (f True)"
              "1" '(:type-check t :elaborate t))

;; An indexed family is covered only as far as its index allows: at
;; `Succ k' only `VCons' can reach the value, so one clause is enough,
;; while an unknown index admits `VNil' too and the same clause is a gap.
(tl-test-covers tl-ch-cov-gadt-append-is-exhaustive
                "(: appd (-> (n m : Nat) (Vec a n) (Vec a m) (Vec a (plus n m))))
                 (define (appd VNil ys) ys)
                 (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))
                 appd"
                tl-ch-cov-opts)
(tl-test-coverage-reject tl-ch-cov-gadt-append-missing-nil
                         "(: appd (-> (n m : Nat) (Vec a n) (Vec a m) (Vec a (plus n m))))
                          (define (appd (VCons x xs) ys) (VCons x (appd xs ys)))
                          appd"
                         "no case for VNil" tl-ch-cov-opts)
(tl-test-covers tl-ch-cov-gadt-a-concrete-index-narrows-the-set
                "(: vhd (-> (k : Nat) (Vec Int (Succ k)) Int))
                 (define (vhd (VCons x xs)) x)
                 vhd"
                tl-ch-cov-opts)
(tl-test-coverage-reject tl-ch-cov-gadt-an-unknown-index-admits-more
                         "(: vhd (-> (n : Nat) (Vec Int n) Int))
                          (define (vhd (VCons x xs)) x)
                          vhd"
                         "no case for VNil" tl-ch-cov-opts)
(tl-test-coverage-reject tl-ch-cov-gadt-redundant-clause
                         "(: vhd (-> (k : Nat) (Vec Int (Succ k)) Int))
                          (define (vhd (VCons x xs)) x)
                          (define (vhd (VCons x xs)) x)
                          vhd"
                         "clause 2 is unreachable" tl-ch-cov-opts)

;; One REPL submission is one coverage batch, so a report arrives at the
;; end of the submission that wrote the clauses -- not partway through a
;; function whose remaining clauses have not been typed yet.
(ert-deftest tl-ch-cov-repl-reports-per-submission ()
  "The gap is reported at the end of the submission that wrote the clauses."
  (let ((termlisp-repl--env
         (termlisp-load-prelude
          (termlisp-make-env '(:type-check t :elaborate t :coverage t)))))
    (should (string-match-p
             "no case for False"
             (termlisp-repl--error-message
              (should-error (termlisp-repl--eval-string "(define (f True) 1) f")
                            :type 'termlisp-type-error))))
    ;; The next submission starts from an empty queue.
    (should (equal (termlisp-repl--eval-string
                    "(define (g True) 1) (define (g False) 2) (g True)")
                   "1"))))

(ert-deftest tl-ch-cov-repl-drops-a-failed-submission ()
  "A submission that fails partway reports nothing, here or later.
The first form announced a clause and the second failed.  Were the
announcement to survive, the next submission would report a function the
user is not working on, and would report it while it is still half
written."
  (let ((termlisp-repl--env
         (termlisp-load-prelude
          (termlisp-make-env '(:type-check t :elaborate t :coverage t)))))
    (should (string-match-p
             "Unknown symbol"
             (termlisp-repl--error-message
              (should-error
               (termlisp-repl--eval-string "(define (h True) 1) (define (h True) nope)")
               :type 'termlisp-type-error))))
    (should (equal (termlisp-repl--eval-string
                    "(define (g True) 1) (define (g False) 2) (g True)")
                   "1"))))

;;; `tl-apply-pi': what fills a `Pi' binder at a call site
;;
;; A `Pi' codomain's occurrences of its binder stand for the argument's
;; *value*.  This suite covers every shape that value can arrive in, and
;; every shape the codomain can hold the binder in, because the old code
;; put a fresh variable there and let unification rediscover the answer --
;; which worked exactly when something else happened to name the function
;; and failed silently when nothing did.

(defconst tl-ch--apply-pi-cong
  "(: cong (-> (a : *) (b : *) (x : a) (y : a) (f : a -> b)
                (Eq a x y) (Eq b (f x) (f y))))
   (define (cong f Refl) Refl)"
  "A congruence rule whose codomain mentions its function binder twice.
The two occurrences are what make this the probe for `tl-apply-pi': each
has to become the argument's value, not one fresh variable left to chance.")

(tl-test-eval tl-ch-apply-pi-fills-a-named-function
  (concat tl-ch--apply-pi-cong "
   (: zc (-> (n : Nat) (Vec Nat n) (Vec Nat (Succ n))))
   (define (zc xs) (VCons Zero xs))
   (: t (-> (n : Nat) (xs : Vec Nat n) (ys : Vec Nat n)
             (Eq (Vec Nat n) xs ys)
             (Eq (Vec Nat (Succ n)) (zc xs) (zc ys))))
   (define (t h) (cong zc h)) (t Refl)")
  "Refl" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-apply-pi-fills-a-partial-constructor
  (concat tl-ch--apply-pi-cong "
   (: t (-> (n : Nat) (xs : Vec Nat n) (ys : Vec Nat n)
             (Eq (Vec Nat n) xs ys)
             (Eq (Vec Nat (Succ n)) (VCons Zero xs) (VCons Zero ys))))
   (define (t h) (cong (VCons Zero) h)) (t Refl)")
  "Refl" '(:type-check t :elaborate t))

;; Two leading Pis, each filled by a different value, each mentioned
;; twice.  `Succ' fills the first as a bare name and `dblf' as a head
;; applied to one argument, so the codomain's two spines come out as
;; `(Succ Zero)' and `(dblf Zero)' -- the second only agrees with its
;; signature if the substituted head was spliced into the applications
;; around it rather than dropped into the head slot as a node the
;; reducer could not name.
(tl-test-eval tl-ch-apply-pi-fills-two-nested-pis-differently
  "(: bothf (-> (f : Nat -> Nat) (g : Nat -> Nat) Nat
                 (Pair (Eq Nat (f Zero) (f Zero)) (Eq Nat (g Zero) (g Zero)))))
   (define (bothf f g k) (Pair Refl Refl))
   (: dblf (-> (n : Nat) Nat))
   (define (dblf n) (Succ (Succ n)))
   (car (bothf Succ dblf Zero))"
  "Refl" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-apply-pi-leaves-a-lambda-to-unification
  (concat tl-ch--apply-pi-cong "
   (: t (-> (n : Nat) (Eq Nat n n) (Eq Nat n n)))
   (define (t h) (cong (lambda (v) (Succ v)) h)) (t Refl)")
  "Refl" '(:type-check t :elaborate t))

;; The signature says the lambda twice where the clause says one variable.
;; The two spellings are separate lists, so a head compared with `eq'
;; calls them different terms and the clause is refused for agreeing with
;; its own statement.
(tl-test-eval tl-ch-apply-pi-agrees-when-the-signature-spells-the-same-lambda
  (concat tl-ch--apply-pi-cong "
   (: t (-> (x : Nat) (y : Nat) (Eq Nat x y)
             (Eq Nat ((lambda (v) (Succ v)) x) ((lambda (v) (Succ v)) y))))
   (define (t h) (cong (lambda (v) (Succ v)) h)) (t Refl)")
  "Refl" '(:type-check t :elaborate t))

;; The argument names a global through a local, so only part of it
;; converts.  The head is known and converts; the local has no type-level
;; spelling and becomes a variable, which is the degradation to the
;; behaviour every argument had before -- and the theorem still goes
;; through, because what the codomain needs is the head.
(tl-test-eval tl-ch-apply-pi-converts-a-global-applied-to-a-local
  (concat tl-ch--apply-pi-cong "
   (: t (-> (k : Nat) (x : Nat) (y : Nat) (Eq Nat x y)
             (Eq Nat (plus k x) (plus k y))))
   (define (t k h) (cong (plus k) h)) (t Zero Refl)")
  "Refl" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-apply-pi-still-refuses-the-wrong-function
  (concat tl-ch--apply-pi-cong "
   (: zc (-> (n : Nat) (Vec Nat n) (Vec Nat (Succ n))))
   (define (zc xs) (VCons Zero xs))
   (: t (-> (n : Nat) (xs : Vec Nat n) (ys : Vec Nat n)
             (Eq (Vec Nat n) xs ys)
             (Eq (Vec Nat (Succ n)) (zc xs) (zc ys))))
   (define (t h) (cong (lambda (v) v) h)) (t Refl)")
  "does not match its signature" '(:type-check t :elaborate t))

(tl-test-reject tl-ch-apply-pi-still-refuses-the-wrong-argument
  (concat tl-ch--apply-pi-cong "
   (: t (-> (x : Nat) (y : Nat) (Eq Nat x y) (Eq Nat x y)))
   (define (t h) (cong VNil h)) (t Refl)")
  "Cannot apply cong to VNil" '(:type-check t :elaborate t))

;;; `let': where a binding stops being monomorphic
;;
;; A `let' used to be rewritten into an inline-lambda application before
;; inference, and a lambda application instantiates its argument at one
;; type -- so every binding was monomorphic and an identity could not be
;; used twice.  The bindings now reach `tl-infer-ir-Let', which is where
;; the capitalised `Let' of the lowering IR has always been quantified.

(tl-test-eval tl-ch-let-quantifies-a-binding-introduced-inside-it
  "(define (use n) (let ((f (lambda (x) x))) (Pair (f 1) (f \"s\")))) (car (use 0))"
  "1" '(:type-check t :elaborate t))

;; The elaborator used to rewrite `let' into the very lambda application
;; that closed the question, so a program could be polymorphic under
;; `:type-check' and monomorphic under `:elaborate'.  It leaves `let'
;; alone now, and the same source means the same thing either way.
(tl-test-eval tl-ch-let-quantifies-under-elaboration
  "(define (use n) (let ((f (lambda (x) x))) (Pair (f 1) (f \"s\")))) (cdr (use 0))"
  "s" '(:type-check t :elaborate t))

(tl-test-eval tl-ch-let-inner-binding-sees-the-outer-one
  "(define (use n) (let ((f (lambda (y) y))) (let ((g (lambda (x) (f x)))) (g \"s\")))) (use 0)"
  "s" '(:type-check t :elaborate t))

(ert-deftest tl-ch-let-says-what-the-ir-let-always-said ()
  "Surface `let' and capitalised `Let' are one rule, not two.
The only test that a binding is quantified at all is that its scheme
looks the same whichever spelling introduced it -- and the surrounding
argument, bound to a type the caller fixed, stays put, which is what
keeps generalization from reaching outside its own scope."
  (should (equal (tl-test--scheme-datum
                  "(define (k x) (let ((id (lambda (v) v))) (let ((u (id 1))) (id \"s\"))))"
                  'k)
                 '(-> %1 String))))

(tl-test-eval tl-ch-let-a-lambda-is-a-value-even-when-its-body-is-not
  "(define (use n) (let ((mk (lambda (z) (Pair z z)))) (car (mk \"s\")))) (use 0)"
  "s" '(:type-check t :elaborate t))

;; The value restriction: an application has already run, so its type
;; may still be pinned by whatever else used it.  `idl' applied to one
;; argument is not a value, `g' is not generalized, and the second use
;; cannot pick a type the first one did not.
(tl-test-reject tl-ch-let-keeps-an-application-monomorphic
  "(: idl (-> (a : *) (f : a -> a) (b : a) a))
   (define (idl f x) (f x))
   (define (use n) (let ((g (idl (lambda (v) v)))) (Pair (g 1) (g \"s\"))))"
  "Cannot apply g to" '(:type-check t :elaborate t))

;; The hole generalizing levels were built to close.  `y' was created
;; before this scope opened, so its variable is not the binding's to
;; quantify over, and `z' cannot be used at two types.
(tl-test-reject tl-ch-let-does-not-let-a-parameter-escape
  "(define (h y) (let ((z y)) (seq (z 1) (z \"s\"))))"
  "Cannot apply z to" '(:type-check t :elaborate t))

;; One value read at as many types as it was instantiated at cannot have
;; its value swapped under all of them at once.
(tl-test-reject tl-ch-let-refuses-to-reassign-a-polymorphic-binding
  "(define (bad y) (let ((f (lambda (x) x))) (seq (Setq f (lambda (x) \"s\")) (f 1))))"
  "bound polymorphically" '(:type-check t :elaborate t))

(ert-deftest tl-ch-let-leaves-an-accumulator-reassignable ()
  "`While' and `Setq' are not the value restriction's business.
An accumulator is bound to a literal, so there is nothing to quantify
and nothing to retain; were it wrapped in a closed scheme the
reassignment below would be refused as polymorphism, and every loop
that carries its sum in a `let' would stop compiling.  The assertion is
the absence of a signal, since `termlisp-typecheck-def' reports by
signaling and returns nothing to look at -- and `While' is a form of the
lowering IR, so it can be checked but not run."
  (let ((env (termlisp-load-prelude
              (termlisp-make-env '(:type-check t :elaborate t)))))
    (should (progn
              (termlisp-typecheck-def
               env
               "(define (accf n)
                  (let ((i 1) (acc 0))
                    (While (<= i n) (Setq acc (+ acc i)) (Setq i (+ i 1)))
                    acc))")
              t))))

;; Each binding expression is read in the enclosing scope, so a later one
;; cannot name an earlier -- the rewrite into a lambda application used
;; to mask this by binding both names at once.
(tl-test-reject tl-ch-let-is-simultaneous
  "(let ((a Zero) (b a)) b)"
  "Unknown symbol" '(:type-check t :elaborate t))

(provide 'curry-howard-test)
;;; curry-howard-test.el ends here
