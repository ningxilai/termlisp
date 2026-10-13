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
    (should (equal (tl-ch--kind-string env 'Fin) "(Nat -> *)"))
    (should (equal (tl-ch--kind-string env 'Eq) "(* -> *)"))))

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
(tl-test-eval tl-ch-refl-at-a-type
  "(: r (Eq Int)) (define r (Refl)) r" "Refl" '(:type-check t :elaborate t))

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

(provide 'curry-howard-test)
;;; curry-howard-test.el ends here
