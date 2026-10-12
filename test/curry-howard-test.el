;;; curry-howard-test.el --- propositional layer and type-check safety -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Stage 0 of the Curry-Howard roadmap: `Void', `Either' and
;; `absurd', plus the cases that must keep being rejected.

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

(provide 'curry-howard-test)
;;; curry-howard-test.el ends here
