;;; nbe-test.el --- type-layer reduction over the term graph -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Stage 2(c): the type-layer reducer.  Types may now contain terms --
;; `Vec a (plus n m)' -- so two of them are equal only if what they index
;; by reduces to the same thing.  These cases pin the three properties the
;; reducer has to have: it reduces beta and user clauses, it stops rather
;; than failing when a term is not yet known, and it compares normal forms
;; without caring what the unknowns are called.

;;; Code:

(require 'test-support)
(require 'termlisp-nbe)

(defun tl-nbe-test--env ()
  "Return a fresh prelude reduction environment."
  (tl-nbe (termlisp-load-prelude
           (termlisp-make-env '(:type-check t :elaborate t)))
          nil))

(defun tl-nbe-test--whnf (sexp)
  "Parse type SEXP and reduce it to weak head normal form, rendered."
  (tl-test--alpha (tl-type-to-datum
                   (tl-nbe-whnf (tl-type-parse sexp) (tl-nbe-test--env)))))

(defun tl-nbe-test--nf (sexp)
  "Parse type SEXP and reduce it to normal form, rendered."
  (tl-test--alpha (tl-type-to-datum
                   (tl-nbe-nf (tl-type-parse sexp) (tl-nbe-test--env)))))

;;; Beta

(ert-deftest tl-nbe-beta-substitutes-the-argument ()
  "Applying a type-level lambda must put the argument in the body."
  (let* ((nbe (tl-nbe-test--env))
         (lam (tl-type-parse '(lambda (n) (Vec a n))))
         (app (tl-type-parse '(f Zero))))
    (should (equal (tl-test--alpha
                    (tl-type-to-datum
                     (tl-nbe-whnf app (tl-nbe-extend nbe 'f lam))))
                   '(Vec %1 Zero)))))

;;; Unfolding user clauses

(ert-deftest tl-nbe-unfolds-a-matching-clause ()
  "`plus' is defined by clauses in the prelude; its first clause matches here."
  (should (equal (tl-nbe-test--whnf '(plus Zero n)) '%1)))

(ert-deftest tl-nbe-whnf-stops-at-the-outer-constructor ()
  "Weak head normal form is *weak*: it does not reduce underneath."
  (should (equal (tl-nbe-test--whnf '(plus (Succ Zero) (Succ Zero)))
                 '(Succ (plus Zero (Succ Zero))))))

(ert-deftest tl-nbe-nf-reduces-underneath-constructors ()
  "Normal form reduces everywhere, which is what makes indices comparable."
  (should (equal (tl-nbe-test--nf '(plus (Succ Zero) (Succ Zero)))
                 '(Succ (Succ Zero)))))

(ert-deftest tl-nbe-unfolding-is-recursive ()
  "The second clause of `plus' calls `plus' again; that must keep going."
  (should (equal (tl-nbe-test--nf '(plus (Succ Zero) (Succ (Succ Zero))))
                 '(Succ (Succ (Succ Zero))))))

;;; Stuck is normal

(ert-deftest tl-nbe-an-unknown-argument-leaves-the-term-stuck ()
  "`plus n m' with `n' unknown cannot take a step, and must not fail.
This is exactly what `append''s index looks like before it is called."
  (should (equal (tl-nbe-test--whnf '(plus n m))
                 (tl-test--alpha (tl-type-to-datum
                                  (tl-type-parse '(plus n m)))))))

;;; Reduction inside types

(ert-deftest tl-nbe-reduces-an-index-inside-a-type ()
  "A reducible index makes `Vec a (plus Zero n)' and `Vec a n' one type."
  (should (equal (tl-nbe-test--nf '(Vec a (plus Zero n)))
                 (tl-nbe-test--nf '(Vec a n)))))

(ert-deftest tl-nbe-leaves-a-pi-structure-intact ()
  "Normalising a `Pi' must not disturb its binder or its domain."
  (should (equal (tl-nbe-test--nf '((n : Nat) -> (Vec a n)))
                 '((n : Nat) -> (Vec %1 n)))))

(ert-deftest tl-nbe-normalising-a-type-leaves-the-type-it-came-from ()
  "Normal form is computed copy-on-write: the type NODE was taken from stays.
A type node is shared by every type that mentions it, so rewriting it in
place would edit a signature as a side effect of comparing two other types."
  (let* ((nbe (tl-nbe-test--env))
         (node (tl-type-parse '(Vec a (plus (Succ Zero) Zero))))
         (before (tl-node->sexp node)))
    ;; Normalising reduces the term...
    (should (equal (tl-test--alpha (tl-type-to-datum (tl-nbe-nf node nbe)))
                   '(Vec %1 (Succ Zero))))
    ;; ...and the walk never edited what it was handed.
    (should (equal (tl-node->sexp node) before))))

;;; Bounded

(ert-deftest tl-nbe-a-definition-that-never-stops-is-a-type-error ()
  "A type-level function that calls itself forever is reported, not waited for.
Nothing bounded reduction before it ran on the term graph, so a mistaken
definition would have hung the session; now the budget runs out and the
failure says what it is -- a type error, not an evaluation error."
  (let* ((env (termlisp-load-prelude
               (termlisp-make-env '(:type-check t :elaborate t))))
         (nbe (tl-nbe env nil))
         (tl-nbe-fuel 40))
    (puthash 'spin
             (list (tl-make-clause 'spin (list (tl-pattern-parse 'x))
                                   '(spin x)))
             (tl-env-functions env))
    (should-error (tl-nbe-whnf (tl-type-parse '(spin Zero)) nbe)
                  :type 'termlisp-type-error)
    (should-error (tl-nbe-nf (tl-type-parse '(spin Zero)) nbe)
                  :type 'termlisp-type-error)))

;;; Definitional equality

(ert-deftest tl-nbe-equal-agrees-with-reduction ()
  (let ((nbe (tl-nbe-test--env)))
    (should (tl-nbe-equal (tl-type-parse '(plus Zero n))
                          (tl-type-parse 'n) nbe))
    (should (tl-nbe-equal (tl-type-parse '(Vec a (plus Zero n)))
                          (tl-type-parse '(Vec a n)) nbe))
    (should-not (tl-nbe-equal (tl-type-parse '(Vec a Zero))
                              (tl-type-parse '(Vec a (Succ Zero))) nbe))))

;;; Compiled patterns

(ert-deftest tl-nbe-case-pattern-renames-a-literal-the-way-case-spells-it ()
  "The conversion between the two pattern languages is a rename.
Every shape the function-clause parser accepts must come out with the
tag `termlisp-case' matches on.  A literal spelled any other way
would leave the case tree a branch nothing can take, and the type
side -- which reads the compiled pattern -- would see a pattern it
cannot interpret."
  (should (equal (tl-nbe--case-pattern '(lit 5)) '(plit 5)))
  (should (equal (tl-nbe--case-pattern '(var . $x)) '(pvar $x)))
  (should (equal (tl-nbe--case-pattern '(con True)) '(pcon True))))

(provide 'nbe-test)
;;; nbe-test.el ends here
