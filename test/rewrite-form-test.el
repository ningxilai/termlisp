;;; rewrite-form-test.el --- the rewrite and reduce top-level forms -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Stage 2's two surface forms.  `rewrite' extends an existing function
;; with one more clause, and it is the `rewrite' form -- an ordinary
;; top-level form, not the proof-level rewrite of the roadmap -- so it
;; goes through the same gate a definition does: the new clause is
;; parsed as a pattern, the whole function is re-inferred, and the rule
;; the pair makes is put through `tl-preserve-check'.  A verdict of
;; violated or cannot-check refuses the form before anything is
;; written, which is what the env-intact test below exists to pin:
;; every refusal class is one the function must be shown to survive.
;;
;; `reduce' reads a term as a term -- it does not evaluate -- and
;; unfolds it under the environment's rewrite rules, the same unfolding
;; the type level performs.  Its type is the type of its argument, so
;; the checked cases below are as much about the checker reading
;; `reduce' in every position it can appear in as about the unfolding
;; itself: head position, argument position, and the honest refusal
;; for an open term whose free variable has no type to report.

;;; Code:

(require 'test-support)
(require 'termlisp)

;;; rewrite

(tl-test-eval tl-rewrite-form-appends-a-checked-clause
  "(define (rf True) True)
(rewrite (rf False) False)
(rf False)" "False" '(:type-check t :elaborate t))

(tl-test-reject tl-rewrite-form-refuses-a-reduct-at-the-wrong-type
  "(define (rf True) True)
(rewrite (rf True) 1)" "refused: the reduct is at Int, the pattern at Bool"
  '(:type-check t :elaborate t))

(tl-test-reject tl-rewrite-form-refuses-a-name-that-has-no-clauses
  "(define (rf True) True)
(rewrite (nope True) False)" "no such function to extend"
  '(:type-check t :elaborate t))

(tl-test-reject tl-rewrite-form-refuses-a-name-that-is-a-constructor
  "(rewrite (Zero $x) $x)" "no such function to extend"
  '(:type-check t :elaborate t))

(tl-test-reject tl-rewrite-form-refuses-a-form-that-is-not-an-extension
  "(define (rf True) True)
(rewrite rf False)" "rewrite extends a function"
  '(:type-check t :elaborate t))

;; Without the checker the gate has no verdict to wait for, so it
;; refuses rather than extending blind -- cannot-check is a refusal,
;; not a permission.  `length' comes from the prelude, which loaded
;; without schemes, so its pattern side cannot even be typed.
(tl-test-reject tl-rewrite-form-refuses-when-nothing-can-check-it
  "(rewrite (length Nil) 0)" "the pattern does not type")

(ert-deftest tl-rewrite-form-refusal-leaves-the-function-untouched ()
  "A refused rewrite writes nothing, and an accepted one appends.
The clause table is the environment's own record: if a refusal had
landed before the verdict, `rf' would carry two clauses -- and its
old one would answer at the wrong type."
  (let ((env (termlisp-load-prelude
              (termlisp-make-env '(:type-check t :elaborate t)))))
    (termlisp-eval "(define (rf True) True)" env)
    (should-error (termlisp-eval "(rewrite (rf True) 1)" env)
                  :type 'termlisp-type-error)
    (should (= (length (gethash 'rf (tl-env-clauses env))) 1))
    (termlisp-eval "(rewrite (rf False) False)" env)
    (should (= (length (gethash 'rf (tl-env-clauses env))) 2))
    (should (equal (termlisp-eval "(rf False)" env) 'False))))

;;; reduce

(tl-test-eval tl-reduce-form-unfolds-a-closed-term
  "(reduce (plus (Succ Zero) (Succ Zero)))" "(Succ (Succ Zero))"
  '(:type-check t :elaborate t))

(tl-test-eval tl-reduce-form-hands-back-the-value-it-spells
  "(reduce (plus (Succ Zero) Zero))" "(Succ Zero)")

(tl-test-eval tl-reduce-form-keeps-an-open-term-open
  "(reduce (plus Zero n))" "n")

;; The checker reads `reduce' as its argument, and an argument with a
;; free variable has no type to report -- that refusal is the form's
;; type doing its job, not the form being unreadable.
(tl-test-reject tl-reduce-form-under-the-checker-types-its-argument
  "(reduce (plus Zero n))" "Unknown symbol: n" '(:type-check t :elaborate t))

(tl-test-reject tl-reduce-form-takes-exactly-one-term
  "(reduce)" "reduce takes exactly one term")

(tl-test-reject tl-reduce-form-rejects-two-terms
  "(reduce a b)" "reduce takes exactly one term")

(tl-test-eval tl-reduce-form-reads-the-list-form-the-way-inference-does
  "(head (reduce (list 1 2)))" "1" '(:type-check t :elaborate t))

(tl-test-eval tl-reduce-form-declares-its-value-at-the-arguments-type
  "(define r1 (reduce (plus (Succ Zero) Zero)))
r1" "(Succ Zero)" '(:type-check t :elaborate t))

(tl-test-reject tl-reduce-form-is-caught-wherever-it-appears
  "(head (reduce (plus (Succ Zero) Zero)))" "Cannot apply head"
  '(:type-check t :elaborate t))

(tl-test-eval tl-reduce-form-leaves-a-let-as-it-was-written
  "(reduce (let ((x Zero)) (Succ x)))" "(let ((x Zero)) (Succ x))")

(tl-test-reject tl-reduce-form-stops-when-the-fuel-runs-out
  "(define (spin n) (spin (Succ n)))
(reduce (spin Zero))" "fuel" '(:fuel 30))

(provide 'rewrite-form-test)
;;; rewrite-form-test.el ends here
