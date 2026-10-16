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
;;
;; The gate is also turned on the prelude's own rules, which were
;; written before there was a gate to run them through: every clause
;; is rebuilt as the term it spells and given the same locality trial
;; a new `rewrite' gets, and the one rule that cannot pass it is
;; recorded under its reason rather than let through silently.

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

;; The gate also holds the two obligations a value verdict cannot
;; speak for.  A clause the type layer can read may be unfolded inside
;; a type, so the kinds it preserves are asked of it too, and its cut
;; is tried at its own pattern under DPO discipline: a value can be
;; re-generalized after a shared cut, a kind cannot, so what `reduce'
;; merely records the gate refuses.

(tl-test-reject tl-rewrite-form-refuses-a-rule-the-kinds-do-not-allow
  "(datatype Box (MkBox (-> Nat Nat)))
(define (h (MkBox f)) Zero)
(rewrite (h (MkBox f)) (f Zero))" "the reduct does not kind"
  '(:type-check t :elaborate t))

(tl-test-reject tl-rewrite-form-refuses-a-pattern-that-cuts-where-it-does-not-own
  "(define (f x y) x)
(datatype G (MkG a))
(rewrite (f (MkG a) (MkG a)) (MkG a))" "the cut is not local: identification"
  '(:type-check t :elaborate t))

(tl-test-reject tl-rewrite-form-refuses-a-reduct-that-escapes-its-own-cut
  "(define (f x) x)
(rewrite (f (Succ x)) (Succ (f (Succ x))))" "the cut is not local: dangling"
  '(:type-check t :elaborate t))

(ert-deftest tl-rewrite-form-tries-a-rule-and-finds-every-cut-local ()
  "An accepted rewrite leaves the trial's own verdict behind: nil.
The gate normalises the pattern with the new rule and writes what the
walk found to `tl-dpo-last-gluing', the slot `tl-reduce-term' also
reports through; the sentinel shows the slot was written, and `rf'
answers at the extended type because the clause really landed."
  (let ((env (termlisp-load-prelude
              (termlisp-make-env '(:type-check t :elaborate t)))))
    (termlisp-eval "(define (rf True) True)" env)
    (setq tl-dpo-last-gluing 'unset)
    (termlisp-eval "(rewrite (rf False) False)" env)
    (should-not tl-dpo-last-gluing)
    (should (equal (termlisp-eval "(rf False)" env) 'False))))

;;; The locality trial over the prelude's own rules

(defconst rewrite-form-test--folded
  '(trans)
  "Prelude rules the locality trial reports, by name.
`trans' spells both its arguments `Refl' because the clause needs
them to type: each `Refl' pattern collapses one equation of the
signature's `x y z' chain, and only then does the body `Refl' prove
`(Eq a x z)'.  The two positions reach one node on a term graph that
hash-conses, so what the trial reports as identification is one
element of the pattern appearing at two places, and the reduct is
the node those positions already share.  The verdict stays recorded
in `tl-dpo-last-gluing' as it is for `reduce', and a user rewrite
that repeats a subterm it does not need is refused as before: this
is the one rule the prelude cannot spell any other way.")

(defun rewrite-form-test--pattern-term (pat)
  "Return the term the compiled pattern PAT spells.
A variable, a literal or a wildcard reads itself, a nullary
constructor stands as its own atom rather than a call, and a
constructor with parameters spells the application."
  (pcase (car-safe pat)
    ('pvar (cadr pat))
    ('plit (cadr pat))
    ('pwild '_)
    ('pcon (if (null (cddr pat))
               (cadr pat)
             (cons (cadr pat)
                   (mapcar #'rewrite-form-test--pattern-term (cddr pat)))))
    (_ (error "The type layer does not read pattern %S" pat))))

(defun rewrite-form-test--lhs (name pat)
  "Return the application of NAME that the clause PAT spells.
A compiled pattern leads with the name and carries `(pnil)' markers
for parameters the term does not spell, so those are dropped and the
remaining arguments read as terms."
  (cons name
        (mapcar #'rewrite-form-test--pattern-term
                (cl-remove-if (lambda (x) (eq (car-safe x) 'pnil))
                              (cddr pat)))))

(ert-deftest tl-rewrite-locality-trials-the-prelude-rules ()
  "Every clause the prelude ships cuts locally at its own pattern.
Each rule's clauses are rebuilt as the terms they spell and put
through `tl-rewrite--locality', the trial the gate runs on a new
`rewrite': nil is the answer every rule gives, except that the rules
named in `rewrite-form-test--folded' must come back flagged, so the
exemption can neither be passed over quietly nor outlive the reason
written down for it.  A rule that stopped being type-readable would
leave the rule set and never be tried at all, so the count is also
checked to have reached past the number of rules: clauses, not
rules, are what this pins."
  (let* ((env (termlisp-load-prelude
               (termlisp-make-env '(:type-check t :elaborate t))))
         (rules (tl-nbe--rules (tl-nbe env nil)))
         (tried 0)
         (flagged nil))
    (should rules)
    (dolist (r rules)
      (dolist (cl (tl-grule-clauses r))
        (let* ((name (tl-grule-name r))
               (v (tl-rewrite--locality
                   r (rewrite-form-test--lhs name (car cl)))))
          (setq tried (1+ tried))
          (if (memq name rewrite-form-test--folded)
              (when v (push name flagged))
            (should-not v)))))
    (should (> tried (length rules)))
    (dolist (name rewrite-form-test--folded)
      (should (memq name flagged)))))

(provide 'rewrite-form-test)
;;; rewrite-form-test.el ends here
