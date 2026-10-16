;;; kind-preserve-test.el --- kind preservation of type-level rules -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; F1's checker is the kind mirror of `tl-preserve-check'.  The value
;; side asks whether a rule rewrites every redex at the type it matched;
;; the kind side asks whether it rewrites every type at the kind it
;; matched -- the question that matters once a rule rewrites inside a
;; type, where a reduct of the wrong kind would break every signature
;; that mentions the expression it replaced.  Both sides of a rule are
;; read as types with the rule's variables shared: one node per name,
;; its kind slot filled while the left side is kinded and read while
;; the right side is, so the right side is judged at every kind the
;; match admits rather than at the one it would choose.  The verdicts
;; are the three the value checker speaks, and only `preserved' says
;; the rule is safe.
;;
;; The oracle section is the kind side's twin of
;; `tl-preserve-oracle-matches-the-prelude': the value oracle pins the
;; family of prelude rules it cannot decide, and the kind oracle pins
;; the family it refuses -- the same class-method implementations, seen
;; from the side that can see them.  A change in either direction has
;; to be looked at.

;;; Code:

(require 'test-support)
(require 'termlisp)

(defun kind-preserve-test--env ()
  "Return a fresh environment with the prelude checked and elaborated.
The same options the value oracle runs under, so both oracles bucket
the same rule set from the same declarations."
  (termlisp-load-prelude
   (termlisp-make-env '(:type-check t :elaborate t))))

(ert-deftest tl-kind-preserve-check-refuses-a-reduct-that-changes-kind ()
  "A reduct at another kind is violated, with both kinds in the reason.
`(List a)' applies a type constructor to a type and comes out a proper
type, kind `*'; `Zero' is a Nat value, kind `Nat'.  The kinds do not
match, so the verdict is `violated' -- not `cannot-check', which would
say only that the checker failed to look."
  (let* ((env (kind-preserve-test--env))
         (v (tl-kind-preserve-check
             env (tl-make-grule 'kind-preserve-test :normalize 0
                                '(List $a) 'Zero))))
    (should (eq (car v) 'violated))
    (should (string-match-p "the reduct is at kind" (cdr v)))))

(ert-deftest tl-kind-preserve-check-refuses-a-reduct-that-mistakes-a-type-for-a-value ()
  "A reduct that feeds a type where a value belongs is violated.
The pattern pins `a' to `*', because `List' wants a type there; the
reduct hands the same `a' to `Cons', whose lifted kind asks for the
values of some type instead.  The clash is found while the right side
is being kinded, and the reason carries the kind error that found it."
  (let* ((env (kind-preserve-test--env))
         (v (tl-kind-preserve-check
             env (tl-make-grule 'kind-preserve-test :normalize 0
                                '(List $a) '(Cons $a $a)))))
    (should (eq (car v) 'violated))
    (should (string-match-p "Kind error" (cdr v)))))

(ert-deftest tl-kind-preserve-check-keeps-a-reduct-at-the-same-kind ()
  "A reduct that stays at the pattern's kind is preserved, with no reason.
`(Vec a n)' is a proper type at both ends: the index takes Nat values
and `Succ' delivers one, so growing the index changes nothing about
what kind the whole sits at.  Both sides share the pattern's variables,
which is what lets the right side's demands be read against the pins
the left side already set."
  (let* ((env (kind-preserve-test--env))
         (v (tl-kind-preserve-check
             env (tl-make-grule 'kind-preserve-test :normalize 0
                                '(Vec $a $n) '(Vec $a (Succ $n))))))
    (should (eq (car v) 'preserved))
    (should-not (cdr v))))

(ert-deftest tl-kind-preserve-check-cannot-decide-a-rule-without-a-pattern ()
  "A rule with nothing to match with is reported as undecided.
Guarded earlier by the same clause `tl-preserve-check' uses: silence
would read as permission, and the kind side refuses blind as surely as
the value side does."
  (let ((v (tl-kind-preserve-check
            (kind-preserve-test--env)
            (tl-make-grule 'kind-preserve-test :normalize 0 nil nil))))
    (should (eq (car v) 'cannot-check))))

;;; The oracle: the prelude's own type-level rules

(defconst kind-preserve-test--violated
  '(num-mul num-sub num-add maybe-ap ap pure return bind fmap
    monad-fmap monad-bind monad-return)
  "Prelude rules the kind checker refuses, by name.
Each is the implementation of a class method, and each reduct applies
a variable the pattern declared a value.  The pattern takes the
method out of its dictionary -- `(num-add (NumDict add sub mul) a
b)' -- and the dictionary constructor has already said what came out
is a value: its fields are types, so the lifted kind of the
constructor asks for `univ' of their types, the kind of the values it
stores, and `univ(T)' is no `karr' that an application could consume.
The reduct applies it anyway -- `(add a b)' -- and the reduct does not
kind.  The value checker cannot decide this family at all, no scheme
covering the dict-taking pattern, while the kind side can see it, and
what it sees it refuses.")

(ert-deftest tl-kind-preserve-oracle-buckets-the-prelude-rules ()
  "Every prelude rule gets the verdict the findings above predict.
The oracle buckets the rule set `tl-nbe--rules' hands the type level,
the way the value oracle buckets it: the family named in
`kind-preserve-test--violated' comes back `violated' and no other
rule may, nothing may go undecided, and every rule lands in exactly
one bucket.  A change here is a finding about the prelude, not a
nuisance: the test exists so the change has to be looked at."
  (let* ((env (kind-preserve-test--env))
         (rules (tl-nbe--rules (tl-nbe env nil)))
         (buckets (list (cons 'preserved nil)
                        (cons 'violated nil)
                        (cons 'cannot-check nil))))
    (should rules)
    (dolist (r rules)
      (let* ((v (tl-kind-preserve-check env r))
             (cell (assq (car v) buckets)))
        (should cell)
        (setf (cdr cell) (cons (tl-grule-name r) (cdr cell)))))
    (should (null (cdr (assq 'cannot-check buckets))))
    (let ((got (cdr (assq 'violated buckets))))
      (should (= (length got) (length kind-preserve-test--violated)))
      (dolist (name kind-preserve-test--violated)
        (should (memq name got))))
    (should (= (length rules)
               (+ (length (cdr (assq 'preserved buckets)))
                  (length kind-preserve-test--violated))))))

(provide 'kind-preserve-test)
;;; kind-preserve-test.el ends here
