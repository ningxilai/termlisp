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
  '(maybe-mapm list-mapm-bind list-mapm maybe-traverse list-traverse
    mapm traverse fold-map to-list foldr endo-mappend run-endo mappend
    num-mul num-sub num-add reader-lift-a2 state-lift-a2 list-lift-a2
    maybe-lift-a2 maybe-ap lift-a2 ap pure return bind fmap
    monad-fmap monad-bind monad-return)
  "Prelude rules the kind checker refuses, by name.
The kind side reads every reduct as a type with the pattern's
variables shared, and these thirty reducts it refuses, in three
shapes the reasons report verbatim.  A variable the pattern
declared a value, applied: the dictionary-field family -- `num-add'
applies its `add', `foldr' applies the `FoldableDict' field `fo',
`traverse' and `mapm' apply their two dict fields, `mappend'
applies the `MonoidDict' field `app', `run-endo' and `endo-mappend'
apply the `Endo' field `f' -- and the four lift implementations,
whose uncurrying wrapper leaves a `(lambda (y) (f x y))' of
function kind where the reading wants `*'.  A constructor
application where a proper type is required: `to-list' and
`list-mapm-bind' both fold with `Cons', whose lifted kind asks for
values and whose answer has kind `List', not `*'.  The value
checker sees none of this -- the family it cannot decide is pinned
separately in `preserve-test--cannot' -- and every other reduct is
preserved.")

(ert-deftest tl-kind-preserve-oracle-buckets-the-prelude-rules ()
  "Every prelude rule gets the verdict the findings above predict.
The oracle buckets the rule set `tl-nbe--rules' hands the type level,
the way the value oracle buckets it: the family named in
`kind-preserve-test--violated' comes back `violated' and no other
rule may, nothing may go undecided, and every rule lands in exactly
one bucket.  Rules the oracle has met since it was written are named
too: `vappend' computes its codomain's index with the type-level
`plus', and if its clauses ever stopped being type-readable the rule
would leave the set and every count above would still hold, so
presence is asked for directly.  A change here is a finding about
the prelude, not a nuisance: the test exists so the change has to be
looked at."
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
                  (length kind-preserve-test--violated))))
    ;; Presence, not just arithmetic: a rule that stops being
    ;; type-readable disappears from `rules' and no count moves.
    (should (memq 'vappend (cdr (assq 'preserved buckets))))))

(provide 'kind-preserve-test)
;;; kind-preserve-test.el ends here
