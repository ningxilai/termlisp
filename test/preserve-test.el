;;; preserve-test.el --- type preservation of rewrite rules -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Stage 1': the first invariant that does not trust the rule generator.
;; A rule LHS -> RHS preserves types when every redex it matches at a
;; type T rewrites to a reduct at that same T; `tl-preserve-check'
;; decides it by typing both sides, freezing what the left side left
;; open before the right side is read, so the right side is checked at
;; every type the match admits rather than the one it would choose.
;;
;; Two negative tests are the reason the file exists.  The argument
;; mismatch catches a plain unsound reduct.  The polymorphic one
;; catches the subtler mistake -- reading the reduct while the pattern
;; variables are still free to solve, which would bless `(id $x) ->
;; (g $x)' at `g : Int -> Int' even though the rule breaks at every
;; other instantiation of `id'.  Freezing is what tells them apart.
;;
;; The oracle pins what the checker says about the prelude's own rules
;; today: 66 preserved, and one family that cannot be decided at all.
;; Eight method implementations (num-add through fmap) have no scheme
;; in the type environment -- their dict-taking defines are checked
;; against the dict-erased class method and register nothing, so the
;; pattern `(num-mul dict a b)' cannot be typed at all.
;;
;; The other finding the oracle used to pin is fixed.  state-ap and
;; state-ap-run called forward-declared functions, the forward name
;; was typed as a throwaway fresh variable, and their schemes came out
;; more general than their bodies justify.  Inference now records every
;; such use and, once the defining form has been read, tells the
;; earlier uses what the definition really was: the state family comes
;; out at its real State type, both rules are preserved, and
;; `(state-ap-run (Pair 5 0) (lambda (x) x))' at Int is a type error
;; instead of an evaluator crash.  The last test in this file pins
;; that regression.

;;; Code:

(require 'test-support)
(require 'termlisp)

(defconst preserve-test--cannot
  '(num-add num-sub num-mul ap pure return bind fmap)
  "Prelude rules the checker cannot decide at all.
Each is the implementation of a class method: the type environment
holds only the dict-erased method scheme, so the dict-taking pattern
the rule matches has no scheme to be typed against.")

(defun preserve-test--env ()
  "Return an environment with the few definitions the synthetic rules use.
f, g, h are monomorphic at distinct types; id is inferred, so its
scheme is the polymorphic one every instantiation must satisfy."
  (let ((env (termlisp-make-env '(:type-check t :elaborate t))))
    (termlisp-eval "(: f (-> Int Int))
(define (f $x) $x)
(: g (-> Bool Bool))
(define (g $x) $x)
(: h (-> Int Int))
(define (h $x) $x)
(define (id $x) $x)"
                   env)
    env))

(defun preserve-test--rule (pattern template)
  "Return a graph-style rewrite rule matching PATTERN and rebuilding TEMPLATE."
  (tl-make-grule 'preserve-test :normalize 0 pattern template))

;;; Synthetic rules

(ert-deftest tl-preserve-check-accepts-an-ordinary-rule ()
  "A rule whose reduct types at the pattern's own type is preserved.
The prelude's append is the example, and its verdict carries no
reason: `preserved' is a claim, not a guess."
  (let* ((env (termlisp-load-prelude
               (termlisp-make-env '(:type-check t :elaborate t))))
         (rule (cl-find 'append (tl-nbe--rules (tl-nbe env nil))
                        :key #'tl-grule-name)))
    (should rule)
    (should (equal (tl-preserve-check env rule) '(preserved)))))

(ert-deftest tl-preserve-check-catches-an-argument-mismatch ()
  "A reduct at the wrong argument type violates preservation.
f is Int -> Int and g is Bool -> Bool, so `(f $x) -> (g $x)' rewrites
a redex at Int to a term that will not type there."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check env (preserve-test--rule '(f $x) '(g $x)))))
    (should (eq (car v) 'violated))
    (should (stringp (cdr v)))))

(ert-deftest tl-preserve-check-freezes-the-pattern-variables ()
  "The reduct must type at every instantiation the match admits.
id : a -> a, so after `(id $x)' the type of $x is what the match left
open; a reduct `(g $x)' at g : Int -> Int only works if $x is forced
to Int, and forcing is exactly what freezing forbids.  Without it
this rule would be blessed at the one instantiation it likes and
break at every other."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check env (preserve-test--rule '(id $x) '(g $x)))))
    (should (eq (car v) 'violated))))

(ert-deftest tl-preserve-check-accepts-every-instantiation ()
  "A reduct that reuses the open types freely still preserves them.
`(id $x) -> (id (id $x))' works at every instantiation of id, which
is what the frozen reading checks and a forced one would not."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check
             env (preserve-test--rule '(id $x) '(id (id $x))))))
    (should (eq (car v) 'preserved))
    (should-not (cdr v))))

(ert-deftest tl-preserve-check-refuses-to-guess-an-unknown-pattern-name ()
  "An unreadable pattern proves nothing, so it is not a verdict of violation.
`(nosuch $x)' cannot be typed because nothing has a scheme for nosuch;
that is a gap in knowledge, not evidence about the rule."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check
             env (preserve-test--rule '(nosuch $x) '(f $x)))))
    (should (eq (car v) 'cannot-check))))

(ert-deftest tl-preserve-check-refuses-to-guess-an-unknown-reduct-name ()
  "A failing reduct with an unknown name is a gap, not a violation.
The failure would look like the mismatch case were it not for nosuch,
which the environment has never heard of; the checker asks rather
than reads the message."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check
             env (preserve-test--rule '(f $x) '(nosuch $x)))))
    (should (eq (car v) 'cannot-check))))

(ert-deftest tl-preserve-check-lets-a-violation-outweigh-a-gap ()
  "One violating clause decides the rule even when another is unreadable.
Verdicts aggregate worst-first: a rule that breaks anywhere breaks,
and a clause that cannot be read does not soften that."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check
             env
             (tl-make-crule
              'preserve-test :normalize 0
              (list (cons '(pcon f (pvar $x)) '(g $x))
                    (cons '(pcon h (pvar $x)) '(nosuch $x)))))))
    (should (eq (car v) 'violated))))

(ert-deftest tl-preserve-check-ignores-a-guard ()
  "A guard is not read: it only makes a rule apply less often.
Fewer redexes cannot undo what the unguarded rule preserves, so the
guarded and unguarded verdicts must agree."
  (let ((env (preserve-test--env)))
    (should (eq (car (tl-preserve-check
                      env (preserve-test--rule '(f $x) '(g $x))))
                (car (tl-preserve-check
                      env (tl-make-grule
                           'preserve-test :normalize 0 '(f $x) '(g $x)
                           (lambda (_bindings) nil))))))))

(ert-deftest tl-preserve-check-rejects-a-rest-pattern ()
  "A rest binds a sequence, and a sequence is not a term with one type.
The graph pattern reading refuses it rather than inventing a meaning."
  (let* ((env (preserve-test--env))
         (v (tl-preserve-check
             env (preserve-test--rule '(f $x (:rest $xs)) '(g $x)))))
    (should (eq (car v) 'cannot-check))))

;;; The oracle: the prelude's own rules

(ert-deftest tl-preserve-oracle-matches-the-prelude ()
  "Every prelude rule gets the verdict the findings above predict.
Anything preserved must say so with no reason attached; the family
that cannot be decided must appear, under its names, exactly as
documented in `preserve-test--cannot', and no rule may be violated.
A change here is a finding about the prelude, not a nuisance: the
test exists so the change has to be looked at."
  (let* ((env (termlisp-load-prelude
               (termlisp-make-env '(:type-check t :elaborate t))))
         (rules (tl-nbe--rules (tl-nbe env nil)))
         (seen nil))
    (should rules)
    (dolist (r rules)
      (let* ((name (tl-grule-name r))
             (v (tl-preserve-check env r))
             (want (cond ((memq name preserve-test--cannot) 'cannot-check)
                         (t 'preserved))))
        (push name seen)
        (should (eq (car v) want))
        (when (eq (car v) 'preserved)
          (should-not (cdr v)))))
    (dolist (name preserve-test--cannot)
      (should (memq name seen)))))

(ert-deftest tl-preserve-forward-linking-rejects-the-old-violation ()
  "The program the old state-ap finding died on is a type error now.
state-ap-run's scheme used to admit `(Pair 5 0)' where it needed
`Pair (a -> b) s', so the typechecker said yes and evaluation died
with \"No matching clause for state-ap-run2\".  Linking the forward
uses to their definitions is what moves the rejection to the place
that can name it."
  (let ((env (termlisp-load-prelude
              (termlisp-make-env '(:type-check t :elaborate t)))))
    (dolist (prog '("(define bad (state-ap-run (Pair 5 0) (lambda (x) x))) bad"
                    "(define bad (state-ap (lambda (n) n) 0)) bad"))
      (should-error (termlisp-eval prog env) :type 'termlisp-type-error))))

(provide 'preserve-test)
;;; preserve-test.el ends here
