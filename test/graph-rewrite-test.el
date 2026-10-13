;;; graph-rewrite-test.el --- tests for the term-graph rewriter -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; The term-graph rewriter (`tl-graph-rewrite') is the dormant half of the
;; unified term graph: stage 2(b) chose the node representation partly to
;; revive it, and it is what the type layer now normalises through.  These
;; cases pin the four properties that made it safe to adopt:
;;
;;   - rewriting does not touch the node it was handed, because a type node
;;     is shared by every type that mentions it;
;;   - a rule that structurally fits but has nothing to do is *stuck*, not
;;     an error;
;;   - a clause rule dispatches to the clause that matches and reuses the
;;     matched nodes in the reduct, so the reduct still points at the
;;     variables that were matched;
;;   - fuel is reported in the class the host asks for.

;;; Code:

(require 'ert)
(require 'termlisp-graph)
(require 'termlisp-case)

(defun tl-tgr--sexp (node)
  "Render NODE back to an s-expression, for readable assertions."
  (tl-node->sexp node))

;;; Purity

(ert-deftest tl-tgr-reduce-leaves-the-node-it-was-given-alone ()
  "`tl-graph-reduce' computes a reduct; it never edits the subject."
  (let* ((node (tl-graph-root (tl-graph-build '(f a))))
         (rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x)))
         (reduct (tl-graph-reduce node rule)))
    (should (tl-node-p reduct))
    (should (equal (tl-tgr--sexp reduct) '(g a)))
    ;; The subject still says what it said before.
    (should (eq (tl-node-head node) 'f))
    (should (eq (tl-node-head (car (tl-node-children node))) 'a))))

(ert-deftest tl-tgr-rewriting-a-shared-node-does-not-reach-the-other-holder ()
  "Two graphs may point at one node; rewriting one must not rewrite both."
  (let* ((graph (tl-graph-build '(wrapper (f a))))
         (shared (car (tl-node-children (tl-graph-root graph))))
         (other (tl-make-graph shared nil))
         (rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x))))
    (tl-graph-rewrite other (list rule))
    (should (eq (tl-node-head (tl-graph-root other)) 'g))
    ;; The first graph still holds the original.
    (should (eq (tl-node-head shared) 'f))
    (should (eq (tl-node-head (car (tl-node-children shared))) 'a))
    (should (equal (tl-tgr--sexp (tl-graph-root graph)) '(wrapper (f a))))))

;;; Clause rules

(defconst tl-tgr--plus-rule
  (tl-make-crule
   'plus :normalize 0
   (list (cons (tl-pat-parse '(pcon plus (plit Zero) (pvar $m))) '$m)
         (cons (tl-pat-parse '(pcon plus (pcon Succ (pvar $n)) (pvar $m)))
               '(Succ (plus $n $m)))))
  "The prelude's `plus', written as a clause-based rewrite rule.")

(ert-deftest tl-tgr-a-clause-rule-selects-the-clause-that-matches ()
  "`Zero' takes the first clause; `Succ' must fall through to the second."
  (should (equal (tl-tgr--sexp
                  (tl-graph-reduce (tl-graph-root (tl-graph-build '(plus Zero b)))
                                   tl-tgr--plus-rule))
                 'b))
  (should (equal (tl-tgr--sexp
                  (tl-graph-reduce (tl-graph-root (tl-graph-build '(plus (Succ a) b)))
                                   tl-tgr--plus-rule))
                 '(Succ (plus a b)))))

(ert-deftest tl-tgr-a-clause-rule-stops-when-no-clause-applies ()
  "`n' is neither `Zero' nor a `Succ', so the term is stuck and stays put.
Stuck is a normal form, not an error: reducing the whole graph around it
must leave it exactly where it was."
  (should-not (tl-graph-reduce (tl-graph-root (tl-graph-build '(plus n m)))
                               tl-tgr--plus-rule))
  (should (equal (tl-graph-rewrite-sexp '(plus n m)
                                        (list tl-tgr--plus-rule))
                 '(plus n m))))

(ert-deftest tl-tgr-the-reduct-reuses-the-matched-nodes ()
  "The reduct must point at the nodes that were matched, not at copies.
A copy of a unification variable is not that variable: equating the copy
would leave the original free and the equality would hold nowhere."
  (let* ((node (tl-graph-root (tl-graph-build '(plus Zero b))))
         (reduct (tl-graph-reduce node tl-tgr--plus-rule))
         (argument (cadr (tl-node-children node))))
    ;; `$m' is the second argument, so the reduct *is* that node.
    (should (eq reduct argument))))

;;; Templates that are functions

(ert-deftest tl-tgr-a-function-template-supplies-the-reduct ()
  "A clause may compute its own reduct instead of naming it.
This is how the type layer unfolds a definition: the body names its
variables the ordinary way -- `n', not `$n' -- so the rule carries a
function that substitutes and nothing else does.  A node the function
returns is used as it stands, so it keeps whatever identity it has."
  (let* ((node (tl-graph-root (tl-graph-build '(f a b))))
         (bound nil)
         (rule (tl-make-grule
                'f :normalize 0 '(f $x $y)
                (lambda (bindings)
                  (setq bound bindings)
                  (cdr (assq '$y bindings))))))
    (should (eq (tl-graph-reduce node rule) (cadr (tl-node-children node))))
    ;; Both arguments arrived, and they arrived as the nodes that were matched.
    (should (eq (cdr (assq '$x bound)) (car (tl-node-children node))))
    (should (eq (cdr (assq '$y bound)) (cadr (tl-node-children node))))))

;;; Matching reduces first

(ert-deftest tl-tgr-matching-reduces-an-argument-before-deciding ()
  "A clause cannot see that `(id Zero)' is a `Zero' unless it reduces first.
`tl-graph-whnf' is how a host offers that reduction."
  (let* ((tl-graph-whnf (lambda (n)
                          (if (and (tl-node-application n)
                                   (eq (tl-node-head n) 'id))
                              (car (tl-node-children n))
                            n)))
         (rule (tl-make-crule 'f :normalize 0
                              (list (cons (tl-pat-parse '(pcon f (plit Zero)))
                                          'ok))))
         (node (tl-graph-root (tl-graph-build '(f (id Zero))))))
    (should (equal (tl-tgr--sexp (tl-graph-reduce node rule)) 'ok))))

(ert-deftest tl-tgr-matching-is-structural-when-no-reduction-is-offered ()
  "With `tl-graph-whnf' unbound the same rule sees only the syntax."
  (let ((rule (tl-make-crule 'f :normalize 0
                             (list (cons (tl-pat-parse '(pcon f (plit Zero)))
                                         'ok)))))
    (should-not (tl-graph-reduce (tl-graph-root (tl-graph-build '(f (id Zero))))
                                 rule))))

;;; Fuel

(ert-deftest tl-tgr-running-out-of-fuel-signals-in-the-default-class ()
  "With no host to ask, the rewriter reports its own failure class."
  (let ((rule (tl-make-grule 'grow :normalize 0 '(grow $x) '(grow (Succ $x)))))
    (should-error (tl-graph-rewrite-sexp '(grow a) (list rule) 3)
                  :type 'termlisp-eval-error)))

(ert-deftest tl-tgr-running-out-of-fuel-signals-in-the-hosts-class ()
  "A host normalising a type asks for its own error class.
A type-level function that will not stop is a type error, not an
evaluation error."
  (let ((rule (tl-make-grule 'grow :normalize 0 '(grow $x) '(grow (Succ $x)))))
    (should-error (tl-graph-rewrite-sexp '(grow a) (list rule) 3
                                         'termlisp-type-error)
                  :type 'termlisp-type-error)))

(ert-deftest tl-tgr-fuel-is-spent-on-steps-not-on-time ()
  "A term that reduces once and stops must not exhaust a small fuel."
  (let ((rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x))))
    (should (equal (tl-graph-rewrite-sexp '(f a) (list rule) 2) '(g a)))))

(provide 'graph-rewrite-test)
;;; graph-rewrite-test.el ends here
