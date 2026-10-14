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
(require 'termlisp-dpo)

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

;;; Double-Pushout rewriting

(ert-deftest tl-dpo-match-records-every-reached-node ()
  "A morphism keeps the whole correspondence, not just the bindings.
The gluing condition is a statement about the set m(L), so that set has
to be recorded before the question can be asked."
  (let* ((graph (tl-graph-build '(f (g a) b)))
         (m (tl-dpo-match '(f $x $y) (tl-graph-root graph))))
    (should (tl-dpo-match-p m))
    (should (eq (tl-dpo-match-root m) (tl-graph-root graph)))
    ;; f, (g a), b -- three positions.  `$x' holds `(g a)' without
    ;; descending into it, so m(L) is what the pattern itself reached.
    (should (= (length (tl-dpo-match-image m)) 3))))

(ert-deftest tl-dpo-match-requires-a-repeat-to-agree ()
  "Two positions naming one variable must reach one node by `eq'.
That is what makes the identification condition decidable."
  (should-not (tl-dpo-match '(f $x $x)
                            (tl-graph-root (tl-graph-build '(f a b)))))
  (should (tl-dpo-match '(f $x $x)
                        (tl-graph-root (tl-graph-build '(f a a))))))

(ert-deftest tl-dpo-interface-keeps-what-the-template-names ()
  "A variable the template never mentions is not in K.
Such a node lies in the zone the step is entitled to cut."
  (let* ((graph (tl-graph-build '(f a b)))
         (m (tl-dpo-interface (tl-dpo-match '(f $x $y) (tl-graph-root graph))
                              '(g $y))))
    (should (= (length (tl-dpo-match-interface m)) 1))
    (should (eq (car (tl-dpo-match-interface m))
                (cadr (tl-node-children (tl-graph-root graph)))))))

(ert-deftest tl-dpo-gluing-names-a-redex-that-is-shared ()
  "A redex reachable from a holder outside the match is not local.
SPO cuts the edge anyway; DPO says which one it was."
  (let* ((graph (tl-graph-build '(w (f a) (f a))))
         (redex (car (tl-node-children (tl-graph-root graph))))
         (m (tl-dpo-interface (tl-dpo-match '(f $x) redex) '(g $x))))
    (should (eq (car (tl-dpo-gluing m (tl-dpo-parents graph))) 'dangling))))

(ert-deftest tl-dpo-gluing-holds-at-the-root-of-a-lonely-graph ()
  (let* ((graph (tl-graph-build '(f a)))
         (m (tl-dpo-interface (tl-dpo-match '(f $x) (tl-graph-root graph))
                              '(g $x))))
    (should-not (tl-dpo-gluing m (tl-dpo-parents graph)))))

(ert-deftest tl-dpo-gluing-reports-two-positions-reaching-one-node ()
  "Two positions of L reaching one host node is what non-injective means.
A complement would have to cut one of them and keep the other, so SPO
folds them; DPO names the node instead."
  (let* ((graph (tl-graph-build '(f a a)))
         (m (tl-dpo-interface (tl-dpo-match '(f $x $y) (tl-graph-root graph))
                              '(g $x $y))))
    (should (eq (car (tl-dpo-gluing m (tl-dpo-parents graph)))
                'identification))))

(ert-deftest tl-spo-apply-leaves-the-host-graph-as-it-was ()
  "The cut is an indirection, not a deletion.
The redex node still reads back as it was written, and the reduct is
what MEMO now holds for it."
  (let* ((graph (tl-graph-build '(f a)))
         (rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x)))
         (m (tl-dpo-interface (tl-dpo-match '(f $x) (tl-graph-root graph))
                              (tl-grule-template rule)))
         (reduct (tl-spo-apply m (tl-grule-template rule))))
    (should (equal (tl-node->sexp reduct) '(g a)))
    (should (eq (tl-node-head (tl-graph-root graph)) 'f))
    (should (eq (cdr (tl-node-memo (tl-graph-root graph))) reduct))))

(ert-deftest tl-dpo-apply-returns-the-reduct-and-its-diagnosis ()
  (let* ((graph (tl-graph-build '(w (f a) (f a))))
         (rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x)))
         (redex (car (tl-node-children (tl-graph-root graph))))
         (res (tl-dpo-apply rule redex graph)))
    (should (equal (tl-node->sexp (car res)) '(g a)))
    ;; The redex is shared, so the cut was not local.
    (should (eq (cadr res) 'dangling))))

(ert-deftest tl-dpo-apply-is-clean-at-the-root ()
  (let* ((graph (tl-graph-build '(f a)))
         (rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x)))
         (res (tl-dpo-apply rule (tl-graph-root graph) graph)))
    (should (equal (tl-node->sexp (car res)) '(g a)))
    (should-not (cdr res))))

(ert-deftest tl-dpo-apply-returns-nil-when-the-rule-does-not-fit ()
  (let* ((graph (tl-graph-build '(h a)))
         (rule (tl-make-grule 'r :normalize 0 '(f $x) '(g $x))))
    (should-not (car (tl-dpo-apply rule (tl-graph-root graph) graph)))))

(provide 'graph-rewrite-test)
;;; graph-rewrite-test.el ends here
