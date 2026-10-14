;;; treematch-workload-test.el --- stress workload from ~/treematch -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; The `~/treematch' port, in the shape TREEMATCH-PORT.md §7 chose for it:
;; not a port but its *type shapes*, used to stress the checker.
;;
;; `~/treematch' is a ~1,276-line OCaml code generator: `.tm' AST
;; declarations become mutually recursive variant types, and `map' rules
;; become class visitors.  Its own doc promises a language runtime that
;; was never written, so what it actually exercises is narrow and worth
;; naming: mutual recursion, parameterised types, constructors whose
;; fields mention types declared later, deep constructor patterns, and a
;; great many partial matches.  It writes no proofs and never will.
;;
;; That last shape is the reason this file exists rather than a port.
;; treematch's `typing.ml' -- 349 lines, its largest module -- leans on
;; the exhaustiveness OCaml's compiler hands out for free and covers the
;; rest with `assert' and `Not_found' used as control flow.  Carried to
;; termlisp unchanged, those become runtime explosions and silently
;; wrong branches.  Exhaustiveness checking is the one part of what this
;; repository built that treematch actually needed, so it is the part
;; that gets measured here: not "does the checker accept the shape" but
;; "does it name the case that was forgotten, at depth, before anything
;; runs".
;;
;; The declarations below are `testsuite/treematch/001-basic_ast.tm'
;; translated to s-expressions.  Its twelve groups reference each other
;; in both directions, which is the property §6 risked as T1 and which
;; the checker handles in either declaration order.
;;
;; Timings are asserted only against a bound wide enough to be
;; uninteresting: the point is to notice an algorithm that stopped being
;; linear, not to police a machine's speed.  The measurements this file
;; was calibrated against are recorded in TREEMATCH-PORT.md.

;;; Code:

(require 'ert)
(require 'termlisp)
(require 'termlisp-exhaust)
(require 'test-support)

(defconst tl-tm--opts '(:type-check t :elaborate t :coverage t)
  "Options every workload here is checked under: coverage included.")

(defconst tl-tm--ast
  "(datatype Identifier (MkIdentifier String))
(datatype Identifer (MkIdentifer String))
(datatype Integer (MkInteger Int))
(datatype Operator (Plus) (Minus) (Mult))
(datatype Arguments (Arg Identifer Arguments) (ArgsEnd))
(datatype Expressions (ExprL Expression Expressions) (ExprsEnd))
(datatype Expression
  (Let Identifer Expression Expression)
  (Apply Operator Expression Expression)
  (Call Identifer Expressions)
  (Variable Identifier)
  (Constant Integer))
(datatype Function (Fn Identifer Arguments Expression))
(datatype Global (Glob Identifer))
(datatype Definition (DFunction Function) (DGlobal Global))
(datatype Program (PProgram Definition Program) (PEnd))"
  "`001-basic_ast.tm' as termlisp declarations.
Eleven types plus `Expression''s five constructors; `Identifer' and
`Identifier' are separate on purpose, which is how the OCaml source
gets its `U' and `L' phantom distinction out of a type system that
cannot express a row constraint.  `End' appears twice in the .tm file --
under `Arguments' and under `Expressions' -- and keeps two names here
for the same reason.")

(defconst tl-tm--size
  (concat tl-tm--ast "
(: size (-> Program Int))
(define (size (PEnd)) 0)
(define (size (PProgram d rest)) (+ 1 (size rest)))")
  "`001-basic_ast.tm''s `Program' spine, covered completely.")

(defconst tl-tm--size-partial
  (concat tl-tm--ast "
(: size (-> Program Int))
(define (size (PProgram d rest)) (+ 1 (size rest)))")
  "`tl-tm--size' with `PEnd' left out: the shape `typing.ml' shipped.
Its OCaml `function' on a `Program' would not compile without the case;
here nothing runs until the coverage check says otherwise.")

;;; The shapes, one property each

(tl-test-covers tl-tm-mutual-recursion-in-both-directions
                tl-tm--size tl-tm--opts)

(tl-test-covers tl-tm-a-forward-reference-is-not-a-free-variable
                (concat tl-tm--ast "
(datatype P (MkP Q))
(datatype Q (MkQ Nat))
(define ok (MkP (MkQ Zero)))
ok")
                tl-tm--opts)

(tl-test-reject tl-tm-a-forward-reference-still-loses-nothing
                (concat tl-tm--ast "
(datatype P (MkP Q))
(datatype Q (MkQ Nat))
(define bad (MkP (MkQ True)))
bad")
                "Cannot apply MkQ to True" tl-tm--opts)

(tl-test-covers tl-tm-three-deep-constructor-patterns
                (concat tl-tm--ast "
(: f (-> Program Int))
(define (f (PProgram (DFunction (Fn n a e)) rest)) 1)
(define (f (PProgram (DGlobal g) rest)) 1)
(define (f (PEnd)) 0)")
                tl-tm--opts)

(tl-test-covers tl-tm-a-nested-pattern-sixteen-deep
                (let ((pat "MkB"))
                  (dotimes (_ 16) (setq pat (format "(MkA1 %s)" pat)))
                  (format "(datatype E (MkA1 E) (MkB))
(: f (-> E Int))
(define (f %s) 1)
(define (f _) 0)" pat))
                tl-tm--opts)

;;; Exhaustiveness: what `typing.ml' got from the OCaml compiler

(tl-test-coverage-reject tl-tm-an-uncounted-constructor-is-named
                         tl-tm--size-partial
                         "no case for PEnd" tl-tm--opts)

(tl-test-coverage-reject tl-tm-an-uncounted-case-is-named-at-depth
                         (concat tl-tm--ast "
(: f (-> Program Int))
(define (f (PProgram (DFunction (Fn n a e)) rest)) 1)
(define (f (PEnd)) 0)")
                         "(PProgram (DGlobal _) _)" tl-tm--opts)

;; The exhaustiveness machine has a budget, and running out of it is an
;; error rather than a pass.  A coverage check that gave up has proved
;; nothing, and reading that as coverage is the failure the whole file
;; exists to prevent -- so it is worth a test that the budget is real.
(ert-deftest tl-tm-an-exhausted-coverage-budget-signals ()
  "A coverage check that runs out of steps reports it instead of passing.
`tl-exh-fuel' is one integer, and this is the assertion that it is
load-bearing: with twelve binary constructors the usefulness search has
real work to do, and ten steps is not enough of it."
  (let ((tl-exh-fuel 10)
        (src (concat "(datatype E "
                     (mapconcat (lambda (i) (format "(C%d E E)" i))
                                (number-sequence 1 12) " ")
                     ")\n(: f (-> E Int))\n"
                     (mapconcat
                      (lambda (i) (format "(define (f (C%d a b)) 1)" i))
                      (number-sequence 1 12) "\n"))))
    (should (string-match-p
             "fuel exhausted"
             (tl-test--coverage src tl-tm--opts)))))

;;; The `003-simple_map.tm' shape: rewriting over a list

(tl-test-eval tl-tm-a-rewrite-rule-runs
              (concat tl-tm--ast "
(define (double (Cons x xs)) (Cons x (Cons x xs)))
(define (double Nil) Nil)
(: q (List Nat))
(define q (double (Cons Zero (Cons (Succ Zero) Nil))))
q")
              "(Cons Zero (Cons Zero (Cons (Succ Zero) Nil)))" tl-tm--opts)

;; `map reverse_args : ListA => ListB' in 003 writes `Cons xs x' where
;; the constructor takes the element first.  Nothing in treematch's own
;; pipeline catches that: the rule is only ever run, never checked
;; against the target type until it fires.  Here it is a type error, at
;; the declaration, which is the whole value the exhaustiveness pass and
;; the indexed constructors add to a translation of this shape.
(tl-test-reject tl-tm-an-argument-swap-is-caught-at-the-declaration
                (concat tl-tm--ast "
(: rev (-> (List Nat) (List Nat)))
(define (rev (Cons x xs)) (Cons xs x))
(define (rev Nil) Nil)")
                "does not match its signature" tl-tm--opts)

;;; Scale

(ert-deftest tl-tm-hundreds-of-mutual-datatypes ()
  "`001-basic_ast.tm' sixty-four times over: 704 datatypes, checked.
The bound is deliberately loose -- a tenth of a minute -- because what
is being guarded is the shape of the cost, not the cost.  Measured on
this machine the sixty-four copies cost about 0.17s over the 0.26s a
run spends loading the prelude anyway, against 0.13s for one copy:
sixty-four times the datatypes buys a few hundredths of a second, so
the growth is close to linear.  A superlinear search would blow through
this bound long before it got embarrassing."
  (let* ((copy (lambda (i)
                 (replace-regexp-in-string
                  "Identifier" (format "Identifier%d" i) tl-tm--ast)))
         (src (mapconcat copy (number-sequence 1 64) "\n"))
         (t0 (float-time))
         (got (tl-test--coverage src tl-tm--opts))
         (elapsed (- (float-time) t0)))
    (should (equal got "ok"))
    (should (< elapsed 60.0))))

(ert-deftest tl-tm-depth-does-not-cost-exponentially ()
  "A nested pattern is cheap at depth 16, and the point is that it is flat.
The usefulness search is the part of this repository with a worst case,
and a nested constructor pattern is where it would show.  Depth 1, 2, 4,
8 and 16 all finish inside the noise here, which is what it means for
the cost to track the pattern rather than a power of it."
  (dolist (depth '(1 2 4 8 16))
    (let ((pat "MkB"))
      (dotimes (_ depth) (setq pat (format "(MkA1 %s)" pat)))
      (should
       (equal
        (tl-test--coverage
         (format "(datatype E (MkA1 E) (MkB))
(: f (-> E Int))
(define (f %s) 1)
(define (f _) 0)" pat)
         tl-tm--opts)
        "ok")))))

(provide 'treematch-workload-test)
;;; treematch-workload-test.el ends here
