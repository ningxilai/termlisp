;;; prelude-test.el --- prelude, operator and monad regression -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Every form the prelude is expected to support, each in its own
;; test: booleans, pairs, Peano naturals, the hlisp operators, the

;;; Code:

(require 'test-support)

;;; Prelude, operators, monads, list library, builtins

(tl-test-eval tl-prelude-true "true" "True")
(tl-test-eval tl-prelude-false "false" "False")
(tl-test-eval tl-prelude-if-true "(if True 1 2)" "1")
(tl-test-eval tl-prelude-if-false "(if False 1 2)" "2")
(tl-test-eval tl-prelude-not-true "(not True)" "False")
(tl-test-eval tl-prelude-not-false "(not False)" "True")
(tl-test-eval tl-prelude-and-tt "(and True True)" "True")
(tl-test-eval tl-prelude-and-tf "(and True False)" "False")
(tl-test-eval tl-prelude-and-false "(and False 1)" "False")
(tl-test-eval tl-prelude-or-ft "(or False True)" "True")
(tl-test-eval tl-prelude-or-ff "(or False False)" "False")
(tl-test-eval tl-prelude-cons "(cons 1 2)" "(Pair 1 2)")
(tl-test-eval tl-prelude-car "(car (Pair 1 2))" "1")
(tl-test-eval tl-prelude-cdr "(cdr (Pair 1 2))" "2")
(tl-test-eval tl-prelude-zero "zero" "Zero")
(tl-test-eval tl-prelude-one "one" "(Succ Zero)")
(tl-test-eval tl-prelude-two "two" "(Succ (Succ Zero))")
(tl-test-eval tl-prelude-plus "(plus two two)" "(Succ (Succ (Succ (Succ Zero))))")
(tl-test-eval tl-prelude-t "(= 1 1)" "True")
(tl-test-eval tl-prelude-f "(= 1 2)" "False")
(tl-test-eval tl-prelude-xor-tf "(xor True False)" "True")
(tl-test-eval tl-prelude-xor-tt "(xor True True)" "False")
(tl-test-eval tl-prelude-xor-f "(xor False 1)" "False")
(tl-test-eval tl-prelude-null-nil "(null? Nil)" "True")
(tl-test-eval tl-prelude-null-cons "(null? (Cons 1 Nil))" "False")
(tl-test-eval tl-prelude-map "(map 5 (lambda (x) (+ x 1)))" "6")
(tl-test-eval tl-prelude-monad-return-maybe "(monad-return MaybeDict 1)" "(Just 1)")
(tl-test-eval tl-prelude-monad-return-nothing "(monad-return MaybeDict Nothing)" "(Just Nothing)")
(tl-test-eval tl-prelude-monad-bind-just "(monad-bind MaybeDict (Just 1) maybe-return)" "(Just 1)")
(tl-test-eval tl-prelude-monad-bind-nothing "(monad-bind MaybeDict Nothing maybe-return)" "Nothing")
(tl-test-eval tl-prelude-monad-bind-list "(monad-bind ListDict (Cons 1 Nil) list-return)" "(Cons 1 Nil)")
(tl-test-eval tl-prelude-monad-fmap-maybe "(monad-fmap MaybeDict (lambda (x) (+ x 1)) (Just 4))" "(Just 5)")
(tl-test-eval tl-prelude-state-return "((state-return 1) 5)" "(Pair 1 5)")
(tl-test-eval tl-prelude-state-get "((state-get) 5)" "(Pair 5 5)")
(tl-test-eval tl-prelude-state-put "((state-put 9) 5)" "(Pair Unit 9)")
(tl-test-eval tl-prelude-state-bind "((state-bind (state-get) (lambda (s) (state-return (+ s 1)))) 5)" "(Pair 6 5)")
(tl-test-eval tl-prelude-state-fmap "((state-fmap (lambda (x) (* x 2)) (state-return 21)) 0)" "(Pair 42 0)")
(tl-test-eval tl-prelude-reader-ask "((reader-ask) 42)" "42")
(tl-test-eval tl-prelude-reader-return "((reader-return 1) 42)" "1")
(tl-test-eval tl-prelude-reader-bind "((reader-bind (reader-ask) (lambda (r) (reader-return (+ r 1)))) 42)" "43")
(tl-test-eval tl-prelude-head "(head (Cons 1 Nil))" "1")
(tl-test-eval tl-prelude-tail "(tail (Cons 1 (Cons 2 Nil)))" "(Cons 2 Nil)")
(tl-test-eval tl-prelude-length "(length (Cons 1 (Cons 2 Nil)))" "2" '(:elaborate t))
(tl-test-eval tl-prelude-append "(append (Cons 1 Nil) (Cons 2 Nil))" "(Cons 1 (Cons 2 Nil))")
(tl-test-eval tl-prelude-map-list "(map-list (lambda (x) (* x 2)) (Cons 1 (Cons 2 Nil)))" "(Cons 2 (Cons 4 Nil))")
(tl-test-eval tl-prelude-filter "(filter (lambda (x) (< x 2)) (Cons 1 (Cons 2 (Cons 3 Nil))))" "(Cons 1 Nil)")
(tl-test-eval tl-prelude-foldr "(foldr (lambda (x acc) (+ x acc)) 0 (Cons 1 (Cons 2 Nil)))" "3" '(:elaborate t))
(tl-test-eval tl-prelude-foldl "(foldl (lambda (z x) (+ z x)) 0 (Cons 1 (Cons 2 Nil)))" "3")
(tl-test-eval tl-prelude-foldl-with-builtin "(foldl + 0 (Cons 1 (Cons 2 Nil)))" "3")
(tl-test-eval tl-prelude-reverse "(reverse (Cons 1 (Cons 2 Nil)))" "(Cons 2 (Cons 1 Nil))")
(tl-test-eval tl-prelude-sort "(sort (Cons 3 (Cons 1 (Cons 2 Nil))))" "(Cons 1 (Cons 2 (Cons 3 Nil)))")
(tl-test-eval tl-prelude-assertequal-t "(assertEqual 1 1)" "True")
(tl-test-eval tl-prelude-assertequal-f "(assertEqual 1 2)" "False")
(tl-test-eval tl-prelude-op-plus "(+ 1 2)" "3")
(tl-test-eval tl-prelude-op-minus "(- 5 3)" "2")
(tl-test-eval tl-prelude-op-times "(* 4 3)" "12")
(tl-test-eval tl-prelude-op-divide "(/ 8 2)" "4")
(tl-test-eval tl-prelude-op-lt "(< 1 2)" "True")
(tl-test-eval tl-prelude-op-lte "(<= 2 2)" "True")
(tl-test-eval tl-prelude-op-gt "(> 1 2)" "False")
(tl-test-eval tl-prelude-op-gte "(>= 2 2)" "True")
(tl-test-eval tl-prelude-sin "(sin 0)" "0.0")
(tl-test-eval tl-prelude-cos "(cos 0)" "1.0")
(tl-test-eval tl-prelude-tan "(tan 0)" "0.0")
(tl-test-eval tl-prelude-exp "(exp 0)" "1.0")
(tl-test-eval tl-prelude-log "(log 1)" "0.0")
(tl-test-eval tl-prelude-sqrt "(sqrt 4)" "2.0")
(tl-test-eval tl-prelude-format-int "(format \"~a\" 5)" "5")
(tl-test-eval tl-prelude-format-bool "(format \"~a\" True)" "True")
;; A constructor application has no Aldor OutputType here, and it used
;; to fall through to `%s', which printed the argument thunks and the
;; environment they close over instead of the value.  These two are the
;; regression: one bare constructor, one nested inside a list, where the
;; list branch had no way to reach it.
(tl-test-eval tl-prelude-format-constructor
              "(format \"~a\" (Succ Zero))" "(Succ Zero)")
(tl-test-eval tl-prelude-format-list-of-constructors
              "(format \"~a\" (Cons (Succ Zero) Nil))" "[(Succ Zero)]")
(tl-test-eval tl-prelude-string-join "(string-join (list \"a\" \"b\"))" "ab")
(tl-test-eval tl-prelude-string-list "(string->list \"ab\")" "(Cons a (Cons b Nil))")
(tl-test-eval tl-prelude-list-string "(list->string (string->list \"ab\"))" "ab")
(tl-test-eval tl-prelude-list-variadic "(list 1 2 3)" "(Cons 1 (Cons 2 (Cons 3 Nil)))")
(tl-test-eval tl-prelude-list-nullary "(list)" "Nil")
(tl-test-eval tl-prelude-seq "(seq 1 2)" "2")
(tl-test-eval tl-prelude-first "(first (Cons 1 Nil))" "1")
(tl-test-eval tl-prelude-rest "(rest (Cons 1 (Cons 2 Nil)))" "(Cons 2 Nil)")
(tl-test-eval tl-prelude-empty-t "(empty? Nil)" "True")
(tl-test-eval tl-prelude-empty-f "(empty? (Cons 1 Nil))" "False")
(tl-test-eval tl-prelude-builtin-as-value "((lambda (f) (f 1 2)) +)" "3")
(tl-test-eval tl-prelude-builtin-first-as-value "((lambda (f) (f (Cons 1 Nil))) first)" "1")
(tl-test-eval tl-prelude-fmap-maybe "(fmap (lambda (x) (+ x 1)) (Just 4))" "(Just 5)" '(:elaborate t))
(tl-test-eval tl-prelude-fmap-list "(fmap (lambda (x) (+ x 1)) (Cons 1 (Cons 2 Nil)))" "(Cons 2 (Cons 3 Nil))" '(:elaborate t))
(tl-test-eval tl-prelude-fmap-nothing "(fmap (lambda (x) (+ x 1)) Nothing)" "Nothing" '(:elaborate t))
(tl-test-eval tl-prelude-num-add "(num-add 1 2)" "3" '(:elaborate t))
(tl-test-eval tl-prelude-num-sub "(num-sub 5 2)" "3" '(:elaborate t))
(tl-test-eval tl-prelude-num-mul "(num-mul 3 4)" "12" '(:elaborate t))
(tl-test-eval tl-prelude-do-single-bind-maybe "(do (x <- (Just 1)) (return x))" "(Just 1)" '(:elaborate t))
(tl-test-eval tl-prelude-do-single-bind-list "(do (x <- (Cons 1 (Cons 2 Nil))) (return (* x 10)))" "(Cons 10 (Cons 20 Nil))" '(:elaborate t))
(tl-test-eval tl-prelude-sin-composes "(sin (sin 1))" "0.7456241416655579" '(:type-check t))
(tl-test-reject tl-prelude-reject-1-true "(+ 1 True)" "Cannot apply" '(:type-check t))
(tl-test-reject tl-prelude-reject-cos-true "(cos True)" "Cannot apply" '(:type-check t))
(tl-test-reject tl-prelude-reject-string-list-42 "(string->list 42)" "Cannot apply" '(:type-check t))
(tl-test-reject tl-prelude-reject-list-1-true "(list 1 True)" "Cannot apply" '(:type-check t))

;;; Integer and float arithmetic

;; Every primitive here carried a type scheme already and nothing
;; behind it: the call typechecked and then rendered back as source,
;; stuck.  These pin the runtimes under `:type-check t', because the
;; promise that was broken was the scheme's.
(tl-test-eval tl-arith-quo "(quo 7 2)" "3" '(:type-check t))
(tl-test-eval tl-arith-quo-toward-zero "(quo -7 2)" "-3" '(:type-check t))
;; `quo' truncates a float too -- elisp `truncate' behind it -- and
;; that is what makes a floor spellable in term-lisp at all.
(tl-test-eval tl-arith-quo-truncates-a-float "(quo 7.5 1)" "7" '(:type-check t))
(tl-test-eval tl-arith-quo-truncates-a-negative-float "(quo -7.5 1)" "-7"
              '(:type-check t))
;; ...and this is that spelling, kept honest: expressible (the round
;; compared all three roundings against the primitives on an
;; 18-float battery, every one equal) and shipped as primitives
;; anyway, for emit parity and exactness.
(tl-test-eval tl-arith-floor-is-spellable-over-quo
  "(define (floor-spelled x)
     (if (and (< x 0) (> (quo x 1) x)) (- (quo x 1) 1) (quo x 1)))
   (and (eq (floor-spelled -7.5) (floor -7.5))
        (eq (floor-spelled 7.5) (floor 7.5)))"
  "True" '(:type-check t))
(tl-test-eval tl-arith-mod-floors "(mod -7 2)" "1" '(:type-check t))
(tl-test-eval tl-arith-cl-gcd "(cl-gcd -12 18)" "6" '(:type-check t))
(tl-test-eval tl-arith-expt-bignum "(^ 2 100)"
              "1267650600228229401496703205376" '(:type-check t))
(tl-test-eval tl-arith-zero-true "(zero? 0)" "True" '(:type-check t))
(tl-test-eval tl-arith-zero-false "(zero? 3)" "False" '(:type-check t))
(tl-test-eval tl-arith-even-true "(even? 4)" "True" '(:type-check t))
(tl-test-eval tl-arith-even-false "(even? 5)" "False" '(:type-check t))
(tl-test-eval tl-arith-odd-true "(odd? 5)" "True" '(:type-check t))
(tl-test-eval tl-arith-neq-true "(neq 1 2)" "True" '(:type-check t))
(tl-test-eval tl-arith-neq-false "(neq 2 2)" "False" '(:type-check t))
(tl-test-eval tl-arith-floor "(floor 7.5)" "7" '(:type-check t))
(tl-test-eval tl-arith-ceiling "(ceiling 7.2)" "8" '(:type-check t))
;; `round' halves to even -- elisp's rule, and now the prelude's.
(tl-test-eval tl-arith-round-half-to-even "(round 2.5)" "2" '(:type-check t))
(tl-test-reject tl-arith-quo-by-zero "(quo 7 0)" "Division by zero" '(:type-check t))
(tl-test-reject tl-arith-mod-by-zero "(mod 7 0)" "Division by zero" '(:type-check t))

;; The library the primitives feed.  Default options here: these are
;; value pins, and every one of the checked tests above has already
;; loaded and typechecked the prelude that defines them.
(tl-test-eval tl-arith-abs-negative "(abs -3)" "3")
(tl-test-eval tl-arith-abs-positive "(abs 3)" "3")
(tl-test-eval tl-arith-signum-negative "(signum -3)" "-1")
(tl-test-eval tl-arith-signum-zero "(signum 0)" "0")
(tl-test-eval tl-arith-signum-positive "(signum 3)" "1")
(tl-test-eval tl-arith-min "(min 3 5)" "3")
(tl-test-eval tl-arith-max "(max 3 5)" "5")
(tl-test-eval tl-arith-positive-true "(positive? 1)" "True")
(tl-test-eval tl-arith-negative-true "(negative? -1)" "True")
(tl-test-eval tl-arith-square "(square 7)" "49")
(tl-test-eval tl-arith-rem-toward-zero "(rem -7 2)" "-1")
(tl-test-eval tl-arith-rem-positive-divisor "(rem 7 -2)" "1")
(tl-test-eval tl-arith-div-floors "(div -7 2)" "-4")
(tl-test-eval tl-arith-div-positive "(div 7 2)" "3")
;; The section's own claim, checked at the value level: each pair
;; rebuilds its dividend whatever the signs, which is the difference
;; between `quo' and `div' made observable.
(tl-test-eval tl-arith-quo-rem-rebuild-the-dividend
              "(+ (* (quo -7 2) 2) (rem -7 2))" "-7")
(tl-test-eval tl-arith-div-mod-rebuild-the-dividend
              "(+ (* (div -7 2) 2) (mod -7 2))" "-7")
(tl-test-eval tl-arith-gcd "(gcd 12 18)" "6")
(tl-test-eval tl-arith-lcm "(lcm 4 6)" "12")
(tl-test-eval tl-arith-lcm-zero-is-zero "(lcm 0 5)" "0")
;; 20! exceeds a fixnum, so this pins the arbitrary-width Integer an
;; interpreter's `IntegerVal' is supposed to have.  `factorial' is a
;; primitive, not a prelude definition: the locality law refuses an
;; Int accumulator loop (see the note in termlisp-builtins).
(tl-test-eval tl-arith-factorial "(factorial 10)" "3628800" '(:type-check t))
(tl-test-eval tl-arith-factorial-bignum "(factorial 20)"
              "2432902008176640000" '(:type-check t))
(tl-test-eval tl-arith-sum "(sum (list 1 2 3))" "6")
(tl-test-eval tl-arith-product "(product (list 2 3 4))" "24")

;; The Calc tower, first-class: a bigfloat is a value with a printed
;; form of its own, a working precision chosen per construction, and a
;; place in the cross-representation order.
(tl-test-eval tl-arith-bigfloat-prints-exactly "(tl-bigfloat 0.1 25)"
              "0.1000000000000000055511151" '(:type-check t))
(tl-test-eval tl-arith-bigfloat-rounds-to-working-precision
              "(tl-bigfloat 12345 2)" "12000" '(:type-check t))
(tl-test-eval tl-arith-bigfloat-inexact-quotient
              "(tl-num-div (tl-bigfloat 1 10) 3)" "0.333333333333" '(:type-check t))
(tl-test-eval tl-arith-num-less-native "(tl-num-less? 1 2)" "True" '(:type-check t))
;; 0.1 at 25 digits is the double's exact value, a hair above a tenth;
;; the order sees what a rounded comparison would miss.
(tl-test-eval tl-arith-num-less-cross-precision
              "(tl-num-less? (tl-bigfloat 0.1 5) (tl-bigfloat 0.1 25))"
              "True" '(:type-check t))
(tl-test-eval tl-arith-num-less-cross-precision-mirror
              "(tl-num-less? (tl-bigfloat 0.1 25) (tl-bigfloat 0.1 5))"
              "False" '(:type-check t))
;; Equal values normalise alike at any precision, so `=' holds.
(tl-test-eval tl-arith-bigfloat-canonical-equality
              "(= (tl-bigfloat 5 5) (tl-bigfloat 5 10))" "True" '(:type-check t))
(tl-test-reject tl-arith-bigfloat-rejects-zero-precision
                "(tl-bigfloat 2 0)" "bigfloat precision" '(:type-check t))
(tl-test-reject tl-arith-num-less-complex
                "(tl-num-less? (tl-complex 1 2) 1)" "Complex numbers have no order"
                '(:type-check t))

;;; The aldor--.hs skeleton: six mutually recursive trees

;; `~/aldor--.hs' is the Haskell sketch of an Aldor interpreter's AST:
;; FB, DefTable, DTE, Expr, Value and Type refer to one another in a
;; cycle, `Value' carries closures as data, and the evaluator does
;; integer arithmetic over all of it.  The prelude is the base library
;; that port must stand on, so the transcription is the capability
;; pin -- symbolic half first, the interpreter's arithmetic in the
;; last two.  The declarations keep the .hs file's own order, which is
;; the part that must not be reordered: every tree mentions a partner
;; the reader has not reached yet.  `QName = [String]' is spelled
;; `(List String)', and the `DefTable' constructor keeps its
;; datatype's own name exactly as the Haskell declaration has it.

(defconst tl-prelude--aldor-hs-datatypes
  "(datatype DefTable (DefTable (List DTE) (List (List String))))
(datatype DTE (DTE String FB Expr))
(datatype FB
  (SimpleFB Expr)
  (NestedFB DefTable FB)
  (FParamFB DTE)
  (VoidFB))
(datatype Expr
  (Literal Value)
  (Identifier (List String))
  (AndList (List FB))
  (OrList (List FB))
  (IfThenElse FB FB FB)
  (FunctionCall FB (List FB))
  (RecordCtor (List FB))
  (UnionCtor Expr FB)
  (UnionCase FB Expr)
  (RestrictType FB FB)
  (ConvertTo FB FB)
  (Add1 FB)
  (Add2 FB FB)
  (With1 FB)
  (With2 FB FB)
  (VoidExpr))
(datatype Value
  (TypeVal Type)
  (BooleanVal Bool)
  (IntegerVal Int)
  (FloatVal DoubleFloat)
  (StringVal String)
  (LambdaVal Type FB)
  (BuiltInOp String Type (-> (List Value) Value))
  (RecordVal (List Value))
  (UnionVal Expr Value)
  (ADT_Val Type Value)
  (TrivVal))
(datatype Type
  (TrivT) (ExitT) (TypeT) (BooleanT) (IntegerT) (FloatT) (StringT)
  (FunctionT (List FB) FB)
  (BuiltInT (List Type) Type)
  (RecordT (List FB))
  (UnionT (List FB))
  (ADT FB DefTable)
  (CategoryT DefTable))"
  "The six data declarations of ~/aldor--.hs, in the file's own order.")

(tl-test-eval tl-prelude-aldor-hs-declare-and-build
  (concat tl-prelude--aldor-hs-datatypes "
           (Literal (TypeVal IntegerT))")
  "(Literal (TypeVal IntegerT))" '(:type-check t))

(tl-test-eval tl-prelude-aldor-hs-nested-match
  (concat tl-prelude--aldor-hs-datatypes "
           (define (int-of (Literal (IntegerVal n))) n)
           (int-of (Literal (IntegerVal 42)))")
  "42" '(:type-check t))

(tl-test-eval tl-prelude-aldor-hs-closure-field
  (concat tl-prelude--aldor-hs-datatypes "
           (define (sum-ints Nil) 0)
           (define (sum-ints (Cons v vs)) (sum-one v (sum-ints vs)))
           (define (sum-one (IntegerVal n) m) (+ n m))
           (define plus-op
             (BuiltInOp \"+\" IntegerT (lambda (args) (IntegerVal (sum-ints args)))))
           (define (call-op (BuiltInOp name ty f) args) (f args))
           (call-op plus-op (list (IntegerVal 1) (IntegerVal 2) (IntegerVal 3)))")
  "(IntegerVal 6)" '(:type-check t))

(tl-test-eval tl-prelude-aldor-hs-evaluator-adds
  (concat tl-prelude--aldor-hs-datatypes "
           (define (value-add (IntegerVal a) (IntegerVal b)) (IntegerVal (+ a b)))
           (value-add (IntegerVal 3) (IntegerVal 4))")
  "(IntegerVal 7)" '(:type-check t))

(tl-test-eval tl-prelude-aldor-hs-evaluator-quotes
  (concat tl-prelude--aldor-hs-datatypes "
           (define (value-quo (IntegerVal a) (IntegerVal b)) (IntegerVal (quo a b)))
           (value-quo (IntegerVal 7) (IntegerVal 2))")
  "(IntegerVal 3)" '(:type-check t))

;;; do-notation and monad sequencing

(tl-test-eval tl-do-two-bind-do "(do (x <- (Just 1)) (y <- (Just 2)) (return (+ x y)))" "(Just 3)" '(:elaborate t))
(tl-test-eval tl-do-single-bind-do "(do (x <- (Just 1)) (return x))" "(Just 1)" '(:elaborate t))
(tl-test-eval tl-do-maybe-failure "(do (x <- (Just 1)) (y <- Nothing) (return (+ x y)))" "Nothing" '(:elaborate t))
(tl-test-eval tl-do-list-do "(do (x <- (Cons 1 (Cons 2 Nil))) (return (* x 10)))" "(Cons 10 (Cons 20 Nil))" '(:elaborate t))
(tl-test-eval tl-do-three-bind-do "(do (x <- (Just 1)) (y <- (Just 2)) (z <- (Just 3)) (return (+ (+ x y) z)))" "(Just 6)" '(:elaborate t))
(tl-test-eval tl-do-nested-do-in-lambda "(define (twice m) (do (x <- m) (y <- m) (return (Pair x y)))) (twice (Just 1))" "(Just (Pair 1 1))" '(:elaborate t))
(tl-test-eval tl-do-fmap "(fmap (lambda (x) (+ x 1)) (Just 4))" "(Just 5)" '(:elaborate t))
(tl-test-eval tl-do-num-add "(num-add 1 2)" "3" '(:elaborate t))

;;; load: loading .tls definitions from a program

;; `load' reads a `.tls' file and evaluates its forms into the running
;; environment.  The evaluator already resolves a call head through the
;; environment at the moment the call is applied, so definitions that
;; arrive mid-run are visible to whatever runs next -- checker included:
;; a later form of the same submission is typechecked against the names
;; the loaded file declared.

(defun tl-test--tls-file (content)
  "Write CONTENT to a fresh temporary `.tls' file and return its name."
  (let ((file (make-temp-file "tl-load-test" nil ".tls")))
    (with-temp-file file (insert content))
    file))

(ert-deftest tl-load-defines-a-function ()
  "A loaded definition answers calls made after the load runs."
  (let ((file (tl-test--tls-file "(define (lib-double n) (* n 2))")))
    (should (equal (tl-test--render
                    (format "(seq (load %S) (lib-double 21))" file) nil)
                   "42"))))

(ert-deftest tl-load-visible-to-later-typechecked-forms ()
  "A submission's later forms typecheck against the loaded definitions."
  (let ((file (tl-test--tls-file "(define (lib-double n) (* n 2))")))
    (should (equal (tl-test--render
                    (format "(load %S)\n(lib-double 21)" file)
                    '(:type-check t))
                   "42"))))

(ert-deftest tl-load-answers-unit ()
  "The load itself renders as the unit value."
  (let ((file (tl-test--tls-file "(define (lib-id x) x)")))
    (should (equal (tl-test--render (format "(load %S)" file) nil)
                   "Unit"))))

(ert-deftest tl-load-relative-path-expands-against-default-directory ()
  "A relative file name resolves against the host's `default-directory'."
  (let* ((dir (make-temp-file "tl-load-test" t))
         (default-directory dir))
    (with-temp-file (expand-file-name "lib.tls" dir)
      (insert "(define (lib-nine) 9)"))
    (should (equal (tl-test--render
                    "(seq (load \"lib.tls\") (lib-nine))" nil)
                   "9"))))

(ert-deftest tl-load-missing-file-errors ()
  "An unreadable file is refused with the name in the message."
  (let ((got (tl-test--render "(load \"/nonexistent/tl-load-no-such.tls\")"
                              nil)))
    (should (string-prefix-p "ERR:" got))
    (should (string-match-p (regexp-quote "cannot read") got))))

(ert-deftest tl-load-non-string-argument-errors ()
  "A non-String argument is a type error naming the builtin."
  (let ((got (tl-test--render "(load 42)" nil)))
    (should (string-prefix-p "ERR:" got))
    (should (string-match-p
             (regexp-quote "load expects a String, got 42") got))))

(ert-deftest tl-load-forward-reference-inside-file ()
  "Inside the loaded file a definition may use a later one."
  (let ((file (tl-test--tls-file
               "(define (lib-a n) (lib-b n))\n(define (lib-b n) (+ n 10))")))
    ;; The use is a later form, not part of the load's own form: a
    ;; submission is checked before it runs, so only a form evaluated
    ;; after the load can name what the load declared.
    (should (equal (tl-test--render
                    (format "(load %S)\n(lib-a 5)" file)
                    '(:type-check t))
                   "15"))))

(ert-deftest tl-load-datatype-reaches-the-checker ()
  "A loaded datatype's constructors are registered for later checking."
  (let ((file (tl-test--tls-file
               "(datatype Color (Red) (Green))\n(define (is-red c) (eq c Red))")))
    (should (equal (tl-test--render
                    (format "(load %S)\n(is-red Red)" file)
                    '(:type-check t))
                   "True"))))

(ert-deftest tl-load-nested-file ()
  "A loaded file may itself load another file."
  (let* ((inner (tl-test--tls-file "(define (lib-inc n) (+ n 1))"))
         (outer (tl-test--tls-file
                 (format "(load %S)\n(define (lib-inc2 n) (lib-inc n))"
                         inner))))
    (should (equal (tl-test--render
                    (format "(seq (load %S) (lib-inc2 41))" outer) nil)
                   "42"))))

(ert-deftest tl-load-parse-error-names-the-file ()
  "A parse error inside the file carries the file's name."
  (let* ((file (tl-test--tls-file "(define (oops"))
         (got (tl-test--render (format "(load %S)" file) nil)))
    (should (string-prefix-p "ERR:" got))
    (should (string-match-p (regexp-quote file) got))))

(ert-deftest tl-load-coverage-queue-waits-for-the-submission ()
  "Loading mid-submission does not flush the submission's coverage queue."
  (let ((file (tl-test--tls-file "(define (lib-id x) x)")))
    (should (equal (tl-test--render
                    (format (concat "(define (spread (Cons x xs)) x)\n"
                                    "(load %S)\n"
                                    "(define (spread Nil) Nil)\n"
                                    "(spread Nil)")
                            file)
                    '(:type-check t :elaborate t :coverage t))
                   "Nil"))))

;;; remove: loading is undoable

;; `remove' restores the snapshot `load' took before its file ran, so
;; every table the load touched -- values, clauses, datatypes, types --
;; goes back at once.  The tests watch names disappear through the
;; checker, because an unchecked unknown head renders as itself rather
;; than signalling: the environment is built with `:type-check t'.

(defun tl-test--load-env ()
  "Return a fresh prelude environment with `:type-check' on."
  (let ((env (termlisp-make-env '(:type-check t))))
    (termlisp-load-prelude env)
    env))

(defun tl-test--eval-render (string env)
  "Evaluate STRING in ENV and render it, or \"ERR:...\" when it signals."
  (condition-case e
      (termlisp-value->string (termlisp-eval string env))
    (error (format "ERR:%s" (error-message-string e)))))

(ert-deftest tl-remove-undoes-a-load ()
  "A removed load's names are unknown again, and removing twice fails."
  (let* ((file (tl-test--tls-file "(define (lib-double n) (* n 2))"))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render (format "(load %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(lib-double 21)" env) "42"))
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(lib-double 21)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: lib-double\""))
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   (format "ERR:Term-lisp evaluation error: \"remove: %s is not loaded\""
                           (expand-file-name file))))))

(ert-deftest tl-remove-restores-an-extended-clause ()
  "A load that extended a function gives its clauses back on remove."
  (let* ((file (tl-test--tls-file "(define (tag (False)) 2)"))
         (env (tl-test--load-env)))
    (termlisp-eval "(define (tag (True)) 1)" env)
    (should (equal (tl-test--eval-render (format "(load %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(tag False)" env) "2"))
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(tag False)" env)
                   "ERR:Term-lisp evaluation error: \"No matching clause for tag\""))
    (should (equal (tl-test--eval-render "(tag True)" env) "1"))))

(ert-deftest tl-remove-restores-a-datatype-extension ()
  "Extending a datatype is undone, and the datatype stays extendable."
  (let* ((file (tl-test--tls-file "(datatype-extension Fruit (Banana))"))
         (env (tl-test--load-env)))
    (termlisp-eval "(datatype open Fruit (Apple))" env)
    (should (equal (tl-test--eval-render (format "(load %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(eq Banana Banana)" env) "True"))
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(eq Banana Banana)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: Banana\""))
    ;; The plist itself was restored, so extending again finds the
    ;; open datatype with its original constructors.
    (should (equal (tl-test--eval-render (format "(load %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(eq Banana Banana)" env) "True"))))

(ert-deftest tl-remove-lifo-loads-of-one-file ()
  "Loading twice and removing once returns to the first load's state."
  (let* ((file (tl-test--tls-file "(define (lib-double n) (* n 2))"))
         (env (tl-test--load-env)))
    (termlisp-eval (format "(load %S)" file) env)
    (termlisp-eval (format "(load %S)" file) env)
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(lib-double 2)" env) "4"))
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(lib-double 2)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: lib-double\""))))

(ert-deftest tl-load-failure-installs-nothing ()
  "A load that fails partway leaves the environment exactly as it was."
  (let* ((file (tl-test--tls-file "(define (keep x) x)\n(+ 1 True)"))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render (format "(load %S)" file) env)
                   "ERR:Term-lisp type error: \"Cannot apply + to True\""))
    (should (equal (tl-test--eval-render "(keep 1)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: keep\""))
    ;; A failed load journals nothing, so there is nothing to remove.
    (should (equal (tl-test--eval-render (format "(remove %S)" file) env)
                   (format "ERR:Term-lisp evaluation error: \"remove: %s is not loaded\""
                           (expand-file-name file))))))

(ert-deftest tl-remove-nested-loads-come-out-with-their-parent ()
  "A nested load is refused by name and disappears with its parent."
  (let* ((dir (make-temp-file "tl-remove-nest" t))
         (inner (expand-file-name "b.tls" dir))
         (outer (expand-file-name "a.tls" dir))
         (env (tl-test--load-env)))
    (with-temp-file inner (insert "(define (lib-b x) x)"))
    (with-temp-file outer
      (insert (format "(load %S)\n(define (lib-a x) x)" inner)))
    (termlisp-eval (format "(load %S)" outer) env)
    (should (equal (tl-test--eval-render "(lib-a (lib-b 1))" env) "1"))
    ;; The child's snapshot is a moment inside the parent's load, so
    ;; naming it points at the parent instead of restoring that moment.
    (should (equal (tl-test--eval-render (format "(remove %S)" inner) env)
                   (format
                    "ERR:Term-lisp evaluation error: \"remove: %s was loaded inside %s; remove that file to undo them both\""
                    inner outer)))
    (should (equal (tl-test--eval-render "(lib-a 1)" env) "1"))
    (should (equal (tl-test--eval-render (format "(remove %S)" outer) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(lib-a 1)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: lib-a\""))
    (should (equal (tl-test--eval-render "(lib-b 2)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: lib-b\""))
    ;; The child's record went out with the parent's record.
    (should (equal (tl-test--eval-render (format "(remove %S)" inner) env)
                   (format "ERR:Term-lisp evaluation error: \"remove: %s is not loaded\""
                           inner)))))

(ert-deftest tl-remove-matches-through-a-symlink ()
  "A remove may spell the loaded file differently than the load did."
  (let* ((file (tl-test--tls-file "(define (lib-s x) x)"))
         (link (concat file "-link.tls"))
         (env (tl-test--load-env)))
    (when (file-exists-p link) (delete-file link))
    (make-symbolic-link file link)
    (termlisp-eval (format "(load %S)" file) env)
    (should (equal (tl-test--eval-render (format "(remove %S)" link) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(lib-s 1)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: lib-s\""))))

(ert-deftest tl-remove-a-file-that-was-never-loaded ()
  "Removing an unknown file is an error naming the expansion."
  (let ((env (tl-test--load-env)))
    (should (equal (tl-test--eval-render
                    "(remove \"/nonexistent/tl-remove-no-such.tls\")" env)
                   "ERR:Term-lisp evaluation error: \"remove: /nonexistent/tl-remove-no-such.tls is not loaded\""))))

(ert-deftest tl-load-journal-is-most-recent-first ()
  "The environment's journal lists loads most recent first."
  (let* ((one (tl-test--tls-file "(define (lib-one x) x)"))
         (two (tl-test--tls-file "(define (lib-two x) x)"))
         (env (termlisp-make-env nil)))
    (termlisp-load-prelude env)
    (termlisp-load one env)
    (termlisp-load two env)
    (should (equal (mapcar (lambda (record)
                             (file-name-nondirectory
                              (tl-load-record-file record)))
                           (tl-env-loads env))
                   (list (file-name-nondirectory two)
                         (file-name-nondirectory one)
                         "termlisp-prelude.tls")))))

;;; REPL banner: the welcome line reads the journal

(ert-deftest tl-repl-banner-lists-the-journal ()
  "The banner names the files the environment actually holds."
  (let* ((file (tl-test--tls-file "(define (lib-id x) x)"))
         (env (termlisp-make-env nil)))
    (termlisp-load-prelude env)
    (termlisp-load file env)
    (with-temp-buffer
      (setq-local termlisp-repl--env env)
      (setq-local termlisp-repl--options '(:type-check t))
      (should (string-match-p
               (format "(loaded: termlisp-prelude\\.tls, %s)"
                       (regexp-quote (file-name-nondirectory file)))
               (termlisp-repl--banner))))))

(ert-deftest tl-repl-banner-says-empty ()
  "A banner over an untouched environment says so."
  (with-temp-buffer
    (setq-local termlisp-repl--env (termlisp-make-env nil))
    (setq-local termlisp-repl--options '(:type-check t))
    (should (string-match-p "(empty environment)"
                            (termlisp-repl--banner)))))

(ert-deftest tl-repl-load-files-are-loaded-at-startup ()
  "`termlisp-repl-load-files' is loaded at startup and listed."
  (let* ((file (tl-test--tls-file "(define (lib-id x) x)"))
         (termlisp-repl-load-prelude t)
         (termlisp-repl-load-files (list file)))
    (with-temp-buffer
      (setq-local termlisp-repl--options '(:type-check t))
      (termlisp-repl--reset-env)
      (should (equal (tl-test--eval-render
                      "(lib-id 7)" termlisp-repl--env)
                     "7"))
      (should (string-match-p
               (format "(loaded: termlisp-prelude\\.tls, %s)"
                       (regexp-quote (file-name-nondirectory file)))
               (termlisp-repl--banner))))))

;;; provide/require: libraries have names

;; `provide' stamps a feature name onto the record of the load the
;; file runs inside, and `require' answers from those stamps: the
;; journal the load machinery already keeps is elisp's `features',
;; per environment.  The tests build their own directories and bind
;; `termlisp-load-path' around the evaluations that need the search
;; path; most run in a `:type-check' environment, so the registered
;; schemes are exercised along the way.

(defun tl-test--library-dir (files)
  "Make a temporary directory holding FILES and return its name.
FILES is an alist of (NAME . CONTENT); each entry is written to a
file called NAME."
  (let ((dir (make-temp-file "tl-require" t)))
    (dolist (spec files)
      (with-temp-file (expand-file-name (car spec) dir)
        (insert (cdr spec))))
    dir))

(ert-deftest tl-provide-stamps-the-load-record ()
  "A finished load's record carries the feature its file provided."
  (let* ((file (tl-test--tls-file
                "(define (lib-id x) x)\n(provide \"lib-id\")"))
         (env (tl-test--load-env)))
    (termlisp-eval (format "(load %S)" file) env)
    (should (equal (tl-load-record-features (car (tl-env-loads env)))
                   '("lib-id")))))

(ert-deftest tl-require-loads-through-the-search-path ()
  "A required feature loads the file that provides it, from the load path."
  (let* ((dir (tl-test--library-dir
               '(("geom.tls" . "(define (area x) (* x x))\n(provide \"geom\")"))))
         (termlisp-load-path (list dir))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render "(require \"geom\")" env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(area 6)" env) "36"))))

(ert-deftest tl-require-falls-back-to-default-directory ()
  "With no load path configured, a feature resolves in `default-directory'."
  (let* ((dir (file-name-as-directory (make-temp-file "tl-require" t)))
         (default-directory dir)
         (termlisp-load-path nil)
         (env (tl-test--load-env)))
    (with-temp-file (expand-file-name "here.tls" dir)
      (insert "(define (here-fn) 7)\n(provide \"here\")"))
    (should (equal (tl-test--eval-render "(require \"here\")" env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(here-fn)" env) "7"))))

(ert-deftest tl-require-is-idempotent ()
  "Requiring twice loads once: the journal grows by a single record."
  (let* ((dir (tl-test--library-dir
               '(("twice.tls" . "(define (twice-fn) 1)\n(provide \"twice\")"))))
         (termlisp-load-path (list dir))
         (env (tl-test--load-env))
         (before (length (tl-env-loads env))))
    (should (equal (tl-test--eval-render "(require \"twice\")" env)
                   "Unit"))
    (should (equal (tl-test--eval-render
                    "(seq (require \"twice\") (twice-fn))" env)
                   "1"))
    (should (= (length (tl-env-loads env)) (1+ before)))))

(ert-deftest tl-require-satisfied-by-a-plain-load ()
  "A feature a `load' already brought in answers without the search path."
  (let* ((file (tl-test--tls-file
                "(define (direct-fn) 3)\n(provide \"direct\")"))
         (termlisp-load-path (list "/nonexistent/tl-require-no-such-dir"))
         (env (tl-test--load-env)))
    (termlisp-eval (format "(load %S)" file) env)
    (should (equal (tl-test--eval-render "(require \"direct\")" env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(direct-fn)" env) "3"))))

(ert-deftest tl-provide-outside-a-load-errors ()
  "A feature stamped outside any load is refused."
  (let ((env (tl-test--load-env)))
    (should (equal (tl-test--eval-render "(provide \"loose\")" env)
                   "ERR:Term-lisp evaluation error: \"provide: loose: no load in progress\""))))

(ert-deftest tl-provide-a-second-load-cannot-claim-a-live-feature ()
  "A feature another load holds is an error naming that file."
  (let* ((first (tl-test--tls-file "(define (who-a) 1)\n(provide \"who\")"))
         (second (tl-test--tls-file "(define (who-b) 2)\n(provide \"who\")"))
         (env (tl-test--load-env)))
    (termlisp-eval (format "(load %S)" first) env)
    (should (equal (tl-test--eval-render (format "(load %S)" second) env)
                   (format
                    "ERR:Term-lisp evaluation error: \"provide: who is already provided by %s\""
                    (expand-file-name first))))
    ;; The losing load was rolled back with its transaction...
    (should (equal (tl-test--eval-render "(who-b)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: who-b\""))
    ;; ...and the winner is untouched.
    (should (equal (tl-test--eval-render "(who-a)" env) "1"))))

(ert-deftest tl-provide-twice-in-one-file-is-a-no-op ()
  "A file may stamp the same feature twice; the record carries it once."
  (let* ((file (tl-test--tls-file
                "(define (idem x) x)\n(provide \"idem\")\n(provide \"idem\")"))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render (format "(load %S)" file) env)
                   "Unit"))
    (should (equal (tl-load-record-features (car (tl-env-loads env)))
                   '("idem")))))

(ert-deftest tl-require-without-a-library-errors ()
  "A name no file provides is an error listing the searched directories."
  (let* ((termlisp-load-path (list "/nonexistent/tl-require-no-such-dir"))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render "(require \"nowhere\")" env)
                   "ERR:Term-lisp evaluation error: \"require: nothing provides nowhere (searched: /nonexistent/tl-require-no-such-dir)\""))))

(ert-deftest tl-require-a-file-that-provides-nothing-errors ()
  "A file that loads without providing the feature is rolled back."
  (let* ((dir (tl-test--library-dir
               '(("mute.tls" . "(define (mute-fn) 5)"))))
         (termlisp-load-path (list dir))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render "(require \"mute\")" env)
                   (format
                    "ERR:Term-lisp evaluation error: \"require: %s loaded without providing mute\""
                    (expand-file-name "mute.tls" dir))))
    (should (equal (tl-test--eval-render "(mute-fn)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: mute-fn\""))
    ;; The failed require journalled nothing; the prelude is all there is.
    (should (= (length (tl-env-loads env)) 1))))

(ert-deftest tl-require-a-self-requiring-file-errors ()
  "A file requiring the feature it is being loaded for is refused."
  (let* ((dir (tl-test--library-dir
               '(("loop.tls" . "(require \"loop\")\n(define (loop-fn) 9)"))))
         (termlisp-load-path (list dir))
         (env (tl-test--load-env)))
    (should (equal (tl-test--eval-render "(require \"loop\")" env)
                   "ERR:Term-lisp evaluation error: \"require: recursive load of loop\""))
    (should (equal (tl-test--eval-render "(loop-fn)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: loop-fn\""))
    (should (= (length (tl-env-loads env)) 1))))

(ert-deftest tl-remove-undoes-a-feature ()
  "A library may be removed by the feature it provided."
  (let* ((file (tl-test--tls-file
                "(define (by-name x) x)\n(provide \"by-name\")"))
         (env (tl-test--load-env)))
    (termlisp-eval (format "(load %S)" file) env)
    (should (equal (tl-test--eval-render "(require \"by-name\")" env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(remove \"by-name\")" env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(remove \"by-name\")" env)
                   "ERR:Term-lisp evaluation error: \"remove: by-name is not loaded\""))
    (should (equal (tl-test--eval-render "(by-name 1)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: by-name\""))))

(ert-deftest tl-remove-a-feature-names-the-enclosing-load-when-nested ()
  "A feature provided inside another load comes out with that load."
  (let* ((dir (tl-test--library-dir
               '(("inner.tls" . "(define (inner-fn x) x)\n(provide \"inner\")")
                 ("outer.tls" . "(require \"inner\")"))))
         (outer (expand-file-name "outer.tls" dir))
         (termlisp-load-path (list dir))
         (env (tl-test--load-env)))
    (termlisp-eval (format "(load %S)" outer) env)
    (should (equal (tl-test--eval-render "(remove \"inner\")" env)
                   (format
                    "ERR:Term-lisp evaluation error: \"remove: inner was loaded inside %s; remove that file to undo them both\""
                    outer)))
    (should (equal (tl-test--eval-render (format "(remove %S)" outer) env)
                   "Unit"))
    (should (equal (tl-test--eval-render "(inner-fn 1)" env)
                   "ERR:Term-lisp type error: \"Unknown symbol: inner-fn\""))))

(ert-deftest tl-repl-banner-prefers-feature-names ()
  "A library that provided a feature is listed by it."
  (let* ((file (tl-test--tls-file
                "(define (lib-id x) x)\n(provide \"geometry\")"))
         (env (termlisp-make-env nil)))
    (termlisp-load-prelude env)
    (termlisp-eval (format "(load %S)" file) env)
    (with-temp-buffer
      (setq-local termlisp-repl--env env)
      (setq-local termlisp-repl--options '(:type-check t))
      (should (string-match-p
               "(loaded: termlisp-prelude\\.tls, geometry)"
               (termlisp-repl--banner))))))

(ert-deftest tl-provide-non-string-argument-errors ()
  "A non-String argument is a type error naming the builtin."
  (let ((got (tl-test--render "(provide 42)" nil)))
    (should (string-prefix-p "ERR:" got))
    (should (string-match-p
             (regexp-quote "provide expects a String, got 42") got))))

(ert-deftest tl-require-non-string-argument-errors ()
  "A non-String argument is a type error naming the builtin."
  (let ((got (tl-test--render "(require 42)" nil)))
    (should (string-prefix-p "ERR:" got))
    (should (string-match-p
             (regexp-quote "require expects a String, got 42") got))))

;;; Examples quoted in the README

(tl-test-eval tl-readme-and-implies-or "(define (and-implies-or (Pair a b)) (Left a)) (and-implies-or (Pair 1 2))" "(Left 1)" '(:type-check t :elaborate t))
(tl-test-eval tl-readme-not-void-is-identity "(: not-void (Void -> Void)) (define (not-void v) v) (not-void Void)" "Void" '(:type-check t :elaborate t))
(tl-test-eval tl-readme-absurd-signals-when-reachable "(absurd Void)" "ERR:absurd: Void has no values, so this call is unreachable" '(:type-check t :elaborate t))
(tl-test-eval tl-readme-either-in-a-signature "(: g (Either Int String)) (define (g) (Right \"ok\")) (g)" "(Right ok)" '(:type-check t :elaborate t))


;;; A class parameter may pin its kind

;; `Functor' never said what its parameter ranges over; every instance
;; decided alone.  A parameter may now carry `(NAME : KIND)', which is
;; how `Functor : (* -> *) -> *' gets said -- and an instance at any
;; other kind is refused at its declaration rather than at the first
;; call that cannot resolve.  A parameter written any way other than
;; `(NAME : KIND)' is a typo, and is now read as one instead of being
;; swallowed as two extra parameters.

(tl-test-eval tl-class-a-higher-kinded-instance-resolves
  "(datatype ToyDict (ToyDict tof))
   (define (tof (ToyDict impl) x) (impl x))
   (class Toy ((f : (-> * *))) nil (tof (-> (f Int) Int)))
   (define ToyMaybeDict (ToyDict (lambda (x) 1)))
   (instance (Toy Maybe) ToyMaybeDict)
   (tof (Just 4))"
  "1" '(:type-check t :elaborate t))

(tl-test-reject tl-class-a-parameter-kind-refuses-a-proper-type-instance
  "(datatype ToyDict (ToyDict tof))
   (class Toy ((f : (-> * *))) nil (tof (-> Int Int)))
   (define ToyIntDict (ToyDict (lambda (x) x)))
   (instance (Toy Int) ToyIntDict)"
  "Kind error: instance of Toy is at a * where a (* -> *) is required"
  '(:type-check t :elaborate t))

(tl-test-reject tl-class-a-bare-parameter-annotation-is-refused
  "(class Toy (f : (-> * *)) nil (tof (-> Int Int)))"
  "Malformed parameter (-> * *) in class Toy; write it as (NAME : KIND)"
  '(:type-check t :elaborate t))

;;; The categorical tower: Monoid, Foldable, Traversable, lift-a2

;; Monoid: the identity rides in the record, so every verb takes the
;; dictionary explicitly and nothing needs elaboration.
(tl-test-eval tl-prelude-mempty-int "(mempty MonoidIntDict)" "0")
(tl-test-eval tl-prelude-mempty-list "(mempty MonoidListDict)" "Nil")
(tl-test-eval tl-prelude-mempty-string "(mempty MonoidStringDict)" "")
(tl-test-eval tl-prelude-mappend-int "(mappend MonoidIntDict 3 4)" "7")
(tl-test-eval tl-prelude-mappend-string "(mappend MonoidStringDict \"ab\" \"cd\")" "abcd")
(tl-test-eval tl-prelude-mappend-list
  "(mappend MonoidListDict (Cons 1 Nil) (Cons 2 Nil))" "(Cons 1 (Cons 2 Nil))")
(tl-test-eval tl-prelude-mconcat-int
  "(mconcat MonoidIntDict (Cons 1 (Cons 2 (Cons 3 Nil))))" "6")
(tl-test-eval tl-prelude-mconcat-list
  "(mconcat MonoidListDict (Cons (Cons 1 Nil) (Cons (Cons 2 Nil) Nil)))"
  "(Cons 1 (Cons 2 Nil))")
(tl-test-eval tl-prelude-mconcat-string
  "(mconcat MonoidStringDict (Cons \"ab\" (Cons \"cd\" Nil)))" "abcd")
(tl-test-eval tl-prelude-endo-composition
  "(run-endo (mappend MonoidEndoDict (Endo (lambda (x) (+ x 1))) (Endo (lambda (x) (* x 2)))) 5)"
  "11")
(tl-test-eval tl-prelude-endo-mempty "(run-endo (mempty MonoidEndoDict) 42)" "42")

;; Foldable: `foldr' is a method now, so its callers need the
;; elaborator to find the dictionary.
(tl-test-eval tl-prelude-foldr-maybe
  "(foldr (lambda (x acc) (+ x acc)) 0 (Just 5))" "5" '(:elaborate t))
(tl-test-eval tl-prelude-foldr-nothing
  "(foldr (lambda (x acc) (+ x acc)) 0 Nothing)" "0" '(:elaborate t))
(tl-test-eval tl-prelude-to-list-maybe "(to-list (Just 5))" "(Cons 5 Nil)" '(:elaborate t))
(tl-test-eval tl-prelude-length-maybe "(length (Just 5))" "1" '(:elaborate t))
(tl-test-eval tl-prelude-length-nil "(length Nil)" "0" '(:elaborate t))
(tl-test-eval tl-prelude-fold-map-int
  "(fold-map MonoidIntDict (lambda (x) (* x 2)) (Cons 1 (Cons 2 Nil)))" "6" '(:elaborate t))
(tl-test-eval tl-prelude-fold-map-list-maybe
  "(fold-map MonoidListDict (lambda (x) (Cons x Nil)) (Just 7))" "(Cons 7 Nil)" '(:elaborate t))
(tl-test-eval tl-prelude-fold-map-endo
  "(run-endo (fold-map MonoidEndoDict (lambda (x) (Endo (lambda (s) (string-append s x)))) (Cons \"a\" (Cons \"b\" Nil))) \"z\")"
  "zba" '(:elaborate t))

;; Traversable: the traversable dict matches the container, the
;; effect dict the computation it walks into.
(tl-test-eval tl-prelude-traverse-list-maybe
  "(traverse TraversableListDict ApplicativeMaybeDict (lambda (x) (Just (+ x 1))) (Cons 1 (Cons 2 Nil)))"
  "(Just (Cons 2 (Cons 3 Nil)))")
(tl-test-eval tl-prelude-traverse-list-maybe-short-circuit
  "(traverse TraversableListDict ApplicativeMaybeDict (lambda (x) (if (= x 2) Nothing (Just x))) (Cons 1 (Cons 2 Nil)))"
  "Nothing")
(tl-test-eval tl-prelude-traverse-list-list
  "(traverse TraversableListDict ApplicativeListDict (lambda (x) (Cons x (Cons (* x 10) Nil))) (Cons 1 (Cons 2 Nil)))"
  "(Cons (Cons 1 (Cons 2 Nil)) (Cons (Cons 1 (Cons 20 Nil)) (Cons (Cons 10 (Cons 2 Nil)) (Cons (Cons 10 (Cons 20 Nil)) Nil))))")
(tl-test-eval tl-prelude-traverse-maybe-just
  "(traverse TraversableMaybeDict ApplicativeMaybeDict (lambda (x) (Just x)) (Just 5))"
  "(Just (Just 5))")
(tl-test-eval tl-prelude-traverse-maybe-nothing
  "(traverse TraversableMaybeDict ApplicativeMaybeDict (lambda (x) (Just x)) Nothing)"
  "(Just Nothing)")
(tl-test-eval tl-prelude-sequence-a
  "(sequence-a TraversableListDict ApplicativeMaybeDict (Cons (Just 1) (Cons (Just 2) Nil)))"
  "(Just (Cons 1 (Cons 2 Nil)))")
(tl-test-eval tl-prelude-mapm-maybe-just
  "(mapm TraversableMaybeDict MaybeDict (lambda (x) (Just (+ x 1))) (Just 5))"
  "(Just (Just 6))")
(tl-test-eval tl-prelude-mapm-maybe-nothing
  "(mapm TraversableMaybeDict MaybeDict (lambda (x) (Just (+ x 1))) Nothing)"
  "(Just Nothing)")
(tl-test-eval tl-prelude-mapm-list
  "(mapm TraversableListDict MaybeDict (lambda (x) (Just (+ x 1))) (Cons 1 (Cons 2 Nil)))"
  "(Just (Cons 2 (Cons 3 Nil)))")
(tl-test-eval tl-prelude-sequence
  "(sequence TraversableListDict MaybeDict (Cons (Just 1) (Cons (Just 2) Nil)))"
  "(Just (Cons 1 (Cons 2 Nil)))")
(tl-test-eval tl-prelude-sequence-short-circuit
  "(sequence TraversableListDict MaybeDict (Cons (Just 1) (Cons Nothing Nil)))"
  "Nothing")

;; lift-a2: the Applicative method, elaborated for the dict-shaped
;; instances and called through its implementation where the
;; arguments are functions the elaborator's unifier cannot place.
(tl-test-eval tl-prelude-lift-a2-maybe
  "(lift-a2 (lambda (x y) (+ x y)) (Just 1) (Just 2))" "(Just 3)" '(:elaborate t))
(tl-test-eval tl-prelude-lift-a2-maybe-nothing
  "(lift-a2 (lambda (x y) (+ x y)) (Just 1) Nothing)" "Nothing" '(:elaborate t))
(tl-test-eval tl-prelude-lift-a2-list
  "(lift-a2 (lambda (x y) (Cons x (Cons y Nil))) (Cons 1 Nil) (Cons 2 Nil))"
  "(Cons (Cons 1 (Cons 2 Nil)) Nil)" '(:elaborate t))
(tl-test-eval tl-prelude-state-lift-a2-explicit
  "((state-lift-a2 (lambda (x y) (+ x y)) (state-return 1) (state-return 2)) 0)"
  "(Pair 3 0)")
(tl-test-eval tl-prelude-state-lift-a2-thread
  "((state-lift-a2 (lambda (x y) (+ x y)) (state-return 1) (state-get)) 7)"
  "(Pair 8 7)")
(tl-test-eval tl-prelude-reader-lift-a2-explicit
  "((reader-lift-a2 (lambda (x y) (+ x y)) (reader-return 1) (reader-return 2)) 5)"
  "3")

;; Reader verbs.
(tl-test-eval tl-prelude-asks "((asks (lambda (r) (+ r 1))) 5)" "6")
(tl-test-eval tl-prelude-local-asks
  "((local (lambda (r) (* r 10)) (asks (lambda (x) (+ x 1)))) 5)" "51")

;; The same tower with the default options: the explicit-dictionary
;; verbs work, the elaborated ones name the method they miss.
(tl-test-eval tl-prelude-tower-mappend-default "(mappend MonoidIntDict 3 4)" "7")
(tl-test-eval tl-prelude-tower-mconcat-default
  "(mconcat MonoidIntDict (Cons 1 (Cons 2 Nil)))" "3")
(tl-test-eval tl-prelude-tower-foldr-explicit-dict
  "(foldr FoldableListDict (lambda (x acc) (+ x acc)) 0 (Cons 1 (Cons 2 Nil)))" "3")
(tl-test-eval tl-prelude-tower-traverse-explicit-dicts
  "(traverse TraversableListDict ApplicativeMaybeDict (lambda (x) (Just x)) (Cons 1 Nil))"
  "(Just (Cons 1 Nil))")
(tl-test-eval tl-prelude-tower-asks-default "((asks (lambda (r) (+ r 1))) 5)" "6")

;; The walls: a non-dictionary where one belongs, and the methods
;; that need the elaborator's insertion.
(tl-test-reject tl-prelude-mappend-rejects-a-non-dictionary
  "(mappend Nil 1)" "Cannot apply mappend to Nil" '(:elaborate t))
(tl-test-reject tl-prelude-foldr-rejects-mismatched-element-types
  "(foldr (lambda (x acc) x) 0 (Just \"s\"))" "Cannot apply foldr" '(:elaborate t))
(tl-test-reject tl-prelude-length-rejects-a-non-container
  "(length \"abc\")" "Cannot apply length to" '(:elaborate t))

;;; Application: partial and surplus arguments

(tl-test-eval tl-app-lambda-under-is-pending
  "((lambda (x y) (Cons x y)) 1)" "#<partial>")
(tl-test-eval tl-app-lambda-under-typechecked
  "((lambda (x y) (Cons x y)) 1)" "#<partial>" '(:type-check t))
(tl-test-eval tl-app-lambda-under-completes
  "(((lambda (x y) (Cons x y)) 1) (Cons 2 Nil))" "(Cons 1 (Cons 2 Nil))")
(tl-test-eval tl-app-lambda-under-arithmetic
  "(((lambda (x y) (+ x y)) 1) 2)" "3")
(tl-test-eval tl-app-pending-then-two-more
  "(((lambda (x y z) (list x y z)) 1) 2 3)" "(Cons 1 (Cons 2 (Cons 3 Nil)))")
(tl-test-eval tl-app-nested-lambda-flat
  "((lambda (x) (lambda (y) (Cons x y))) 1 (Cons 2 Nil))" "(Cons 1 (Cons 2 Nil))")
(tl-test-eval tl-app-exact-lambda-is-unchanged
  "((lambda (x y) (Cons x y)) 1 (Cons 2 Nil))" "(Cons 1 (Cons 2 Nil))")
(tl-test-eval tl-app-zero-arg-lambda-is-unchanged "((lambda () 1))" "1")
(tl-test-reject tl-app-surplus-onto-a-value
  "((lambda (x) x) 1 2)" "Not a function")
(tl-test-eval tl-app-partial-inside-data
  "(Cons ((lambda (x y) (Cons x y)) 1) Nil)" "(Cons #<partial> Nil)")
(tl-test-eval tl-app-prelude-clause-under
  "((map-list (lambda (x) (+ x 1))) (Cons 1 Nil))" "(Cons 2 Nil)")
(tl-test-eval tl-app-state-get-flat "(state-get 5)" "(Pair 5 5)")
(tl-test-sub tl-app-named-under-completes
  "(define (add2 x y) (+ x y))" "((add2 1) 2)" "3")
(tl-test-sub tl-app-named-under-pending
  "(define (add2 x y) (+ x y))" "(add2 1)" "#<partial>")
(tl-test-sub tl-app-named-flat-over
  "(define (adder1 x) (lambda (y) (+ x y)))" "(adder1 1 2)" "3")
(tl-test-sub tl-app-named-clause-flat-over
  "(define (adder1 x) (lambda (y) (+ x y)))" "((adder1 1) 2)" "3")
(tl-test-sub tl-app-named-zero-arity-surplus
  "(define (get5) 5)" "(get5 1)" "ERR:Not a function: 5")
(tl-test-sub tl-app-rest-clause-absorbs-surplus
  "(define (resty x (:list xs)) (Pair x xs))" "(resty 1 2 3)" "(Pair 1 (2 3))")
(tl-test-sub tl-app-rest-clause-exact
  "(define (resty x (:list xs)) (Pair x xs))" "(resty 1)" "(Pair 1 nil)")

;;; Ziplist

(tl-test-eval tl-zip-pure "(ziplist-pure 5)" "(Ziplist (Cons 5 Nil))")
(tl-test-eval tl-zip-fmap
  "(fmap (lambda (x) (+ x 1)) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Ziplist (Cons 2 (Cons 3 Nil)))" '(:elaborate t))
(tl-test-eval tl-zip-ap-zips
  "(ap (Ziplist (Cons (lambda (x) (+ x 10)) (Cons (lambda (x) (* x 2)) Nil))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Ziplist (Cons 11 (Cons 4 Nil)))" '(:elaborate t))
(tl-test-eval tl-zip-ap-truncates
  "(ap (Ziplist (Cons (lambda (x) (+ x 10)) Nil)) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Ziplist (Cons 11 Nil))" '(:elaborate t))
(tl-test-eval tl-zip-lift-a2
  "(lift-a2 (lambda (x y) (+ x y)) (Ziplist (Cons 1 (Cons 2 Nil))) (Ziplist (Cons 10 (Cons 20 (Cons 30 Nil)))))"
  "(Ziplist (Cons 11 (Cons 22 Nil)))" '(:elaborate t))
(tl-test-eval tl-zip-lift-a2-calls-builtins-once
  "(lift-a2 + (Ziplist (Cons 1 (Cons 2 Nil))) (Ziplist (Cons 10 (Cons 20 Nil))))"
  "(Ziplist (Cons 11 (Cons 22 Nil)))" '(:elaborate t))
(tl-test-eval tl-zip-foldr
  "(foldr (lambda (x acc) (+ x acc)) 0 (Ziplist (Cons 1 (Cons 2 Nil))))"
  "3" '(:elaborate t))
(tl-test-eval tl-zip-length
  "(length (Ziplist (Cons 1 (Cons 2 Nil))))" "2" '(:elaborate t))
(tl-test-eval tl-zip-to-list
  "(to-list (Ziplist (Cons 1 (Cons 2 Nil))))" "(Cons 1 (Cons 2 Nil))" '(:elaborate t))

;;; Ziplist Traversable

(tl-test-eval tl-zip-traverse-maybe
  "(traverse TraversableZiplistDict ApplicativeMaybeDict (lambda (x) (Just (+ x 1))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Just (Ziplist (Cons 2 (Cons 3 Nil))))")
(tl-test-eval tl-zip-traverse-maybe-short-circuit
  "(traverse TraversableZiplistDict ApplicativeMaybeDict (lambda (x) (if (= x 2) Nothing (Just x))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "Nothing")
(tl-test-eval tl-zip-traverse-list
  "(traverse TraversableZiplistDict ApplicativeListDict (lambda (x) (Cons x (Cons (* x 10) Nil))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Cons (Ziplist (Cons 1 (Cons 2 Nil))) (Cons (Ziplist (Cons 1 (Cons 20 Nil))) (Cons (Ziplist (Cons 10 (Cons 2 Nil))) (Cons (Ziplist (Cons 10 (Cons 20 Nil))) Nil))))")
(tl-test-eval tl-zip-traverse-empty
  "(traverse TraversableZiplistDict ApplicativeMaybeDict (lambda (x) (Just x)) (Ziplist Nil))"
  "(Just (Ziplist Nil))")
(tl-test-eval tl-zip-traverse-through-ziplist-truncates
  "(traverse TraversableZiplistDict ApplicativeZiplistDict (lambda (x) (Ziplist (Cons x (Cons (* x 10) Nil)))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Ziplist (Cons (Ziplist (Cons 1 (Cons 2 Nil))) Nil))")
(tl-test-eval tl-zip-mapm-maybe
  "(mapm TraversableZiplistDict MaybeDict (lambda (x) (Just (+ x 1))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "(Just (Ziplist (Cons 2 (Cons 3 Nil))))")
(tl-test-eval tl-zip-mapm-maybe-short-circuit
  "(mapm TraversableZiplistDict MaybeDict (lambda (x) (if (= x 2) Nothing (Just x))) (Ziplist (Cons 1 (Cons 2 Nil))))"
  "Nothing")
(tl-test-eval tl-zip-sequence-a
  "(sequence-a TraversableZiplistDict ApplicativeMaybeDict (Ziplist (Cons (Just 1) (Cons (Just 2) Nil))))"
  "(Just (Ziplist (Cons 1 (Cons 2 Nil))))")
(tl-test-eval tl-zip-sequence
  "(sequence TraversableZiplistDict MaybeDict (Ziplist (Cons (Just 1) (Cons (Just 2) Nil))))"
  "(Just (Ziplist (Cons 1 (Cons 2 Nil))))")
(tl-test-eval tl-app-method-waiting-for-its-dictionary
  "(fmap (lambda (x) (+ x 1)) (Ziplist (Cons 1 Nil)))" "#<partial>")

(provide 'prelude-test)
;;; prelude-test.el ends here
