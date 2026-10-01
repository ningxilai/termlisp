;;; termlisp-test.el --- Tests for termlisp -*- lexical-binding: t; -*-

;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

(require 'ert)
(add-to-list 'load-path (expand-file-name ".." (file-name-directory load-file-name)))
(require 'termlisp)
(require 'termlisp-graph)

(ert-deftest base/env-defaults ()
  (let ((env (termlisp-make-env)))
    (should (tl-env-p env))
    (should (hash-table-p (tl-env-functions env)))
    (should (eq (tl-env-option env :phase) 'B))
    (should (eq (tl-env-option env :occurs-check) t))))

(ert-deftest base/env-option-override ()
  (let ((env (termlisp-make-env '(:fuel 10))))
    (should (= (tl-env-option env :fuel) 10))
    (should (eq (tl-env-option env :occurs-check) t))))

(ert-deftest base/env-option-nil-override ()
  (should-not (tl-env-option (termlisp-make-env '(:occurs-check nil)) :occurs-check))
  (should (eq (tl-env-option (termlisp-make-env) :missing 'fallback) 'fallback)))

(ert-deftest unify/atom-equal ()
  (should (car (tl-unify 'a 'a nil)))
  (should (null (car (tl-unify 'a 'b nil)))))

(ert-deftest unify/var-binding ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify x 1 nil)))
    (should (car r))
    (should (equal (tl-deref x (cdr r)) 1))))

(ert-deftest unify/structural ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify (list 'f x) (list 'f 2) nil)))
    (should (car r))
    (should (equal (tl-deref x (cdr r)) 2))))

(ert-deftest unify/occurs-check ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify x (list 'f x) nil t)))
    (should (null (car r)))))

(ert-deftest unify/mismatch ()
  (should (null (car (tl-unify (list 'f 1) (list 'g 1) nil))))
  (should (null (car (tl-unify 1 2 nil)))))

(ert-deftest unify/var-var ()
  (let* ((x (tl-make-lvar 'x))
         (y (tl-make-lvar 'y))
         (r (tl-unify x y nil)))
    (should (car r))
    (should (eq (tl-deref x (cdr r)) y))))

(ert-deftest unify/transitive-deref ()
  (let* ((x (tl-make-lvar 'x))
         (y (tl-make-lvar 'y))
         (r (tl-unify x y nil))
         (r2 (tl-unify y 5 (cdr r))))
    (should (car r2))
    (should (equal (tl-deref x (cdr r2)) 5))))

(ert-deftest unify/already-bound-consistency ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify x 1 nil)))
    (should (car (tl-unify x 1 (cdr r))))
    (should (null (car (tl-unify x 2 (cdr r)))))))

(ert-deftest unify/occurs-off-by-default ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify x (list 'f x) nil)))
    (should (car r))))

(ert-deftest unify/improper-list ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify (cons 'f x) (cons 'f 9) nil)))
    (should (car r))
    (should (equal (tl-deref x (cdr r)) 9))))

(ert-deftest unify/failure-contract ()
  (let* ((x (tl-make-lvar 'x))
         (y (tl-make-lvar 'y))
         (r (tl-unify (list 1 x) (list 2 y) nil)))
    (should (null (car r)))
    (should (null (cdr r)))))

(ert-deftest reader/single-form ()
  (should (equal (termlisp-parse "(id 42)") '((id 42)))))

(ert-deftest reader/multiple-forms ()
  (should (equal (termlisp-parse "(a) (b c)") '((a) (b c)))))

(ert-deftest reader/comments-and-whitespace ()
  (should (equal (termlisp-parse ";; hi\n(a)\n  (b)") '((a) (b)))))

(ert-deftest reader/keyword-pattern ()
  (should (equal (termlisp-parse "(:literal true)")
                 '((:literal true)))))

(ert-deftest reader/unbalanced-signals ()
  (should-error (termlisp-parse "(a b") :type 'termlisp-parse-error))

(ert-deftest reader/extra-close-signals ()
  (should-error (termlisp-parse "(a))") :type 'termlisp-parse-error))

(ert-deftest reader/empty-and-whitespace ()
  (should (null (termlisp-parse "")))
  (should (null (termlisp-parse "   \n\t "))))

(ert-deftest reader/trailing-vertical-tab ()
  (should (equal (termlisp-parse "(a)\v") '((a)))))

(ert-deftest reader/rejects-circular ()
  (should-error (termlisp-parse "(#1=(a . #1#))") :type 'termlisp-parse-error))

(ert-deftest reader/parse-file ()
  (let ((file (make-temp-file "termlisp-reader-" nil ".tls")))
    (unwind-protect
        (progn
          (with-temp-file file (insert "(a)\n(b c)\n"))
          (should (equal (termlisp-parse-file file) '((a) (b c)))))
      (delete-file file))))

(ert-deftest machine/thunk-accessors ()
  (let ((t0 (tl-make-thunk '(f 1) '((x . 1)))))
    (should (tl-thunk-p t0))
    (should (equal (tl-thunk-expr t0) '(f 1)))
    (should (null (tl-thunk-forced-p t0)))))

(ert-deftest machine/value-equal-atoms ()
  (should (tl-value-equal 1 1 #'identity))
  (should-not (tl-value-equal 1 2 #'identity))
  (should (tl-value-equal 'Foo 'Foo #'identity)))

(ert-deftest machine/value-equal-constructors ()
  (should (tl-value-equal '(Pair 1 2) '(Pair 1 2) #'identity))
  (should-not (tl-value-equal '(Pair 1 2) '(Pair 1 3) #'identity))
  (should-not (tl-value-equal '(Pair 1 2) '(Cons 1 2) #'identity)))

(ert-deftest machine/true-value-p ()
  (should (tl-true-value-p 'True))
  (should-not (tl-true-value-p 'False)))

(defun tl-test-force (v)
  (if (tl-thunk-p v)
      (progn (setf (tl-thunk-forced-p v) t) (tl-thunk-value v))
    v))

(ert-deftest machine/value-equal-forces-thunk-fields ()
  (let* ((mk (lambda (val) (let ((tk (tl-make-thunk nil nil)))
                             (setf (tl-thunk-value tk) val) tk)))
         (a (funcall mk 'X))
         (b (funcall mk 'X))
         (c (funcall mk 'Y)))
    (should (tl-value-equal (list 'Pair a) (list 'Pair b) #'tl-test-force))
    (should-not (tl-value-equal (list 'Pair a) (list 'Pair c) #'tl-test-force))))

(ert-deftest machine/value-equal-nested ()
  (should (tl-value-equal '(Pair (Pair A B)) '(Pair (Pair A B)) #'identity))
  (should (tl-value-equal '(Pair "x") '(Pair "x") #'identity))
  (should (tl-value-equal '(Pair 1.5) '(Pair 1.5) #'identity))
  (should-not (tl-value-equal '(Pair "x") '(Pair "y") #'identity)))

(ert-deftest machine/value-equal-nullary-and-mismatch ()
  (should (tl-value-equal 'True 'True #'identity))
  (should-not (tl-value-equal 'True 'False #'identity))
  (should-not (tl-value-equal 'True '(True) #'identity)))

(ert-deftest machine/lookup ()
  (let ((termlisp--current-env (termlisp-make-env)))
    (setf (tl-env-globals termlisp--current-env) '((g . 1)))
    (should (equal (cdr (tl-lookup 'g '())) 1))
    (should (equal (cdr (tl-lookup 'g '((g . 2)))) 2))
    (should (null (tl-lookup 'missing '())))))

(ert-deftest pattern/parse-shapes ()
  (should (equal (tl-pattern-parse 'x) '(var . x)))
  (should (equal (tl-pattern-parse '_) '(wild)))
  (should (equal (tl-pattern-parse '(:literal foo)) '(lit foo)))
  (should (equal (tl-pattern-parse '(:list rest)) '(rest . rest)))
  (should (equal (tl-pattern-parse '(Pair a b))
                 '(con Pair (var . a) (var . b)))))

(defun tl-test-ctx ()
  (tl-make-match-ctx
   :force #'identity
   :lit-eval #'identity
   :guard-eval (lambda (e _b) e)
   :lambda-value #'identity))

(ert-deftest pattern/match-var ()
  (let* ((p (tl-pattern-parse 'x))
         (r (tl-match p 5 nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'x (cdr r))) 5))))

(ert-deftest pattern/match-wild ()
  (should (car (tl-match (tl-pattern-parse '_) 5 nil (tl-test-ctx)))))

(ert-deftest pattern/match-constructor ()
  (let* ((p (tl-pattern-parse '(Pair a b)))
         (r (tl-match p '(Pair 1 2) nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'a (cdr r))) 1))
    (should (equal (cdr (assq 'b (cdr r))) 2))))

(ert-deftest pattern/match-constructor-fail ()
  (should (null (tl-match (tl-pattern-parse '(Pair a b)) '(Cons 1 2)
                          nil (tl-test-ctx)))))

(ert-deftest pattern/match-nullary-constructor ()
  (should (car (tl-match (tl-pattern-parse '(True)) 'True nil (tl-test-ctx))))
  (should-not (tl-match (tl-pattern-parse '(True)) 'False nil (tl-test-ctx))))

(ert-deftest pattern/match-literal ()
  (should (car (tl-match (tl-pattern-parse '(:literal foo)) 'foo nil (tl-test-ctx))))
  (should-not (tl-match (tl-pattern-parse '(:literal foo)) 'bar nil (tl-test-ctx))))

(ert-deftest pattern/match-nonlinear ()
  (let* ((p (tl-pattern-parse '(Pair a a))))
    (should (car (tl-match p '(Pair 1 1) nil (tl-test-ctx))))
    (should-not (tl-match p '(Pair 1 2) nil (tl-test-ctx)))))

(ert-deftest pattern/match-rest ()
  (let* ((p (tl-pattern-parse '(:list rest)))
         (r (tl-match-seq (list p) '(1 2 3) nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'rest (cdr r))) '(1 2 3)))))

(ert-deftest pattern/match-guard ()
  (let* ((p (tl-pattern-parse '(guard x True)))
         (r (tl-match p 'anything nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'x (cdr r))) 'anything)))
  (should-not (tl-match (tl-pattern-parse '(guard x False)) 'anything nil (tl-test-ctx))))

(ert-deftest pattern/match-or ()
  (let ((p (tl-pattern-parse '(or (True) (False)))))
    (should (car (tl-match p 'True nil (tl-test-ctx))))
    (should (car (tl-match p 'False nil (tl-test-ctx))))
    (should-not (tl-match p 'Other nil (tl-test-ctx)))))

(ert-deftest pattern/match-and ()
  (should (car (tl-match (tl-pattern-parse '(and (Pair a b) (Pair a b)))
                         '(Pair 1 2) nil (tl-test-ctx))))
  (should-not (tl-match (tl-pattern-parse '(and (Pair a b) a))
                        '(Pair 1 2) nil (tl-test-ctx))))

(ert-deftest pattern/match-lambda ()
  (let* ((p (tl-pattern-parse '(:lambda f)))
         (r (tl-match p 'some-fn nil (tl-test-ctx))))
    (should (car r))
    (should (eq (cdr (assq 'f (cdr r))) 'some-fn))))

(ert-deftest pattern/guard-sees-bindings ()
  "The guard expression is evaluated with the sub-pattern's bindings."
  (let ((ctx (tl-make-match-ctx
              :force #'identity :lit-eval #'identity
              :guard-eval (lambda (e b) (cdr (assq e b)))
              :lambda-value #'identity)))
    (should (car (tl-match (tl-pattern-parse '(guard x x)) 'True nil ctx)))
    (should-not (tl-match (tl-pattern-parse '(guard x x)) 'False nil ctx))))

(ert-deftest pattern/match-seq-arity ()
  (let ((p (list (tl-pattern-parse 'a) (tl-pattern-parse 'b))))
    (should-not (tl-match-seq p '(1) nil (tl-test-ctx)))
    (should-not (tl-match-seq p '(1 2 3) nil (tl-test-ctx)))
    (should (car (tl-match-seq p '(1 2) nil (tl-test-ctx))))))

(ert-deftest pattern/rest-must-be-last ()
  (should-error
   (tl-match-seq (list (tl-pattern-parse '(:list r)) (tl-pattern-parse 'x))
                 '(1 2 3) nil (tl-test-ctx))
   :type 'termlisp-error))

(ert-deftest pattern/or-no-binding-leak ()
  "A failed `or' alternative must not leak its bindings into the next."
  (let* ((p (tl-pattern-parse '(or (Pair a (True)) (Pair b c))))
         (r (tl-match p '(Pair 1 2) nil (tl-test-ctx))))
    (should (car r))
    (should (null (assq 'a (cdr r))))
    (should (equal (cdr (assq 'b (cdr r))) 1))
    (should (equal (cdr (assq 'c (cdr r))) 2))))

(ert-deftest builtins/registry ()
  (should (tl-builtin-p 'eq))
  (should (tl-builtin-p '+))
  (should-not (tl-builtin-p 'nope)))

(ert-deftest builtins/eq ()
  (should (eq (funcall (gethash 'eq tl-builtins) '(1 1)) 'True))
  (should (eq (funcall (gethash 'eq tl-builtins) '(1 2)) 'False)))

(ert-deftest builtins/arith ()
  (should (= (funcall (gethash '+ tl-builtins) '(2 3)) 5))
  (should (= (funcall (gethash '- tl-builtins) '(7 3)) 4))
  (should (= (funcall (gethash '* tl-builtins) '(2 3)) 6))
  (should (eq (funcall (gethash '< tl-builtins) '(1 2)) 'True)))

(ert-deftest builtins/less-than-false ()
  (should (eq (funcall (gethash '< tl-builtins) '(2 1)) 'False)))

(ert-deftest builtins/arith-arity-and-type ()
  (should-error (funcall (gethash '+ tl-builtins) '(1)) :type 'termlisp-type-error)
  (should-error (funcall (gethash '+ tl-builtins) '(1 2 3)) :type 'termlisp-type-error)
  (should-error (funcall (gethash '+ tl-builtins) '(a b)) :type 'termlisp-type-error))

(require 'termlisp-eval)

(ert-deftest eval/atom-and-symbol ()
  (should (equal (termlisp-eval "42") 42))
  (should (eq (termlisp-eval "Foo") 'Foo)))

(ert-deftest eval/constant ()
  (should (equal (termlisp-eval "(define x 5) x") 5)))

(ert-deftest eval/lambda-immediate ()
  (should (equal (termlisp-eval "((lambda (x) x) 42)") 42)))

(ert-deftest eval/constructor-lazy ()
  (should (equal (termlisp-value->string (termlisp-eval "(Pair 1 2)"))
                 "(Pair 1 2)")))

(ert-deftest eval/define-function ()
  (should (equal (termlisp-eval "(define (id x) x) (id 42)") 42)))

(ert-deftest eval/if-clauses ()
  (should (eq (termlisp-eval
               "(datatype Bool (True) (False))
                (define (if (True) a b) a)
                (define (if (False) a b) b)
                (if True yes no)")
              'yes)))

(ert-deftest eval/pattern-destructure ()
  (should (eq (termlisp-eval
               "(datatype Pair (Pair a b))
                (define (fst (Pair a b)) a)
                (fst (Pair hello world))")
              'hello)))

(ert-deftest eval/open-constructor ()
  (should (equal (termlisp-value->string (termlisp-eval "(Foo 1 (Bar 2))"))
                 "(Foo 1 (Bar 2))")))

(ert-deftest eval/match-failure-signals ()
  (should-error (termlisp-eval "(define (f (True)) 1) (f (False))")
                :type 'termlisp-eval-error))

(ert-deftest eval/annotations-ignored ()
  (should (equal (termlisp-eval "(: id (a -> a)) (define (id x) x) (id 7)") 7)))

(ert-deftest eval/tco-deep-recursion ()
  "A tail-recursive loop of 100000 iterations must not overflow the stack."
  (let ((env (termlisp-make-env '(:fuel 10000000))))
    (should (= (termlisp-eval
                "(datatype Bool (True) (False))
                 (define (if (True) a b) a)
                 (define (if (False) a b) b)
                 (define (loop n acc)
                   (if (eq n 0) acc (loop (- n 1) (+ acc 1))))
                 (loop 100000 0)"
                env)
               100000))))

(ert-deftest eval/laziness-shares ()
  (should (= (termlisp-eval
              "(define (id x) x)
               (define (bump n) (+ n 1))
               (+ (id (bump 0)) (id (bump 0)))")
             2)))

(ert-deftest api/value->string ()
  (should (equal (termlisp-value->string '(Pair 1 2)) "(Pair 1 2)"))
  (should (equal (termlisp-value->string 'Foo) "Foo")))

(ert-deftest eval/lambda-as-value ()
  (should (equal (termlisp-eval
                  "(define (apply1 f x) (f x))
                   (apply1 (lambda (y) (+ y 1)) 41)")
                 42))
  (should (equal (termlisp-eval
                  "(define (mk x) (lambda (y) (+ x y)))
                   ((mk 5) 10)")
                 15)))

(ert-deftest eval/named-function-as-value ()
  (should (equal (termlisp-eval
                  "(define (apply1 f x) (f x))
                   (define (inc y) (+ y 1))
                   (apply1 inc 41)")
                 42)))

(ert-deftest eval/lazy-result-forceable-after-return ()
  "A lazy result returned by `termlisp-eval' must still be forceable."
  (should (equal (termlisp-value->string
                  (termlisp-eval "(define (f x) x) (Pair (f 1) (f 2))"))
                 "(Pair 1 2)")))

(ert-deftest eval/nullary-constructor-pattern ()
  (should (equal (termlisp-value->string
                  (termlisp-eval
                   "(datatype Nat (Zero) (Succ Nat))
                    (define (plus Zero b) b)
                    (define (plus (Succ a) b) (Succ (plus a b)))
                    (plus (Succ Zero) (Succ Zero))"))
                 "(Succ (Succ Zero))")))

(ert-deftest prelude/booleans ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(if True 1 2)" env) 1))
    (should (eq (termlisp-eval "(if False 1 2)" env) 2))
    (should (eq (termlisp-eval "(not True)" env) 'False))
    (should (eq (termlisp-eval "(and True False)" env) 'False))
    (should (eq (termlisp-eval "(and True True)" env) 'True))
    (should (eq (termlisp-eval "(or True False)" env) 'True))
    (should (eq (termlisp-eval "(or False False)" env) 'False))))

(ert-deftest prelude/pairs ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(car (cons A B))" env) 'A))
    (should (eq (termlisp-eval "(cdr (cons A B))" env) 'B))))

(ert-deftest prelude/peano ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(plus two two)" env))
                   "(Succ (Succ (Succ (Succ Zero))))"))))

(ert-deftest prelude/map-lambda ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(map Foo (lambda (a) (Wrap a)))" env))
                   "(Wrap Foo)"))))

(ert-deftest prelude/short-circuit ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(and False (boom))" env) 'False))
    (should (eq (termlisp-eval "(or True (boom))" env) 'True))
    (should (eq (termlisp-eval "(not False)" env) 'True))))

(ert-deftest prelude/plus-identities ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(plus one zero)" env))
                   "(Succ Zero)"))
    (should (equal (termlisp-value->string (termlisp-eval "(plus zero one)" env))
                   "(Succ Zero)"))))

(ert-deftest prelude/map-named-function ()
  (let ((env (termlisp-load-prelude)))
    (termlisp-eval "(define (this-is a) (This Is a))" env)
    (should (equal (termlisp-value->string
                    (termlisp-eval "(map Foo this-is)" env))
                   "(This Is Foo)"))))

(ert-deftest monad/maybe-return ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(monad-return MaybeDict 5)" env))
                   "(Just 5)"))))

(ert-deftest monad/maybe-bind-just ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (Just 3) (lambda (x) (Just (+ x 1))))" env))
                   "(Just 4)"))))

(ert-deftest monad/maybe-bind-nothing ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(monad-bind MaybeDict Nothing (lambda (x) (Just x)))" env)
                'Nothing))))

(ert-deftest monad/list-return-and-bind ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(monad-return ListDict 1)" env))
                   "(Cons 1 Nil)"))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (Cons 1 (Cons 2 Nil)) (lambda (x) (Cons (+ x 10) Nil)))" env))
                   "(Cons 11 (Cons 12 Nil))"))))

(ert-deftest prelude/load-prelude-returns-env ()
  (let ((env (termlisp-make-env)))
    (should (eq (termlisp-load-prelude env) env))))

(ert-deftest laziness/unused-argument-not-evaluated ()
  "An argument to a function that ignores it is never forced."
  (tl-register-builtin 'boom2
    (lambda (_args) (signal 'termlisp-eval-error '("boom"))))
  (unwind-protect
      (should (eq (termlisp-eval
                   "(define (const a b) a)
                    (const 1 (boom2))")
                  1))
    (remhash 'boom2 tl-builtins)))

(ert-deftest laziness/sharing-via-memoization ()
  "A thunk bound to a name is forced at most once (observed via a counter)."
  (let ((count 0))
    (tl-register-builtin 'tick2
      (lambda (_args) (setq count (1+ count)) 'True))
    (unwind-protect
        (progn
          (should (eq (termlisp-eval
                       "(define (dup x) (Pair x x))
                        (define (used p) (eq (car p) (cdr p)))
                        (used (dup (tick2)))"
                       (termlisp-load-prelude))
                      'True))
          (should (= count 1)))
      (remhash 'tick2 tl-builtins))))

(ert-deftest tco/mutual-recursion ()
  "Mutually recursive tail calls must not overflow."
  (let ((env (termlisp-load-prelude (termlisp-make-env '(:fuel 10000000)))))
    (termlisp-eval
     "(define (evenp n) (if (eq n 0) True (oddp (- n 1))))
      (define (oddp n) (if (eq n 0) False (evenp (- n 1))))"
     env)
    (should (eq (termlisp-eval "(evenp 20000)" env) 'True))
    (should (eq (termlisp-eval "(evenp 19999)" env) 'False))))

(ert-deftest tco/large-accumulator ()
  "A deep accumulator loop must not overflow the Elisp stack."
  (let ((env (termlisp-load-prelude (termlisp-make-env '(:fuel 10000000)))))
    (termlisp-eval
     "(define (sum n acc) (if (eq n 0) acc (sum (- n 1) (+ acc n))))"
     env)
    (should (= (termlisp-eval "(sum 5000 0)" env) 12502500))))

(ert-deftest acceptance/examples ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval-file
                 (expand-file-name "examples/bool.tls" termlisp--directory)
                 env)
                'booleans-work)))
  (should (equal (termlisp-value->string
                  (termlisp-eval-file
                   (expand-file-name "examples/nat.tls" termlisp--directory)))
                 "(Succ (Succ (Succ Zero)))")))

(ert-deftest reader/trailing-comment ()
  (should (equal (termlisp-parse "(a) ;; trailing") '((a))))
  (should (equal (termlisp-parse "(a) ;; trailing\n") '((a))))
  (should (null (termlisp-parse ";; only a comment")))
  (should (equal (termlisp-eval "(define x 5) ;; set x") 5)))

(ert-deftest value/deep-structure-does-not-overflow ()
  "Rendering and comparing deep values must not overflow the Elisp stack."
  (let ((env (termlisp-load-prelude)))
    (termlisp-eval
     "(define (count n) (if (eq n 0) Zero (Succ (count (- n 1)))))" env)
    (should (stringp (termlisp-value->string (termlisp-eval "(count 2000)" env))))
    (should (eq (termlisp-eval "(eq (count 2000) (count 2000))" env) 'True))
    (should (eq (termlisp-eval "(eq (count 2000) (count 1999))" env) 'False))))

(ert-deftest eval/open-datatype-extension ()
  (should (equal (termlisp-value->string
                  (termlisp-eval
                   "(datatype open Expr (Lit Int))
                    (datatype-extension Expr (Add Expr Expr))
                    (define (eval-expr (Lit n)) n)
                    (eval-expr (Lit 7))"))
                 "7"))
  (should-error (termlisp-eval
                 "(datatype Closed (A))
                  (datatype-extension Closed (B))")
                :type 'termlisp-eval-error)
  (should-error (termlisp-eval
                 "(datatype open Expr (Lit Int))
                  (define (f (Lit n)) n)
                  (f (Other 1))")
                :type 'termlisp-eval-error))

(ert-deftest eval/pattern-forms-end-to-end ()
  (should (equal (termlisp-value->string
                  (termlisp-eval
                   "(define (grab a (:list rest)) (Pair a rest))
                    (grab 1 2 3)"))
                 "(Pair 1 (2 3))"))
  (should (eq (termlisp-eval
               "(datatype Bool (True) (False))
                (define (zero? (guard n (eq n 0))) (True))
                (zero? 0)")
              'True))
  (should-error (termlisp-eval
                 "(datatype Bool (True) (False))
                  (define (zero? (guard n (eq n 0))) (True))
                  (zero? 5)")
                :type 'termlisp-eval-error)
  (should (eq (termlisp-eval
               "(datatype Bool (True) (False))
                (define (is-zero (:literal 0)) (True))
                (is-zero 0)")
              'True))
  (should (eq (termlisp-eval
               "(datatype Bool (True) (False))
                (define (p (or (True) (False))) yes)
                (p (False))")
              'yes)))

(require 'termlisp-types)

(ert-deftest type/representation ()
  (should (tl-type-p (tl-fresh-tvar)))
  (should (tl-type-p (tl-tint)))
  (should (equal (tl-tcon-name (tl-tint)) 'Int))
  (should (equal (tl-tcon-args (tl-tint)) nil)))

(ert-deftest type/unify-atoms ()
  (should (car (tl-unify-types (tl-tint) (tl-tint) nil)))
  (should (null (car (tl-unify-types (tl-tint) (tl-tstring) nil)))))

(ert-deftest type/unify-variable ()
  (let* ((a (tl-fresh-tvar))
         (r (tl-unify-types a (tl-tint) nil)))
    (should (car r))
    (should (equal (tl-deref a (cdr r)) (tl-tint)))))

(ert-deftest type/unify-application ()
  (let* ((a (tl-fresh-tvar))
         (r (tl-unify-types (tl-tcon 'List (list a)) (tl-tcon 'List (list (tl-tint))) nil)))
    (should (car r))
    (should (equal (tl-deref a (cdr r)) (tl-tint)))))

(ert-deftest type/unify-occurs ()
  (let* ((a (tl-fresh-tvar))
         (r (tl-unify-types a (tl-tcon 'List (list a)) nil)))
    (should (null (car r)))))

(ert-deftest type/unify-var-var ()
  (let* ((a (tl-fresh-tvar))
         (b (tl-fresh-tvar))
         (r (tl-unify-types a b nil)))
    (should (car r))
    (should (eq (tl-deref a (cdr r)) b))))

(ert-deftest type/unify-arity-mismatch ()
  (should (null (car (tl-unify-types (tl-tcon 'List (list (tl-tint)))
                                     (tl-tcon 'List nil) nil))))
  (should (null (car (tl-unify-types (tl-tcon 'List (list (tl-tint)))
                                     (tl-tcon 'Maybe (list (tl-tint))) nil)))))

(ert-deftest type/unify-failure-contract ()
  (let* ((a (tl-fresh-tvar))
         (input (list (cons a (tl-tint))))
         (r (tl-unify-types a (tl-tstring) input)))
    ;; failure returns (nil . nil) and does not mutate the input bindings
    (should (null (car r)))
    (should (null (cdr r)))
    (should (equal input (list (cons a (tl-tint)))))))

(ert-deftest type/unify-occurs-through-binding ()
  (let* ((a (tl-fresh-tvar))
         (b (tl-fresh-tvar))
         (b1 (cdr (tl-unify-types b a nil)))
         (r (tl-unify-types a (tl-tcon 'List (list b)) b1)))
    (should (null (car r)))))

(ert-deftest type/parse-atom ()
  (should (equal (tl-type-parse 'Int) (tl-tint)))
  (should (equal (tl-tcon-name (tl-type-parse 'Int)) 'Int)))

(ert-deftest type/parse-arrow ()
  (let ((ty (tl-type-parse '(a -> a))))
    (should (tl-tcon-p ty))
    (should (eq (tl-tcon-name ty) '->))
    (let ((args (tl-tcon-args ty)))
      (should (eq (nth 0 args) (nth 1 args))))))

(ert-deftest type/parse-arrow-right-assoc ()
  (let* ((ty (tl-type-parse '(a -> b -> c)))
         (args (tl-tcon-args ty)))
    (should (tl-tcon-p (nth 1 args)))
    (should (eq (tl-tcon-name (nth 1 args)) '->))))

(ert-deftest type/parse-application ()
  (let* ((ty (tl-type-parse '(List a)))
         (args (tl-tcon-args ty)))
    (should (eq (tl-tcon-name ty) 'List))
    (should (tl-tvar-p (nth 0 args)))))

(ert-deftest type/parse-scheme ()
  (let ((sc (tl-type-parse-scheme '(a -> a))))
    (should (tl-tscheme-p sc))
    (should (= (length (tl-tscheme-vars sc)) 1))))

(ert-deftest type/free-tvars ()
  (let* ((a (tl-fresh-tvar))
         (ty (tl-tarrow a (tl-tint))))
    (should (memq a (tl-free-tvars ty)))
    (should (= (length (tl-free-tvars ty)) 1))))

(ert-deftest type/free-tvars-head-position ()
  "A variable in head position is a free variable."
  (let* ((f (tl-fresh-tvar))
         (a (tl-fresh-tvar))
         (vars (tl-free-tvars (tl-tcon f (list a)))))
    (should (memq f vars))
    (should (memq a vars))
    (should (= (length vars) 2))))

(ert-deftest type/parse-malformed ()
  (should-error (tl-type-parse '(a ->)) :type 'termlisp-type-error)
  (should-error (tl-type-parse '(-> a)) :type 'termlisp-type-error)
  (should-error (tl-type-parse '(->)) :type 'termlisp-type-error)
  (should-error (tl-type-parse 42) :type 'termlisp-type-error))

(ert-deftest type/parse-independent ()
  "Separate parses must not share type variables."
  (let* ((t1 (tl-type-parse '(a -> a)))
         (t2 (tl-type-parse '(a -> a))))
    (should-not (eq (nth 0 (tl-tcon-args t1)) (nth 0 (tl-tcon-args t2))))))

(ert-deftest type/parse-case-sensitive ()
  (should (tl-tcon-p (tl-type-parse 'A)))
  (should (eq (tl-tcon-name (tl-type-parse 'A)) 'A))
  (should (tl-tvar-p (tl-type-parse 'a))))

(ert-deftest type/parse-prefix-arrow ()
  (let ((ty (tl-type-parse '(-> a b))))
    (should (tl-tcon-p ty))
    (should (eq (tl-tcon-name ty) '->))
    (should (tl-tvar-p (nth 0 (tl-tcon-args ty))))
    (should (tl-tvar-p (nth 1 (tl-tcon-args ty)))))
  (let ((ty (tl-type-parse '(-> a b c))))
    (should (eq (tl-tcon-name ty) '->))
    (should (eq (tl-tcon-name (nth 1 (tl-tcon-args ty))) '->))))

(ert-deftest type/subst ()
  (let* ((a (tl-fresh-tvar))
         (ty (tl-tarrow a a))
         (sub (list (cons a (tl-tint)))))
    (should (equal (tl-type-subst ty sub) (tl-tarrow (tl-tint) (tl-tint))))))

(ert-deftest type/subst-head-position ()
  "A variable in the head of an application is substituted."
  (let* ((f (tl-fresh-tvar))
         (g (tl-fresh-tvar))
         (a (tl-fresh-tvar))
         (ty (tl-tcon f (list a)))
         (sub (list (cons f g))))
    (should (eq (tl-tcon-name (tl-type-subst ty sub)) g))
    (should (eq (car (tl-tcon-args (tl-type-subst ty sub))) a))))

(ert-deftest type/subst-is-shallow ()
  "Substitution replaces a variable once, without chasing further bindings."
  (let* ((a (tl-fresh-tvar))
         (b (tl-fresh-tvar))
         (ty (tl-tcon 'Wrap (list a)))
         (sub (list (cons a b) (cons b (tl-tint)))))
    (should (equal (tl-type-subst ty sub)
                   (tl-tcon 'Wrap (list b))))))

(ert-deftest type/generalize-instantiate ()
  (let* ((a (tl-fresh-tvar))
         (ty (tl-tarrow a a))
         (sc (tl-generalize ty nil))
         (i1 (tl-instantiate sc))
         (i2 (tl-instantiate sc)))
    (should (tl-tscheme-p sc))
    (should (= (length (tl-tscheme-vars sc)) 1))
    (should-not (eq (nth 0 (tl-tcon-args i1)) (nth 0 (tl-tcon-args i2))))))

(ert-deftest type/generalize-respects-env ()
  (let* ((a (tl-fresh-tvar))
         (sc (tl-generalize (tl-tarrow a a) (list a))))
    (should (null (tl-tscheme-vars sc)))))

(ert-deftest type/apply-bindings ()
  (let* ((a (tl-fresh-tvar))
         (b (tl-fresh-tvar))
         (binds (list (cons a (tl-tint)) (cons b a))))
    (should (equal (tl-apply-bindings b binds) (tl-tint)))))

(ert-deftest type/apply-bindings-recurses-into-result ()
  "Apply-bindings chases a variable bound to a constructor with variables."
  (let* ((a (tl-fresh-tvar))
         (b (tl-fresh-tvar))
         (binds (list (cons a (tl-tarrow b b)) (cons b (tl-tint)))))
    (should (equal (tl-apply-bindings a binds)
                   (tl-tarrow (tl-tint) (tl-tint))))))

(ert-deftest type/compose-bindings ()
  (let* ((a (tl-fresh-tvar))
         (b (tl-fresh-tvar))
         (b1 (list (cons a b)))
         (b2 (list (cons b (tl-tint))))
         (c (tl-compose-bindings b1 b2)))
    (should (equal (tl-apply-bindings a c) (tl-tint)))))

(ert-deftest type/compose-bindings-overlap ()
  (let* ((a (tl-fresh-tvar)) (b (tl-fresh-tvar))
         (b1 (list (cons a b)))
         (b2 (list (cons a (tl-tint)) (cons b (tl-tstring))))
         (c (tl-compose-bindings b1 b2)))
    ;; a resolves through b1 then b2 => String
    (should (equal (tl-apply-bindings a c) (tl-tstring)))
    ;; exactly one cell for a
    (should (= (length (cl-remove-if-not (lambda (cell) (eq (car cell) a)) c)) 1))))

(ert-deftest type/compose-bindings-no-growth ()
  (let* ((a (tl-fresh-tvar)) (b (tl-fresh-tvar))
         (c (tl-compose-bindings (list (cons a b)) (list (cons b (tl-tint))))))
    (dotimes (_ 5) (setq c (tl-compose-bindings c (list (cons b (tl-tint))))))
    (should (< (length c) 5))))

(ert-deftest type/compose-bindings-cycle-safe ()
  "Composing inverse bindings must not create a self-binding that hangs."
  (let* ((a (tl-fresh-tvar)) (b (tl-fresh-tvar))
         (c (tl-compose-bindings (list (cons a b)) (list (cons b a)))))
    (should (null (assq a c)))
    (should (equal (tl-apply-bindings b c) a))))

(ert-deftest typeenv/constructors ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Bool (True) (False))" env)
    (should (tl-tscheme-p (gethash 'True (tl-env-type-env env))))
    (should (equal (tl-tscheme-type (gethash 'True (tl-env-type-env env)))
                   (tl-tcon 'Bool nil)))))

(ert-deftest typeenv/constructor-arrow ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Nat (Zero) (Succ Nat))" env)
    (let ((ty (tl-tscheme-type (gethash 'Succ (tl-env-type-env env)))))
      (should (equal ty (tl-tarrow (tl-tcon 'Nat nil) (tl-tcon 'Nat nil)))))))

(ert-deftest typeenv/constructor-polymorphic ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Pair (Pair a b))" env)
    (let* ((sc (gethash 'Pair (tl-env-type-env env)))
           (ty (tl-tscheme-type sc))
           (vars (tl-tscheme-vars sc)))
      (should (= (length vars) 2))
      ;; Pair : a -> b -> Pair a b  (argument order preserved)
      (should (eq (tl-tcon-name ty) '->))
      (should (eq (nth 0 (tl-tcon-args ty)) (nth 0 vars)))
      (let ((inner (nth 1 (tl-tcon-args ty))))
        (should (eq (tl-tcon-name inner) '->))
        (should (eq (nth 0 (tl-tcon-args inner)) (nth 1 vars)))
        (let ((res (nth 1 (tl-tcon-args inner))))
          (should (eq (tl-tcon-name res) 'Pair))
          (should (eq (nth 0 (tl-tcon-args res)) (nth 0 vars)))
          (should (eq (nth 1 (tl-tcon-args res)) (nth 1 vars))))))))

(ert-deftest typeenv/extension ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype open Expr (Lit Int))" env)
    (termlisp-eval "(datatype-extension Expr (Add Expr Expr))" env)
    (let ((ty (tl-tscheme-type (gethash 'Add (tl-env-type-env env)))))
      (should (equal ty (tl-tarrow (tl-tcon 'Expr nil)
                                   (tl-tarrow (tl-tcon 'Expr nil)
                                              (tl-tcon 'Expr nil))))))))

(ert-deftest typeenv/open-polymorphic-extension ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype open List (Nil) (Cons a (List a)))" env)
    (termlisp-eval "(datatype-extension List (Snoc (List a) a))" env)
    (let* ((sc (gethash 'Snoc (tl-env-type-env env)))
           (ty (tl-tscheme-type sc))
           ;; Snoc : List a -> a -> List a
           (res (nth 1 (tl-tcon-args (nth 1 (tl-tcon-args ty))))))
      (should (= (length (tl-tscheme-vars sc)) 1))
      (should (eq (tl-tcon-name res) 'List))
      (should (= (length (tl-tcon-args res)) 1)))))

(ert-deftest typeenv/extension-undeclared-param ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype open Expr (Lit Int))" env)
    (should-error (termlisp-eval "(datatype-extension Expr (Var a))" env)
                  :type 'termlisp-type-error)))

(ert-deftest typeenv/redeclaration-purges ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Foo (A) (B))" env)
    (termlisp-eval "(datatype Foo (C))" env)
    (should (null (gethash 'A (tl-env-constructors env))))
    (should (null (gethash 'B (tl-env-constructors env))))
    (should (eq (gethash 'C (tl-env-constructors env)) 'Foo))))

(ert-deftest infer/literals ()
  (should (equal (car (tl-infer nil 1)) (tl-tint)))
  (should (equal (car (tl-infer nil "x")) (tl-tstring))))

(ert-deftest infer/lambda ()
  (let ((ty (car (tl-infer nil '(lambda (x) x)))))
    (should (eq (tl-tcon-name ty) '->))
    (let ((args (tl-tcon-args ty)))
      (should (eq (nth 0 args) (nth 1 args))))))

(ert-deftest infer/application-identity ()
  (should (equal (car (tl-infer nil '((lambda (x) x) 1))) (tl-tint))))

(ert-deftest infer/lambda-two-args ()
  ;; ((lambda (x y) x) 1 "s") : Int
  (should (equal (car (tl-infer nil '((lambda (x y) x) 1 "s"))) (tl-tint))))

(ert-deftest infer/type-error ()
  (should-error (tl-infer nil '(1 2)) :type 'termlisp-type-error))

(ert-deftest infer/constructor-type ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Nat (Zero) (Succ Nat))" env)
    ;; Zero : Nat ; (Succ Zero) : Nat
    (should (equal (car (tl-infer (cons nil env) 'Zero)) (tl-tcon 'Nat nil)))
    (should (equal (car (tl-infer (cons nil env) '(Succ Zero))) (tl-tcon 'Nat nil)))))

(ert-deftest infer/shared-variable-linked ()
  "Two uses of the same local function variable must share its result type."
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Pair (Pair a b))" env)
    (let* ((ty (car (tl-infer (cons nil env) '(lambda (f) (Pair (f 1) (f 2))))))
           (pairty (nth 1 (tl-tcon-args ty)))
           (p1 (nth 0 (tl-tcon-args pairty)))
           (p2 (nth 1 (tl-tcon-args pairty))))
      (should (eq p1 p2)))))

(ert-deftest infer/conflicting-uses-rejected ()
  "Using the same function at two incompatible types must be rejected."
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Pair (Pair a b))" env)
    (should-error (tl-infer (cons nil env) '(lambda (f) (Pair (f 1) (f "s"))))
                  :type 'termlisp-type-error)))

(ert-deftest infer/define-id ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(define (id x) x)")
    (let ((ty (tl-tscheme-type (gethash 'id (tl-env-type-env env)))))
      (should (eq (tl-tcon-name ty) '->))
      (should (eq (nth 0 (tl-tcon-args ty)) (nth 1 (tl-tcon-args ty)))))))

(ert-deftest infer/define-peano-plus ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Nat (Zero) (Succ Nat))")
    (termlisp-typecheck-def env "(define (plus Zero b) b)")
    (termlisp-typecheck-def env "(define (plus (Succ a) b) (Succ (plus a b)))")
    (let ((ty (tl-tscheme-type (gethash 'plus (tl-env-type-env env)))))
      (should (equal ty (tl-tarrow (tl-tcon 'Nat nil)
                                   (tl-tarrow (tl-tcon 'Nat nil)
                                              (tl-tcon 'Nat nil))))))))

(ert-deftest infer/type-mismatch-clauses ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Bool (True) (False))")
    (termlisp-typecheck-def env "(define (bad True) 1)")
    (should-error (termlisp-typecheck-def env "(define (bad False) \"x\")")
                  :type 'termlisp-type-error)))

(ert-deftest infer/define-constant ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(define n 5)")
    (should (equal (tl-tscheme-type (gethash 'n (tl-env-type-env env))) (tl-tint)))))

(ert-deftest infer/guard-pattern ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Bool (True) (False))")
    (termlisp-typecheck-def env "(define (zero? (guard n (eq n 0))) (True))")
    (should (gethash 'zero? (tl-env-type-env env)))))

(ert-deftest infer/lambda-pattern ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(define (map1 a (:lambda fun)) (fun a))")
    (let ((ty (tl-tscheme-type (gethash 'map1 (tl-env-type-env env)))))
      ;; a -> (a -> b) -> b
      (should (eq (tl-tcon-name ty) '->))
      (let* ((a1 (nth 0 (tl-tcon-args ty)))
             (a2 (nth 1 (tl-tcon-args ty)))
             (fun-type (nth 0 (tl-tcon-args a2))))
        (should (eq (tl-tcon-name a2) '->))
        (should (eq (tl-tcon-name fun-type) '->))
        (should (eq (nth 0 (tl-tcon-args fun-type)) a1))))))

(ert-deftest infer/or-pattern-bindings ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Nat (Zero) (Succ Nat))")
    (termlisp-typecheck-def env "(define (pred (or (Succ n) Zero)) n)")
    (let ((ty (tl-tscheme-type (gethash 'pred (tl-env-type-env env)))))
      (should (equal (nth 0 (tl-tcon-args ty)) (tl-tcon 'Nat nil)))
      (should (equal (nth 1 (tl-tcon-args ty)) (tl-tcon 'Nat nil))))))

(ert-deftest infer/constructor-arity-error ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Nat (Zero) (Succ Nat))")
    (should-error (termlisp-typecheck-def env "(define (f (Succ a b)) a)")
                  :type 'termlisp-type-error)))

(ert-deftest signature/checked ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(: id (a -> a))")
    (let ((sig (gethash 'id (tl-env-type-env env))))
      (termlisp-typecheck-def env "(define (id x) x)")
      (should (eq (gethash 'id (tl-env-type-env env)) sig)))))

(ert-deftest signature/under-general-rejected ()
  "A definition less general than its signature must be rejected."
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Nat (Zero) (Succ Nat))")
    (termlisp-typecheck-def env "(: f (a -> a))")
    (should-error (termlisp-typecheck-def env "(define (f x) 5)")
                  :type 'termlisp-type-error)
    (should-error (termlisp-typecheck-def env "(: g (a -> a)) (define (g x) (Succ x))")
                  :type 'termlisp-type-error)))

(ert-deftest signature/specialization-ok ()
  "A definition more general than its signature is accepted."
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(: id (Int -> Int))")
    (termlisp-typecheck-def env "(define (id x) x)")
    (should (gethash 'id (tl-env-type-env env)))))

(ert-deftest signature/constant-mismatch ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(: c Int)")
    (should-error (termlisp-typecheck-def env "(define c \"hello\")")
                  :type 'termlisp-type-error)))

(ert-deftest signature/mismatch ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(: id Int)")
    (should-error (termlisp-typecheck-def env "(define (id x) x)")
                  :type 'termlisp-type-error)))

(ert-deftest api/typecheck-string ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck "(define (id x) x)" env)
    (should (gethash 'id (tl-env-type-env env)))))

(ert-deftest api/typecheck-prelude ()
  "The prelude must typecheck without error."
  (let ((env (termlisp-make-env)))
    (should (termlisp-typecheck-file
             (expand-file-name "termlisp-prelude.tls" termlisp--directory)
             env))))

(ert-deftest class/declare-and-methods ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (should (gethash 'Functor (tl-env-class-env env)))
    (should (gethash 'fmap (tl-env-method-env env)))))

(ert-deftest class/instance-registration ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-typecheck-def env "(instance (Functor Maybe))")
    (should (= (length (gethash 'Functor (tl-env-instance-env env))) 1))))

(ert-deftest class/method-scheme-wellformed ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (let* ((sc (gethash 'fmap (tl-env-method-env env)))
           (ty (tl-tscheme-type sc))
           (vars (tl-tscheme-vars sc))
           (ct (tl-constraint-type (car (tl-tscheme-constraints sc)))))
      (should (= (length vars) 3))
      (should (memq ct vars))
      (should (memq ct (tl-free-tvars ty))))))

(ert-deftest class/method-use-constraint ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-eval "(datatype Maybe (Nothing) (Just a))" env)
    (let ((tl-infer-constraints nil))
      (tl-infer (cons nil env) '(lambda (g x) (fmap g x)))
      (should (= (length tl-infer-constraints) 1))
      (should (tl-constraint-p (car tl-infer-constraints)))
      (should (eq (tl-constraint-class (car tl-infer-constraints)) 'Functor)))))

(ert-deftest class/solve-instance ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-eval "(datatype Maybe (Nothing) (Just a))" env)
    (termlisp-typecheck-def env "(instance (Functor Maybe))")
    (should (termlisp-typecheck "(fmap (lambda (x) x) (Just 1))" env))))

(ert-deftest class/unsolved-constraint-errors ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-eval "(datatype NotFunctor (Mk a))" env)
    (should-error (termlisp-typecheck "(fmap (lambda (x) x) (Mk 1))" env)
                  :type 'termlisp-type-error)))

(ert-deftest class/generalized-constraint ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-typecheck-def env "(define (twice g x) (fmap g (fmap g x)))")
    (let ((sc (gethash 'twice (tl-env-type-env env))))
      (should (= (length (tl-tscheme-constraints sc)) 1)))))

(ert-deftest class/ambiguous-constraint-errors ()
  "A top-level expression whose class variable is unresolved is rejected."
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-file
     (expand-file-name "termlisp-prelude.tls" termlisp--directory) env)
    (should-error (termlisp-typecheck "(return 7)" env)
                  :type 'termlisp-type-error)))

(ert-deftest class/canonical-key ()
  "Canonical keys are invariant under renaming of type variables."
  (let ((a (tl-fresh-tvar)) (b (tl-fresh-tvar)) (c (tl-fresh-tvar)))
    (should (equal (tl-canonical-key (tl-tarrow a a))
                   (tl-canonical-key (tl-tarrow b b))))
    (should (equal (tl-canonical-key (tl-tcon 'Maybe (list a a)))
                   (tl-canonical-key (tl-tcon 'Maybe (list b b)))))
    (should-not (equal (tl-canonical-key (tl-tarrow a b))
                       (tl-canonical-key (tl-tarrow c c))))))

(ert-deftest class/canonical-key-head-position ()
  "Head-position variables are numbered before argument variables."
  (let ((f (tl-fresh-tvar)) (a (tl-fresh-tvar)))
    (should (equal (tl-canonical-key (tl-tcon f (list a))) "(?0 ?1)"))))

(ert-deftest class/canonical-key-dedup ()
  "Canonical-key bucketing dedups equal constraints but not distinct vars."
  (let* ((a (tl-fresh-tvar)) (b (tl-fresh-tvar))
         (c1 (tl-constraint 'Functor (tl-tcon 'Maybe (list a))))
         (c2 (tl-constraint 'Functor (tl-tcon 'Maybe (list a))))
         (c3 (tl-constraint 'Functor (tl-tcon 'Maybe (list b)))))
    (should (= (length (tl-remove-duplicates-by-key
                        (list c1 c2) #'tl-constraint-canonical-key #'equal))
               1))
    (should (= (length (tl-remove-duplicates-by-key
                        (list c1 c3) #'tl-constraint-canonical-key #'equal))
               2))))

(ert-deftest typecheck/do ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-file
     (expand-file-name "termlisp-prelude.tls" termlisp--directory) env)
    (should (termlisp-typecheck "(do MaybeDict (x <- (Just 1)) (return (+ x 1)))" env))
    (should-error (termlisp-typecheck "(do MaybeDict (x <- (Just 1)) (return (+ x \"s\")))" env)
                  :type 'termlisp-type-error)))

(ert-deftest api/eval-with-type-check ()
  (let ((env (termlisp-make-env '(:type-check t))))
    (should (equal (termlisp-eval "(define (id x) x) (id 42)" env) 42))
    (should-error (termlisp-eval "(define (bad x) (+ x 1)) (bad \"s\")" env)
                  :type 'termlisp-type-error)))

(ert-deftest api/eval-type-check-rejects-ill-typed ()
  "Type checking must reject ill-typed code even when eval would not error."
  (let ((env (termlisp-make-env '(:type-check t))))
    (termlisp-eval "(datatype Nat (Zero) (Succ Nat)) (define (bad x) (Succ x))" env)
    (should-error (termlisp-eval "(bad \"s\")" env)
                  :type 'termlisp-type-error)))

(ert-deftest infer/value-restriction-no-escape ()
  "A tvar free in a monomorphic binding must not be generalized."
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(define n (unknown-fn))")
    (termlisp-typecheck-def env "(define (f x) n)")
    (let ((sc (gethash 'f (tl-env-type-env env))))
      ;; only the argument tvar is generalized; n's tvar stays rigid
      (should (= (length (tl-tscheme-vars sc)) 1)))))

(ert-deftest infer/builtin-types ()
  "Builtins are typed: arithmetic is Int-only."
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(define (inc x) (+ x 1))")
    (should (equal (tl-tscheme-type (gethash 'inc (tl-env-type-env env)))
                   (tl-tarrow (tl-tint) (tl-tint))))))

(ert-deftest infer/builtin-static-rejection ()
  (should-error (termlisp-typecheck "(define (bad x) (+ x 1)) (bad \"s\")")
                :type 'termlisp-type-error))

(ert-deftest infer/or-incompatible-alternatives ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Nat (Zero) (Succ Nat))")
    (termlisp-typecheck-def env "(datatype Pair (Pair a b))")
    (should-error
     (termlisp-typecheck-def env "(define (weird (or (Succ n) (Pair n m))) n)")
     :type 'termlisp-type-error)))

(require 'termlisp-data-reader)

(ert-deftest data-reader/pure-and-run ()
  (let ((m (cats-pure (tl-data-reader) 42)))
    (should (= (tl-run-reader m :env) 42))))

(ert-deftest data-reader/ask ()
  (should (eq (tl-run-reader (tl-reader-ask) :env) :env)))

(ert-deftest data-reader/fmap ()
  (let ((m (cats-fmap (lambda (x) (1+ x)) (cats-pure (tl-data-reader) 41))))
    (should (= (tl-run-reader m :env) 42))))

(ert-deftest data-reader/bind ()
  (let ((m (cats-bind (tl-reader-ask)
                      (lambda (r) (cats-pure (tl-data-reader) (list r r))))))
    (should (equal (tl-run-reader m :cfg) '(:cfg :cfg)))))

(ert-deftest data-reader/local ()
  (let ((m (tl-reader-local (lambda (_) :inner) (tl-reader-ask))))
    (should (eq (tl-run-reader m :outer) :inner))))

(ert-deftest data-reader/apply ()
  (let ((mf (cats-pure (tl-data-reader) (lambda (x) (1+ x))))
        (mx (cats-pure (tl-data-reader) 41)))
    (should (= (tl-run-reader (cats-apply mf mx) :e) 42))))

(ert-deftest monad/maybe-fmap ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-fmap MaybeDict (lambda (x) (+ x 1)) (Just 4))" env))
                   "(Just 5)"))
    (should (eq (termlisp-eval "(monad-fmap MaybeDict (lambda (x) (+ x 1)) Nothing)" env)
                'Nothing))))

(ert-deftest monad/list-fmap-and-append ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-fmap ListDict (lambda (x) (+ x 1)) (Cons 1 (Cons 2 Nil)))" env))
                   "(Cons 2 (Cons 3 Nil))"))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(list-append (Cons 1 (Cons 2 Nil)) (Cons 3 Nil))" env))
                   "(Cons 1 (Cons 2 (Cons 3 Nil)))"))))

(ert-deftest monad/list-bind-nil ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(monad-bind ListDict Nil (lambda (x) (Cons x Nil)))" env)
                'Nil))))

(ert-deftest do/maybe ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do MaybeDict (x <- (Just 1)) (y <- (Just 2)) (return (+ x y)))" env))
                   "(Just 3)"))
    (should (eq (termlisp-eval
                 "(do MaybeDict (x <- (Just 1)) (y <- Nothing) (return (+ x y)))" env)
                'Nothing))))

(ert-deftest do/list ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do ListDict (x <- (Cons 1 (Cons 2 Nil))) (return (+ x 10)))" env))
                   "(Cons 11 (Cons 12 Nil))"))))

(ert-deftest do/type-directed-maybe ()
  (let ((env (termlisp-make-env '(:elaborate t))))
    (termlisp-load-prelude env)
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do (x <- (Just 1)) (y <- (Just 2)) (return (+ x y)))" env))
                   "(Just 3)"))
    (should (eq (termlisp-eval
                 "(do (x <- (Just 1)) (y <- Nothing) (return (+ x y)))" env)
                'Nothing))))

(ert-deftest do/type-directed-list ()
  (let ((env (termlisp-make-env '(:elaborate t))))
    (termlisp-load-prelude env)
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do (x <- (Cons 1 (Cons 2 Nil))) (return (+ x 10)))" env))
                   "(Cons 11 (Cons 12 Nil))"))))

(ert-deftest do/requires-return ()
  (let ((env (termlisp-load-prelude)))
    (should-error (termlisp-eval "(do MaybeDict (x <- (Just 1)))" env)
                  :type 'termlisp-eval-error)))

(ert-deftest do/bare-statement ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do MaybeDict (Just 99) (return 2))" env))
                   "(Just 2)"))))

(ert-deftest do/nested ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "(do MaybeDict
                        (x <- (Just 1))
                        (y <- (do MaybeDict (y <- (Just 2)) (return (+ x y))))
                        (return y))"
                     env))
                   "(Just 3)"))))

(ert-deftest do/subexpression ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(Pair (do MaybeDict (return 1)) (do MaybeDict (return 2)))" env))
                   "(Pair (Just 1) (Just 2))"))))

(ert-deftest do/type-directed-nested ()
  "A nested type-directed `do' is elaborated, not just a top-level one.
Each block binds a value from `Just' so its monad is fixed to Maybe;
a bare `(return 1)' would leave the monad ambiguous."
  (let ((env (termlisp-make-env '(:elaborate t))))
    (termlisp-load-prelude env)
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "(Pair (do (x <- (Just 1)) (return x))
                            (do (y <- (Just 2)) (return y)))" env))
                   "(Pair (Just 1) (Just 2))"))))

(ert-deftest do/no-underscore-capture ()
  (let ((env (termlisp-load-prelude)))
    (termlisp-eval "(define _ 42)" env)
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do MaybeDict (Just 0) (return _))" env))
                   "(Just 42)"))))

(ert-deftest monad/state ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "((run-state
                        (do StateDict
                          (n <- (state-get))
                          (state-put (+ n 1))
                          (return n)))
                       0)"
                     env))
                   "(Pair 0 1)"))))

(ert-deftest monad/reader ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval
                 "((run-reader (do ReaderDict (r <- (reader-ask)) (return r))) cfg)"
                 env)
                'cfg))))

(ert-deftest monad-laws/maybe ()
  (let ((env (termlisp-load-prelude)))
    ;; left identity: bind (return a) f = f a
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (monad-return MaybeDict 5) (lambda (x) (Just (+ x 1))))" env))
                   "(Just 6)"))
    ;; right identity: bind m return = m
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (Just 5) (lambda (x) (monad-return MaybeDict x)))" env))
                   "(Just 5)"))
    ;; associativity
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (monad-bind MaybeDict (Just 2) (lambda (x) (Just (+ x 1)))) (lambda (y) (Just (* y 10))))" env))
                   (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (Just 2) (lambda (x) (monad-bind MaybeDict (Just (+ x 1)) (lambda (y) (Just (* y 10))))))" env))))))

(ert-deftest monad-laws/list ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (monad-return ListDict 5) (lambda (x) (Cons x (Cons x Nil))))" env))
                   "(Cons 5 (Cons 5 Nil))"))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (Cons 1 (Cons 2 Nil)) (lambda (x) (monad-return ListDict x)))" env))
                   "(Cons 1 (Cons 2 Nil))"))
    ;; associativity
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (monad-bind ListDict (Cons 1 (Cons 2 Nil)) (lambda (x) (Cons x (Cons (* x 10) Nil)))) (lambda (y) (Cons (+ y 1) Nil)))" env))
                   (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (Cons 1 (Cons 2 Nil)) (lambda (x) (monad-bind ListDict (Cons x (Cons (* x 10) Nil)) (lambda (y) (Cons (+ y 1) Nil)))))" env))))))

(ert-deftest monad-laws/state ()
  (let ((env (termlisp-load-prelude)))
    ;; right identity: bind m return = m (run both with state 7)
    (should (equal (termlisp-value->string
                    (termlisp-eval "((monad-bind StateDict (state-put 3) (lambda (x) (monad-return StateDict x))) 7)" env))
                   (termlisp-value->string
                    (termlisp-eval "((state-put 3) 7)" env))))
    ;; left identity: bind (return a) f = f a
    (should (equal (termlisp-value->string
                    (termlisp-eval "((monad-bind StateDict (monad-return StateDict 5) (lambda (x) (state-put (+ x 1)))) 0)" env))
                   (termlisp-value->string
                    (termlisp-eval "(((lambda (x) (state-put (+ x 1))) 5) 0)" env))))
    ;; associativity
    (should (equal (termlisp-value->string
                    (termlisp-eval "((monad-bind StateDict (monad-bind StateDict (state-put 1) (lambda (x) (state-return x))) (lambda (y) (state-return y))) 0)" env))
                   (termlisp-value->string
                    (termlisp-eval "((monad-bind StateDict (state-put 1) (lambda (x) (monad-bind StateDict (state-return x) (lambda (y) (state-return y))))) 0)" env))))
    ;; fmap over state
    (should (equal (termlisp-value->string
                    (termlisp-eval "((monad-fmap StateDict (lambda (x) (+ x 1)) (state-return 5)) 0)" env))
                   "(Pair 6 0)"))))

(ert-deftest monad-laws/reader ()
  (let ((env (termlisp-load-prelude)))
    ;; left identity
    (should (eq (termlisp-eval "((monad-bind ReaderDict (monad-return ReaderDict 5) (lambda (x) (reader-return (+ x 1)))) cfg)" env)
                6))
    ;; right identity
    (should (eq (termlisp-eval "((monad-bind ReaderDict (reader-ask) (lambda (x) (monad-return ReaderDict x))) cfg)" env)
                'cfg))
    ;; associativity
    (should (eq (termlisp-eval "((monad-bind ReaderDict (monad-bind ReaderDict (reader-ask) (lambda (x) (reader-return x))) (lambda (y) (reader-return y))) cfg)" env)
                'cfg))
    ;; fmap over reader
    (should (eq (termlisp-eval "((monad-fmap ReaderDict (lambda (x) x) (reader-ask)) cfg)" env)
                'cfg))))

(ert-deftest class/prelude-instances ()
  "The prelude declares Functor/Applicative/Monad with Maybe/List/State/Reader instances."
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-file
     (expand-file-name "termlisp-prelude.tls" termlisp--directory) env)
    (dolist (c '(Functor Applicative Monad))
      (should (gethash c (tl-env-class-env env)))
      (let ((types (mapcar (lambda (i)
                             (tl-tcon-name (tl-as-tcon (tl-instance-head i))))
                           (gethash c (tl-env-instance-env env)))))
        (dolist (ty '(Maybe List State Reader))
          (should (memq ty types)))))))

(ert-deftest elaborate/method-dictionary-passing ()
  (let ((env (termlisp-load-prelude (termlisp-make-env '(:elaborate t)))))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(fmap (lambda (x) (+ x 1)) (Just 4))" env))
                   "(Just 5)"))
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "(fmap (lambda (x) (+ x 1)) (Cons 1 (Cons 2 Nil)))" env))
                   "(Cons 2 (Cons 3 Nil))"))))

(ert-deftest elaborate/bind-return ()
  (let ((env (termlisp-load-prelude (termlisp-make-env '(:elaborate t)))))
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "(bind (Just 1) (lambda (x) (return (+ x 1))))" env))
                   "(Just 2)"))))

(ert-deftest elaborate/applicative ()
  "Applicative methods resolve to their instance dictionaries.
A bare `(pure 3)' is ambiguous (its applicative is unconstrained), so
the test fixes the type to Maybe with a signature-annotated binding."
  (let ((env (termlisp-make-env '(:elaborate t))))
    (termlisp-load-prelude env)
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "(: p3 (Maybe Int)) (define p3 (pure 3)) p3" env))
                   "(Just 3)"))
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "(ap (Just (lambda (x) (+ x 1))) (Just 4))" env))
                   "(Just 5)"))))

(ert-deftest elaborate/ambiguous-constraint-errors ()
  (let ((env (termlisp-make-env '(:elaborate t))))
    (termlisp-load-prelude env)
    (should-error (termlisp-eval "(return 7)" env)
                  :type 'termlisp-type-error)))

(ert-deftest prelude/list-head-tail ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(head (Cons A (Cons B Nil)))" env) 'A))
    (should (equal (termlisp-value->string (termlisp-eval "(tail (Cons A (Cons B Nil)))" env))
                   "(Cons B Nil)"))))

(ert-deftest prelude/list-length-append ()
  (let ((env (termlisp-load-prelude)))
    (should (= (termlisp-eval "(length (Cons A (Cons B (Cons C Nil))))" env) 3))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(append (Cons A Nil) (Cons B (Cons C Nil)))" env))
                   "(Cons A (Cons B (Cons C Nil)))"))))

(ert-deftest prelude/list-map-filter-foldr ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(map-list (lambda (x) (+ x 1)) (Cons 1 (Cons 2 Nil)))" env))
                   "(Cons 2 (Cons 3 Nil))"))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(filter (lambda (x) (eq x 1)) (Cons 1 (Cons 2 Nil)))" env))
                   "(Cons 1 Nil)"))
    (should (= (termlisp-eval "(foldr (lambda (x acc) (+ x acc)) 0 (Cons 1 (Cons 2 (Cons 3 Nil))))" env)
               6))))

(ert-deftest prelude/assert-equal ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(assertEqual (Cons 1 Nil) (Cons 1 Nil))" env) 'True))
    (should (eq (termlisp-eval "(assertEqual (Cons 1 Nil) (Cons 2 Nil))" env) 'False))))

(ert-deftest prelude/boolean-law ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(and (not (and True False)) (or True False))" env) 'True))))

(ert-deftest acceptance/examples-all ()
  (let ((env (termlisp-load-prelude)))
    (should (= (termlisp-eval-file
                (expand-file-name "examples/lists.tls" termlisp--directory)
                env)
               3)))
  (let ((env (termlisp-load-prelude (termlisp-make-env '(:elaborate t)))))
    (should (equal (termlisp-value->string
                    (termlisp-eval-file
                     (expand-file-name "examples/classes.tls" termlisp--directory)
                     env))
                   "(Just 5)"))))

(ert-deftest core/decompose-cons ()
  (should (equal (tl-decompose '(f a b)) (cons 'f (list '(a b)))))
  (should (null (tl-decompose 'x))))

(ert-deftest core/decompose-tcon ()
  (let ((ty (tl-tcon 'List (list (tl-tint)))))
    (should (equal (tl-decompose ty) (cons 'List (list (tl-tint)))))))

(ert-deftest core/unify-cons-and-tcon ()
  ;; same kernel, two representations
  (let ((x (tl-make-lvar 'x)))
    (should (car (tl-unify (list 'f x) (list 'f 1) nil)))
    (should (equal (tl-deref x (cdr (tl-unify (list 'f x) (list 'f 1) nil))) 1)))
  (let ((a (tl-fresh-tvar)))
    (should (car (tl-unify-types (tl-tcon 'List (list a)) (tl-tcon 'List (list (tl-tint))) nil)))
    (should (equal (tl-deref a (cdr (tl-unify-types (tl-tcon 'List (list a)) (tl-tcon 'List (list (tl-tint))) nil))) (tl-tint)))))

(ert-deftest load/tls-as-elisp ()
  (let ((file (make-temp-file "termlisp-load-" nil ".tls")))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";;; -*- lexical-binding: t; -*-\n"
                    "(datatype Nat (Zero) (Succ Nat))\n"
                    "(define (plus Zero b) b)\n"
                    "(define (plus (Succ a) b) (Succ (plus a b)))\n"))
          (let ((termlisp--load-env (termlisp-make-env)))
            (load file nil t)
            (should (equal (termlisp-value->string
                            (termlisp-eval-form '(plus (Succ Zero) (Succ Zero))
                                                termlisp--load-env))
                           "(Succ (Succ Zero))"))))
      (delete-file file))))

(ert-deftest load/auto-magic-string ()
  (let ((file (make-temp-file "termlisp-magic-" nil ".tls")))
    (unwind-protect
        (progn
          (with-temp-file file (insert "(datatype Nat (Zero) (Succ Nat))\n"))
          (should-not (string-prefix-p termlisp--magic-string
                                       (with-temp-buffer (insert-file-contents file) (buffer-string))))
          (termlisp-load file)
          (should (string-prefix-p termlisp--magic-string
                                   (with-temp-buffer (insert-file-contents file) (buffer-string)))))
      (delete-file file))))

(ert-deftest graph/build-atom ()
  (let* ((g (tl-graph-build 'foo))
         (n (tl-graph-root g)))
    (should (tl-node-p n))
    (should (eq (tl-node-head n) 'foo))
    (should (null (tl-node-children n)))))

(ert-deftest graph/build-application ()
  (let* ((g (tl-graph-build '(f a b)))
         (n (tl-graph-root g)))
    (should (eq (tl-node-head n) 'f))
    (should (= (length (tl-node-children n)) 2))
    (should (eq (tl-node-head (car (tl-node-children n))) 'a))))

(ert-deftest graph/sharing ()
  "Structurally identical subterms share one node."
  (let* ((g (tl-graph-build '(pair (f x) (f x))))
         (kids (tl-node-children (tl-graph-root g))))
    (should (eq (car kids) (cadr kids)))))

(ert-deftest graph/node-state ()
  (let ((n (tl-make-node 'f nil)))
    (should (eq (tl-node-state n) :idle))))

(ert-deftest graph/match-variable ()
  (let ((g (tl-graph-build '(f a))))
    (should (tl-graph-match '$x (tl-graph-root g) nil))))

(ert-deftest graph/match-structure ()
  (let* ((g (tl-graph-build '(:global "C-c f" foo)))
         (b (tl-graph-match '(:global $key $cmd) (tl-graph-root g) nil)))
    (should b)
    (should (equal (tl-node-head (cdr (assq '$key b))) '"C-c f"))
    (should (eq (tl-node-head (cdr (assq '$cmd b))) 'foo))))

(ert-deftest graph/match-nonlinear ()
  (let* ((g (tl-graph-build '(pair a a)))
         (b (tl-graph-match '(pair $x $x) (tl-graph-root g) nil)))
    (should b))
  (let* ((g (tl-graph-build '(pair a b))))
    (should-not (tl-graph-match '(pair $x $x) (tl-graph-root g) nil))))

(ert-deftest graph/rule-rewrite-in-place ()
  (let* ((g (tl-graph-build '(:global "C-c f" foo)))
         (r (tl-make-grule 'global :normalize 0
                           '(:global $key $cmd)
                           '(:bind (quote current-global-map) $key $cmd))))
    (should (tl-graph-apply (tl-graph-root g) r))
    (let ((root (tl-graph-root g)))
      (should (eq (tl-node-head root) :bind))
      (should (eq (tl-node-head (car (tl-node-children root))) 'quote)))))

(ert-deftest graph/rule-no-match ()
  (let* ((g (tl-graph-build '(foo bar)))
         (r (tl-make-grule 'x :normalize 0 '(:global $k $c) '(:bind $k $c))))
    (should-not (tl-graph-apply (tl-graph-root g) r))))

(ert-deftest graph/non-progressing-error ()
  (let* ((g (tl-graph-build '(foo)))
         (r (tl-make-grule 'id :normalize 0 '$x '$x)))
    (should-error (tl-graph-apply (tl-graph-root g) r)
                  :type 'termlisp-eval-error)))

(ert-deftest graph/phase-order ()
  "An earlier phase fires first; later phases do not re-run."
  (let* ((g (tl-graph-build '(a)))
         (r1 (tl-make-grule 'n :normalize 0 '(a) '(b)))
         (r2 (tl-make-grule 'd :desugar 0 '(a) '(c))))
    (tl-graph-rewrite g (list r1 r2))
    (should (eq (tl-node-head (tl-graph-root g)) 'b))))

(ert-deftest graph/priority ()
  "Within a phase, the lower priority number fires first."
  (let* ((g (tl-graph-build '(a)))
         (r1 (tl-make-grule 'p0 :normalize 0 '(a) '(b)))
         (r2 (tl-make-grule 'p1 :normalize 1 '(a) '(c))))
    (tl-graph-rewrite g (list r1 r2))
    (should (eq (tl-node-head (tl-graph-root g)) 'b))))

(ert-deftest graph/strict-normalization ()
  "Reduction descends into children (leftmost-outermost)."
  (let* ((g (tl-graph-build '(outer (a))))
         (r (tl-make-grule 'r :normalize 0 '(a) '(b))))
    (tl-graph-rewrite g (list r))
    (should (eq (tl-node-head (car (tl-node-children (tl-graph-root g)))) 'b))))

(ert-deftest graph/normal-form ()
  (let* ((g (tl-graph-build '(a)))
         (r (tl-make-grule 'r :normalize 0 '(a) '(b))))
    (should-not (tl-graph-normal-form-p g (list r)))
    (tl-graph-rewrite g (list r))
    (should (tl-graph-normal-form-p g (list r)))))

(ert-deftest graph/chain-within-phase ()
  "Repeated application within a phase reaches the fixed point."
  (let* ((g (tl-graph-build '(a)))
         (r1 (tl-make-grule 'a-b :normalize 0 '(a) '(b)))
         (r2 (tl-make-grule 'b-c :normalize 0 '(b) '(c))))
    (tl-graph-rewrite g (list r1 r2))
    (should (eq (tl-node-head (tl-graph-root g)) 'c))))

(ert-deftest graph/fuel-exhaustion ()
  "A cyclic rule set is bounded by the fuel limit."
  (let* ((g (tl-graph-build '(a)))
         (r1 (tl-make-grule 'a-b :normalize 0 '(a) '(b)))
         (r2 (tl-make-grule 'b-a :normalize 0 '(b) '(a))))
    (should-error (tl-graph-rewrite g (list r1 r2))
                  :type 'termlisp-eval-error)))

(ert-deftest graph/render-node ()
  (let* ((g (tl-graph-build '(f a (g b)))))
    (should (equal (tl-node->sexp (tl-graph-root g)) '(f a (g b))))))

(ert-deftest graph/rewrite-sexp ()
  (let ((r (tl-make-grule 'global :normalize 0
                          '(:global $k $c)
                          '(:bind (quote current-global-map) $k $c))))
    (should (equal (tl-graph-rewrite-sexp '(:global "C-c f" foo) (list r))
                   '(:bind (quote current-global-map) "C-c f" foo)))))

(ert-deftest graph/rewrite-sexp-unchanged ()
  (should (equal (tl-graph-rewrite-sexp '(f a b) nil) '(f a b))))

(ert-deftest graph/rewrite-with-guard ()
  (let ((r (tl-make-grule 'g :normalize 0
                          '(:set $v $val)
                          '(:custom $v $val)
                          (lambda (b) (eq (tl-node-head (cdr (assq '$v b))) 'foo)))))
    (should (equal (tl-graph-rewrite-sexp '(:set foo 1) (list r))
                   '(:custom foo 1)))
    (should (equal (tl-graph-rewrite-sexp '(:set bar 1) (list r))
                   '(:set bar 1)))))

(ert-deftest graph/multiphase-rewrite-sexp ()
  "A two-phase rule set reduces fully to primitives."
  (let ((rules (list (tl-make-grule 'global :desugar 0
                                    '(:global $k $c)
                                    '(:bind (quote current-global-map) $k $c))
                     (tl-make-grule 'hook-into :desugar 0
                                    '(:hook-into $h)
                                    '(:add-hook $h (function foo))))))
    (should (equal (tl-graph-rewrite-sexp '(:seq (:global "C-c f" foo) (:hook-into text-mode-hook)) rules)
                   '(:seq (:bind (quote current-global-map) "C-c f" foo)
                          (:add-hook text-mode-hook (function foo)))))))

(ert-deftest graph/cyclic-rule-signals ()
  "A cyclic rule must be bounded by fuel, not crash the Lisp stack."
  (let* ((g (tl-graph-build '(a)))
         (r (tl-make-grule 'c :normalize 0 '$x '(f $x))))
    (should-error (tl-graph-rewrite g (list r) 100)
                  :type 'termlisp-eval-error)))

(ert-deftest graph/normal-form-respects-guard ()
  (let* ((g (tl-graph-build '(:set bar 1)))
         (r (tl-make-grule 'g :normalize 0 '(:set $v $val) '(:custom $v $val)
                           (lambda (b) (eq (tl-node-head (cdr (assq '$v b))) 'foo)))))
    (should (tl-graph-normal-form-p g (list r)))))

(ert-deftest graph/guard-gets-proper-alist ()
  (let* ((g (tl-graph-build '(:set foo 1)))
         (seen nil)
         (r (tl-make-grule 'g :normalize 0 '(:set $v $val) '(:custom $v $val)
                           (lambda (b) (setq seen b) (mapcar #'car b) t))))
    (tl-graph-rewrite g (list r))
    (should (consp (car seen)))))   ; every entry is a cons

(ert-deftest graph/unbound-template-variable ()
  (let* ((g (tl-graph-build '(a)))
         (r (tl-make-grule 'u :normalize 0 '(a) '(f $y))))
    (should-error (tl-graph-rewrite g (list r)) :type 'termlisp-eval-error)))

(ert-deftest graph/atom-vs-nullary ()
  "A nullary application `(a)' is distinct from the atom `a'."
  (should (eq (tl-node->sexp (tl-graph-root (tl-graph-build 'a))) 'a))
  (should (equal (tl-node->sexp (tl-graph-root (tl-graph-build '(a)))) '(a))))

(ert-deftest graph/roundtrip ()
  (dolist (x '(a (a) (f a (g b)) ((a) b) (a (b) c)))
    (should (equal (tl-node->sexp (tl-graph-root (tl-graph-build x))) x))))

(ert-deftest graph/rewrite-to-nullary ()
  (let ((r (tl-make-grule 'q :normalize 0 '(:quit) '(:done))))
    (should (equal (tl-graph-rewrite-sexp '(:quit) (list r)) '(:done)))))

(ert-deftest graph/quote-is-opaque ()
  "A rule must not rewrite inside a quoted subterm."
  (let ((r (tl-make-grule 'g :normalize 0 '(:global $k $c) '(:bind $k $c))))
    (should (equal (tl-graph-rewrite-sexp '(f (quote (:global a b))) (list r))
                   '(f (quote (:global a b)))))))

(ert-deftest graph/function-is-opaque ()
  (let ((r (tl-make-grule 'g :normalize 0 '(a) '(b))))
    (should (equal (tl-graph-rewrite-sexp '(function (a)) (list r))
                   '(function (a))))))

(ert-deftest graph/match-rest ()
  "A `(:rest $v)' pattern captures all remaining children as a node list."
  (let* ((g (tl-graph-build '(:option a b c)))
         (b (tl-graph-match '(:option (:rest $args)) (tl-graph-root g) nil)))
    (should b)
    (let ((args (cdr (assq '$args b))))
      (should (= (length args) 3))
      (should (equal (mapcar #'tl-node->sexp args) '(a b c))))))

(ert-deftest graph/match-rest-empty ()
  "A `(:rest $v)' pattern matches zero remaining children."
  (let* ((g (tl-graph-build '(:option)))
         (b (tl-graph-match '(:option (:rest $args)) (tl-graph-root g) nil)))
    (should b)
    (should (null (cdr (assq '$args b))))))

(ert-deftest graph/match-rest-not-last-errors ()
  "A `(:rest $v)' pattern must be the final element of a list pattern."
  (let ((g (tl-graph-build '(:option a b))))
    (should-error (tl-graph-match '(:option (:rest $args) $x) (tl-graph-root g) nil)
                  :type 'termlisp-eval-error)))

(ert-deftest graph/splice-template ()
  "A `(:splice $v)' template splices a captured node list."
  (let ((r (tl-make-grule 'unseq :normalize 0
                          '(:option (:rest $args))
                          '(:seq (:splice $args)))))
    (should (equal (tl-graph-rewrite-sexp '(:option a b c) (list r))
                   '(:seq a b c)))
    (should (equal (tl-graph-rewrite-sexp '(:option) (list r))
                   '(:seq)))))

(ert-deftest graph/function-template-sexp ()
  "A function template may return a template sexp of the bindings."
  (let ((r (tl-make-grule 'dup :normalize 0
                          '(:double $x)
                          (lambda (_b) '(:pair $x $x)))))
    (should (equal (tl-graph-rewrite-sexp '(:double a) (list r))
                   '(:pair a a)))))

(ert-deftest graph/function-template-node ()
  "A function template may return a node directly."
  (let ((r (tl-make-grule 'swap :normalize 0
                          '(:reverse $x $y)
                          (lambda (b)
                            (tl-make-node :pair
                                          (list (cdr (assq '$y b))
                                                (cdr (assq '$x b)))
                                          t)))))
    (should (equal (tl-graph-rewrite-sexp '(:reverse a b) (list r))
                   '(:pair b a)))))

(ert-deftest graph/function-template-chunks ()
  "Rest patterns, guards and function templates combine for chunking."
  (let ((r (tl-make-grule 'chunk :normalize 0
                          '(:option (:rest $args))
                          (lambda (b)
                            (let ((args (cdr (assq '$args b))))
                              (cons :seq
                                    (cl-loop for (a c) on args by #'cddr
                                             collect (list :option
                                                           (tl-node->sexp a)
                                                           (tl-node->sexp c))))))
                          (lambda (b) (> (length (cdr (assq '$args b))) 2)))))
    (should (equal (tl-graph-rewrite-sexp '(:option a 1 b 2) (list r))
                   '(:seq (:option a 1) (:option b 2))))
    (should (equal (tl-graph-rewrite-sexp '(:option a 1) (list r))
                   '(:option a 1)))))

(ert-deftest graph/splice-unbound-errors ()
  (let ((r (tl-make-grule 'bad :normalize 0
                          '(:x $a)
                          '(:seq (:splice $missing)))))
    (should-error (tl-graph-rewrite-sexp '(:x a) (list r))
                  :type 'termlisp-eval-error)))

(ert-deftest graph/literal-lambda-is-data ()
  "A literal `(lambda ...)' inside a template is data, not a function template."
  (let ((r (tl-make-grule 'wrap :normalize 0
                          '(:wrap $x)
                          (lambda (_b) '(:handler (lambda () $x))))))
    (should (equal (tl-graph-rewrite-sexp '(:wrap a) (list r))
                   '(:handler (lambda () a))))))

(ert-deftest graph/opaque-leaf ()
  "A quoted subterm is built as one opaque leaf, not traversed."
  (let* ((g (tl-graph-build '(f (quote (a b)))))
         (n (car (tl-node-children (tl-graph-root g)))))
    (should-not (tl-node-application n))
    (should (equal (tl-node-head n) '(quote (a b))))))

(ert-deftest graph/deep-quoted-does-not-overflow ()
  "A long quoted list is neither traversed nor rebuilt."
  (let ((sexp (cons 'quote (number-sequence 1 5000))))
    (should (equal (tl-node->sexp (tl-graph-root (tl-graph-build sexp)))
                   sexp))))

(ert-deftest case/parse-shapes ()
  (should (equal (tl-pat-parse '(pvar $x)) '(pvar $x)))
  (should (equal (tl-pat-parse '(pwild)) '(pwild)))
  (should (equal (tl-pat-parse '(plit 0)) '(plit 0)))
  (should (equal (tl-pat-parse '(pcon :seq (pvar $x))) '(pcon :seq (pvar $x))))
  (should (equal (tl-pat-parse '(pas $whole (pvar $x))) '(pas $whole (pvar $x)))))

(ert-deftest case/parse-list ()
  (should (equal (tl-pat-parse '(plist)) '(pnil)))
  (should (equal (tl-pat-parse '(plist (pvar $x) (pvar $y)))
                 '(pcon cons (pvar $x) (pcon cons (pvar $y) (pnil))))))

(ert-deftest case/parse-error ()
  (should-error (tl-pat-parse '(bogus x)) :type 'termlisp-error))

(provide 'termlisp-test)
;;; termlisp-test.el ends here
