;;; termlisp-test.el --- Tests for termlisp -*- lexical-binding: t; -*-

;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

(require 'ert)
(add-to-list 'load-path (expand-file-name ".." (file-name-directory load-file-name)))
(require 'termlisp)

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
  (let ((file (make-temp-file "termlisp-reader-" nil ".tlsp")))
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
                 (expand-file-name "examples/bool.tlsp" termlisp--directory)
                 env)
                'booleans-work)))
  (should (equal (termlisp-value->string
                  (termlisp-eval-file
                   (expand-file-name "examples/nat.tlsp" termlisp--directory)))
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

(ert-deftest type/subst ()
  (let* ((a (tl-fresh-tvar))
         (ty (tl-tarrow a a))
         (sub (list (cons a (tl-tint)))))
    (should (equal (tl-type-subst ty sub) (tl-tarrow (tl-tint) (tl-tint))))))

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

(provide 'termlisp-test)
;;; termlisp-test.el ends here
