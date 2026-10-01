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

(provide 'termlisp-test)
;;; termlisp-test.el ends here
