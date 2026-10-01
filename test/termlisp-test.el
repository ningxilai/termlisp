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

(provide 'termlisp-test)
;;; termlisp-test.el ends here
