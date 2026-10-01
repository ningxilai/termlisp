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

(provide 'termlisp-test)
;;; termlisp-test.el ends here
