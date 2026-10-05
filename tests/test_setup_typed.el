;; tests/test_setup_typed.el -- simple unit checks for setup-typed

;; This test script is intended to be run in batch mode with:
;;   emacs -Q --batch -l setup-typed.el -l tests/test_setup_typed.el

;; The tests are intentionally small and focused on type predicates and a
;; smoke test for macro expansion. They will `error` on failure which makes
;; the process exit with a non-zero status in batch mode.

(require 'subr-x)

;; load local file
(load-file "setup-typed.el")

;; Helper assert
(defun tst-assert (cond msg)
  (unless cond (error "TEST-FAIL: %s" msg)))

;; 1) Composite type: list-of
(let* ((pred (setup-typed-compile-sort-to-pred '(list-of Feature))))
  (tst-assert (funcall pred '(a b c)) ":list-of Feature should accept list of symbols")
  (tst-assert (not (funcall pred '(a 1))) ":list-of Feature should reject mixed list"))

;; 2) maybe
(let* ((pred (setup-typed-compile-sort-to-pred '(maybe Number))))
  (tst-assert (funcall pred nil) ":maybe should accept nil")
  (tst-assert (funcall pred 42) ":maybe should accept number")
  (tst-assert (not (funcall pred "x")) ":maybe Number should reject string"))

;; 3) or / literal
(let* ((pred (setup-typed-compile-sort-to-pred '(or Number Text))))
  (tst-assert (funcall pred 1) ":or should accept number")
  (tst-assert (funcall pred "s") ":or should accept string")
  (tst-assert (not (funcall pred '(1))))
  (let ((pl (setup-typed-compile-sort-to-pred '(literal "a"))))
    (tst-assert (funcall pl "a") ":literal matches")
    (tst-assert (not (funcall pl "b")) ":literal rejects")))

;; 4) Smoke macroexpand test: ensure :require expands into a form containing 'require
(let* ((expanded (macroexpand '(setup-typed (my :feature) (:require foo)))))
  ;; convert to string and check
  (tst-assert (string-match-p "require\\'foo" (prin1-to-string expanded))
              ":require should appear in expansion"))

(princ "ALL TESTS PASSED\n")
