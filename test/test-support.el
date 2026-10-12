;;; test-support.el --- shared assertions for the termlisp suites -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Two macros build the data-driven suites in `prelude-test' and
;; `curry-howard-test': `tl-test-eval' asserts that a form renders as a
;; value, `tl-test-reject' that it fails with a message containing a
;; given fragment.  Both evaluate in a *fresh* prelude environment, so no
;; test can leak definitions or type bindings into the next one -- several
;; cases deliberately define functions with the same name.

;;; Code:

(require 'ert)
(require 'termlisp)
(require 'termlisp-io)

(defun tl-test--render (form opts)
  "Evaluate FORM in a fresh prelude environment built from OPTS.
Return the rendered value, or \"ERR:...\" when FORM signals.  Termlisp's
own errors carry their message as the sole string element; anything else
falls back to `error-message-string' rather than printing the offending
argument, which is what a bare `(cadr err)' would do for a
`wrong-type-argument'."
  (let ((env (termlisp-load-prelude (termlisp-make-env opts))))
    (condition-case e
        (termlisp-value->string (termlisp-eval form env))
      (error (format "ERR:%s"
                     (if (stringp (cadr e)) (cadr e) (error-message-string e)))))))

(defmacro tl-test-eval (name form want &optional opts)
  "Define ERT test NAME asserting that FORM renders as WANT.
FORM is evaluated in a fresh prelude environment built from OPTS, which
may be nil to accept the defaults."
  `(ert-deftest ,name ()
     ,(format "Assert %S renders as %S." form want)
     (should (equal (tl-test--render ,form ,opts) ,want))))

(defmacro tl-test-reject (name form needle &optional opts)
  "Define ERT test NAME asserting that FORM is rejected mentioning NEEDLE.
FORM is evaluated in a fresh prelude environment built from OPTS, which
may be nil to accept the defaults.  The failure must carry the
`ERR:' marker as well, so an unexpected success is caught too."
  `(ert-deftest ,name ()
     ,(format "Assert %S is rejected mentioning %S." form needle)
     (let ((got (tl-test--render ,form ,opts)))
       (should (string-prefix-p "ERR:" got))
       (should (string-match-p (regexp-quote ,needle) got)))))

(provide 'test-support)
;;; test-support.el ends here
