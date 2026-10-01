;;; termlisp.el --- Lazy term-rewriting language -*- lexical-binding: t; -*-

;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Embedded library API for term-lisp.

;;; Code:

(defvar termlisp--root
  (file-name-directory (or load-file-name buffer-file-name))
  "Root directory of the termlisp package.")

(add-to-list 'load-path (expand-file-name "vendor/cats" termlisp--root))

;; These soft requires must become hard requires in a later task, once all
;; modules exist.
(dolist (feature '(termlisp-base termlisp-reader termlisp-unify
                   termlisp-machine termlisp-pattern termlisp-builtins
                   termlisp-eval))
  (require feature nil t))

(defun termlisp-typecheck (string &optional env)
  "Typecheck STRING in ENV.  Implemented in Plan 2; returns ENV for now."
  (ignore string)
  (or env (termlisp-make-env)))

(provide 'termlisp)
;;; termlisp.el ends here
