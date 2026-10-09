;;; termlisp-base.el --- Core types, errors, environment -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Shared definitions used by every other termlisp module.

;;; Code:

(require 'cl-lib)

(define-error 'termlisp-error "Term-lisp error")
(define-error 'termlisp-parse-error "Term-lisp parse error" 'termlisp-error)
(define-error 'termlisp-type-error "Term-lisp type error" 'termlisp-error)
(define-error 'termlisp-eval-error "Term-lisp evaluation error" 'termlisp-error)

(defconst termlisp-default-options
  '(:occurs-check nil :fuel 100000 :type-check nil :elaborate nil :phase B)
  "Default evaluation options.")

(cl-defstruct (tl-env (:constructor tl-env--make))
  "Term-lisp evaluation context."
  (functions (make-hash-table :test #'eq))
  (datatypes (make-hash-table :test #'eq))
  (constructors (make-hash-table :test #'eq))
  (type-env (make-hash-table :test #'eq))
  (sig-env (make-hash-table :test #'eq))
  (kind-env (make-hash-table :test #'eq))
  (class-env (make-hash-table :test #'eq))
  (instance-env (make-hash-table :test #'eq))
  (method-env (make-hash-table :test #'eq))
  (clauses (make-hash-table :test #'eq))
  (globals nil)
  (options termlisp-default-options))

(defun termlisp-make-env (&optional options)
  "Create a fresh evaluation environment, merging OPTIONS over defaults."
  (tl-env--make
   :options (append options (copy-sequence termlisp-default-options))))

(defun tl-env-option (env key &optional default)
  "Return option KEY of ENV, or DEFAULT if unset."
  (let ((plist (tl-env-options env)))
    (if (plist-member plist key)
        (plist-get plist key)
      default)))

(provide 'termlisp-base)
;;; termlisp-base.el ends here
