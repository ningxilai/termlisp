;;; termlisp-base.el --- Core types, errors, environment -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Shared definitions used by every other termlisp module: the error
;; hierarchy, the evaluation environment, and the pipeline option plist.
;;
;; Error model.  Every error the package signals derives from
;; `termlisp-error', so a caller may catch the whole family with a single
;; `(condition-case err BODY (termlisp-error ...))' or a specific phase:
;;
;;   termlisp-error            base
;;    +- termlisp-parse-error  `termlisp-reader'
;;    +- termlisp-type-error   `termlisp-types', `termlisp-kinds', ...
;;    +- termlisp-eval-error   `termlisp-eval', `termlisp-numeric', ...
;;    +- termlisp-abn-error    `termlisp-abn'
;;    +- termlisp-aldor-error  `termlisp-aldor'
;;    +- termlisp-emit-error   `termlisp-emit'
;;
;; Errors are signalled with a one-element list holding the message,
;; `(signal 'termlisp-type-error (list "...")))', so the `error-message'
;; of a caught condition is its `cadr'.  Errors that carry structured data
;; put it in the remaining list elements.

;;; Code:

(require 'cl-lib)

(defgroup termlisp nil
  "Lazy term-rewriting language and Aldor-to-Lisp compiler."
  :group 'languages
  :prefix "tl-")

(define-error 'termlisp-error "Term-lisp error")
(define-error 'termlisp-parse-error "Term-lisp parse error" 'termlisp-error)
(define-error 'termlisp-type-error "Term-lisp type error" 'termlisp-error)
(define-error 'termlisp-eval-error "Term-lisp evaluation error" 'termlisp-error)

(defconst termlisp-default-options
  '(:occurs-check nil :fuel 100000 :type-check nil :elaborate nil :phase B)
  "Default evaluation options.")

(defun tl-split-ctor (ctor)
  "Split constructor declaration CTOR into (FIELDS . RESULT).
CTOR has the shape (NAME ITEM...), where a top-level `:' introduces the
constructor's result type:

    (VCons a (Vec a n) : (Vec a (Succ n)))

Everything before the `:' is a field type and the single item after it
is the result type, so that a datatype can declare per-constructor
indices instead of forcing every constructor to return the datatype
applied to its parameters.  RESULT is nil when the declaration omits the
`:', which is how ordinary non-indexed datatypes are written; the caller
then defaults the result itself.  Anything other than exactly one item
after the `:' is an error, so a stray `:' cannot silently truncate a
constructor."
  (let ((items (cdr ctor)))
    (if (not (memq ': items))
        (cons items nil)
      (let ((at (cl-position ': items)))
        (unless (= at (- (length items) 2))
          (signal 'termlisp-type-error
                  (list (format "Constructor %S: `:' must be followed by exactly one result type"
                                (car ctor)))))
        (cons (cl-subseq items 0 at) (nth (1+ at) items))))))

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
  (options termlisp-default-options)
  (current nil))

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

(defun tl-env-resolve-current (env)
  "Return the current environment linked from ENV, or ENV itself."
  (or (tl-env-current env) env))

(provide 'termlisp-base)
;;; termlisp-base.el ends here
