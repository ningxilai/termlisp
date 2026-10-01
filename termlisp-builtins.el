;;; termlisp-builtins.el --- Primitive functions -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Builtins receive a list of already-forced argument values.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-machine)

(declare-function tl-force "termlisp-eval" (value))

(defun tl-force-or-identity (v)
  "Force V with `tl-force' when available, else return V."
  (if (and (tl-thunk-p v) (fboundp 'tl-force))
      (tl-force v)
    v))

(defvar tl-builtins (make-hash-table :test #'eq)
  "Registry mapping builtin names to functions of a list of values.")

(defun tl-builtin-p (name)
  "Return non-nil if NAME is a builtin."
  (gethash name tl-builtins))

(defun tl-register-builtin (name fn)
  "Register builtin NAME implemented by FN."
  (puthash name fn tl-builtins))

(defun tl-bool (b) (if b 'True 'False))

(defun tl-check-numbers (args name)
  "Signal `termlisp-type-error' unless ARGS is two numbers."
  (unless (= (length args) 2)
    (signal 'termlisp-type-error
            (list (format "%s expects 2 arguments, got %d" name (length args)))))
  (dolist (a args)
    (unless (numberp a)
      (signal 'termlisp-type-error
              (list (format "%s expects numbers, got %S" name a))))))

(tl-register-builtin 'eq
  (lambda (args)
    (tl-bool (tl-value-equal (nth 0 args) (nth 1 args) #'tl-force-or-identity))))
(tl-register-builtin '+
  (lambda (args) (tl-check-numbers args '+) (+ (nth 0 args) (nth 1 args))))
(tl-register-builtin '-
  (lambda (args) (tl-check-numbers args '-) (- (nth 0 args) (nth 1 args))))
(tl-register-builtin '*
  (lambda (args) (tl-check-numbers args '*) (* (nth 0 args) (nth 1 args))))
(tl-register-builtin '<
  (lambda (args) (tl-check-numbers args '<) (tl-bool (< (nth 0 args) (nth 1 args)))))

(provide 'termlisp-builtins)
;;; termlisp-builtins.el ends here
