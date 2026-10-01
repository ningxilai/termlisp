;;; termlisp-builtins.el --- Primitive functions -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Builtins receive a list of already-forced argument values.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(defvar tl-builtins (make-hash-table :test #'eq)
  "Registry mapping builtin names to functions of a list of values.")

(defun tl-builtin-p (name)
  "Return non-nil if NAME is a builtin."
  (gethash name tl-builtins))

(defun tl-register-builtin (name fn)
  "Register builtin NAME implemented by FN."
  (puthash name fn tl-builtins))

(defun tl-bool (b) (if b 'True 'False))

(tl-register-builtin 'eq
  (lambda (args) (tl-bool (equal (nth 0 args) (nth 1 args)))))
(tl-register-builtin '+
  (lambda (args) (+ (nth 0 args) (nth 1 args))))
(tl-register-builtin '-
  (lambda (args) (- (nth 0 args) (nth 1 args))))
(tl-register-builtin '*
  (lambda (args) (* (nth 0 args) (nth 1 args))))
(tl-register-builtin '<
  (lambda (args) (tl-bool (< (nth 0 args) (nth 1 args)))))

(provide 'termlisp-builtins)
;;; termlisp-builtins.el ends here
