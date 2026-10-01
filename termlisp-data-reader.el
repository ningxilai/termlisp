;;; termlisp-data-reader.el --- Reader monad -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A cats-style Reader monad: a computation `env -> a'.

;;; Code:

(require 'cl-lib)
(require 'eieio)
(require 'cats-data-monad)
(require 'cats-data-applicative)
(require 'cats-data-functor)

(defclass tl-data-reader ()
  ((run :initarg :run :accessor tl-data-reader-run))
  :documentation "Reader monad: RUN is a function of the environment.")

(cl-defmethod cl-print-object ((this tl-data-reader) stream)
  "Print the object THIS to STREAM."
  (princ "#<tl-data-reader " stream)
  (cl-print-object (if (slot-boundp this 'run) (tl-data-reader-run this) nil) stream)
  (princ ">" stream))

(defun tl-reader-pure (v)
  "Return a Reader that ignores the environment and yields V."
  (tl-data-reader :run (lambda (_env) v)))

(defun tl-reader-ask ()
  "Return a Reader that yields the environment."
  (tl-data-reader :run #'identity))

(defun tl-reader-local (f m)
  "Run M under the environment transformed by F."
  (tl-data-reader :run (lambda (env)
                         (funcall (tl-data-reader-run m) (funcall f env)))))

(defun tl-run-reader (m env)
  "Run Reader M with ENV."
  (funcall (tl-data-reader-run m) env))

(cl-defmethod cats-pure ((_this tl-data-reader) v)
  (tl-reader-pure v))

(cl-defmethod cats-fmap (f (m tl-data-reader))
  (tl-data-reader :run (lambda (env) (funcall f (tl-run-reader m env)))))

(cl-defmethod cats-apply ((mf tl-data-reader) (mx tl-data-reader))
  (tl-data-reader :run (lambda (env)
                         (funcall (tl-run-reader mf env)
                                  (tl-run-reader mx env)))))

(cl-defmethod cats-bind ((m tl-data-reader) f)
  (tl-data-reader :run (lambda (env)
                         (tl-run-reader (funcall f (tl-run-reader m env)) env))))

(provide 'termlisp-data-reader)
;;; termlisp-data-reader.el ends here
