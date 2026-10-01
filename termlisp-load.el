;;; termlisp-load.el --- Load .tls files as elisp -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A `.tls' file is an Emacs Lisp file whose top-level forms are term-lisp
;; declarations (`datatype', `define', `class', `instance').  These macros
;; evaluate their quoted form in the current term-lisp environment, so
;; `(load "file.tls")' works like loading an elisp file.
;;
;; WARNING: this file defines global elisp macros named `datatype', `define',
;; `class' and `instance'.  `termlisp-load' must be required before loading
;; `.tls' files; while it is loaded those names are reserved and must not be
;; used for ordinary elisp definitions.
;;
;; The trailing file-local variable block (`mode: emacs-lisp') in a `.tls'
;; file is for editing only.  `load' does not process file-local variables,
;; so the block has no effect on evaluation; it just opens `.tls' files in
;; `emacs-lisp-mode'.

;;; Code:

(require 'termlisp-eval)

(defvar termlisp--load-env nil
  "Term-lisp environment used while loading `.tls' files.")

(defun termlisp--load-eval (form)
  "Evaluate the quoted term-lisp FORM in `termlisp--load-env'."
  (unless termlisp--load-env
    (setq termlisp--load-env (termlisp-make-env)))
  (termlisp-eval-form form termlisp--load-env))

(defmacro datatype (&rest args)
  "Declare a term-lisp datatype."
  `(termlisp--load-eval '(datatype ,@args)))

(defmacro define (&rest args)
  "Define a term-lisp function or constant."
  `(termlisp--load-eval '(define ,@args)))

(defmacro class (&rest args)
  "Declare a term-lisp type class."
  `(termlisp--load-eval '(class ,@args)))

(defmacro instance (&rest args)
  "Declare a term-lisp type class instance."
  `(termlisp--load-eval '(instance ,@args)))

(provide 'termlisp-load)
;;; termlisp-load.el ends here
