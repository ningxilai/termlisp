;;; termlisp-load.el --- Load .tls files as elisp -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A `.tls' file is an Emacs Lisp file whose top-level forms are term-lisp
;; declarations (`datatype', `define', `class', `instance', `rewrite') or
;; term-lisp expressions (`reduce').  These macros evaluate their quoted
;; form in the current term-lisp environment, so `(load "file.tls")' works
;; like loading an elisp file.
;;
;; WARNING: this file defines global elisp macros named `datatype', `define',
;; `class', `instance', `rewrite', `reduce' and `:'.  `termlisp-load' must
;; be required before loading `.tls' files; while it is loaded those names
;; are reserved and must not be used for ordinary elisp definitions.
;;
;; A `.tls' file starts with a magic string (see
;; `termlisp--magic-string') that opens it in `scheme-mode' -- the
;; language the file is written in, elisp being only how it is read.
;; `load' does not process the file-local variable part of the magic
;; string, so it has no effect on evaluation.
;;
;; The same reserved names are why this file opts out of definition
;; prefixes.  Generating autoloads collects a prefix for every
;; definition in the file, and `:' is one character long, which Emacs
;; refuses to register -- it prints `Not registering prefix ":"' and
;; drops the prefix, on every build.  A prefix exists to fetch a file
;; whose definitions are not loaded yet, and the WARNING above says
;; these names must be required before they are met rather than fetched
;; by accident.  The file-local `autoload-compute-prefixes: nil' after
;; the `ends here' line says that for the whole file, so the warning
;; goes away with the prefixes it was about.

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

(defmacro rewrite (&rest args)
  "Extend a term-lisp function with a preservation-checked clause.
ARGS is the `(NAME PATTERN...) BODY' extension to append to it."
  `(termlisp--load-eval '(rewrite ,@args)))

(defmacro reduce (&rest args)
  "Reduce a term-lisp TERM to normal form in the load environment.
ARGS is the one term to reduce."
  `(termlisp--load-eval '(reduce ,@args)))

(defmacro class (&rest args)
  "Declare a term-lisp type class."
  `(termlisp--load-eval '(class ,@args)))

(defmacro instance (&rest args)
  "Declare a term-lisp type class instance."
  `(termlisp--load-eval '(instance ,@args)))

(defmacro : (name type)
  "Declare term-lisp NAME's type as TYPE.
Inference cannot produce every type a definition deserves.  `sym' and
`trans' are the reason: each matches its proof against `Refl', and
without something to check against the refinement the pattern performs
is read back into the inferred type, so `sym' would come out with the
reflexive type `Eq a x x -> Eq a x x' instead of the general one.  The
signature is what says how much is being claimed.

The `:' inside a `datatype' -- `(VNil : (Vec a Zero))' -- is data, not a
call: the `datatype' macro quotes its arguments, so nothing here sees
it."
  `(termlisp--load-eval '(: ,name ,type)))

(provide 'termlisp-load)
;;; termlisp-load.el ends here

;; Local Variables:
;; autoload-compute-prefixes: nil
;; End:
