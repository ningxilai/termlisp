;;; termlisp.el --- Lazy term-rewriting language -*- lexical-binding: t; -*-

;; Copyright (C) 2026  The termlisp authors
;; SPDX-License-Identifier: GPL-3.0-or-later
;; Version: 0.1.0
;; Package-Requires: ((emacs "27.1") (cats "0.0.1"))
;; Keywords: languages, lisp, compilers

;; This file is part of termlisp.

;;; Commentary:
;; Embedded library API for term-lisp: a lazy term-rewriting language, and
;; a compiler from Aldor to Emacs Lisp via the ABN intermediate form.
;;
;; Loading this file loads the whole package.  The modules fall into a few
;; groups (required in dependency order):
;;
;;   core        base, reader, unify, machine, pattern, builtins, numeric
;;   types       types, kinds, graph-types, ir-types
;;   classes     resolve, elaborate
;;   runtime     eval, load
;;   term graph  graph, graph-unify, case
;;   Aldor       abn, emit, aldor, io
;;
;; The typical compilations pipeline is
;;
;;   .as --aldor -Fabn--> .abn --`tl-abn-read-file'--> ABN tree
;;       --`tl-aldor-lower'--> termlisp IR --`tl-emit-program'--> Lisp forms
;;
;; and the type layer (`tl-typecheck-ir', `tl-typecheck') is a Haskell-98-
;; style HM oracle with type classes over the shared term graph.  See
;; `termlisp-base' for the error hierarchy shared by every module.

;;; Code:

;;; Core language

(require 'termlisp-base)
(require 'termlisp-reader)
(require 'termlisp-unify)
(require 'termlisp-machine)
(require 'termlisp-pattern)
(require 'termlisp-builtins)
(require 'termlisp-numeric)

;;; Type system

(require 'termlisp-types)
(require 'termlisp-kinds)
(require 'termlisp-graph-types)
(require 'termlisp-ir-types)

;;; Type classes and dictionary passing

(require 'termlisp-resolve)
(require 'termlisp-elaborate)

;;; Evaluation

(require 'termlisp-eval)
(require 'termlisp-load)

;;; Term-graph rewriting

(require 'termlisp-graph)
(require 'termlisp-graph-unify)
(require 'termlisp-case)

;;; Aldor front end

(require 'termlisp-abn)
(require 'termlisp-emit)
(require 'termlisp-aldor)
(require 'termlisp-io)

;; The Reader monad depends on `cats'; load it when that dependency is
;; available.  The core language does not need it, so a missing `cats'
;; must not break loading termlisp (its own `require' would otherwise
;; signal through the optional `require').
(condition-case nil
    (require 'termlisp-data-reader)
  (error nil))

(provide 'termlisp)
;;; termlisp.el ends here
