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

(require 'termlisp-base)
(require 'termlisp-reader)
(require 'termlisp-unify)
(require 'termlisp-machine)
(require 'termlisp-pattern)
(require 'termlisp-builtins)
(require 'termlisp-types)
(require 'termlisp-graph-types)
(require 'termlisp-ir-types)
(require 'termlisp-elaborate)
(require 'termlisp-eval)
(require 'termlisp-load)
(require 'termlisp-graph)
(require 'termlisp-graph-unify)
(require 'termlisp-case)
(require 'termlisp-abn)
(require 'termlisp-emit)
(require 'termlisp-aldor)
(require 'termlisp-io)

;; The Reader monad depends on the vendored cats library; load it when
;; available (the core language does not require it).
(require 'termlisp-data-reader nil t)

(provide 'termlisp)
;;; termlisp.el ends here
