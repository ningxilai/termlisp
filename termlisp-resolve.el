;;; termlisp-resolve.el --- Unification-driven overload resolution -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Resolve an overloaded operator by *unifying* the operand's type with
;; each candidate's parameter type, rather than by name/source-position
;; heuristics.  A pass on typed IR (the graph-backed HM types) can use
;; this to choose between a program's own method and a prelude operator
;; (e.g. a domain's `empty?' versus the list `empty?').
;;
;; Candidates are `(TAG . SCHEME)' pairs; the tag is whatever the caller
;; uses to name the resolved target (a builtin symbol, a mangled name, a
;; dictionary, ...).  Each candidate's scheme is instantiated afresh, so
;; the trial never mutates the operand type.

;;; Code:

(require 'cl-lib)
(require 'termlisp-types)

(defun tl-scheme-first-param (scheme)
  "Return the first parameter type node of arrow scheme SCHEME, or nil.
The scheme is instantiated so its quantified variables become fresh."
  (let ((ty (car (tl-instantiate-scheme scheme))))
    (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
      (car (tl-tcon-args ty)))))

(defun tl-resolve-overload (operand-type candidates)
  "Return the unique candidate tag whose parameter type unifies with
OPERAND-TYPE, or nil when none or several do.

CANDIDATES is a list of `(TAG . SCHEME)'.  Each trial unifies a fresh
instance of the candidate's first parameter with OPERAND-TYPE; a
variable candidate parameter only ever binds fresh variables, so the
operand type is left unchanged."
  (let (matches)
    (dolist (cand candidates)
      (let ((param (tl-scheme-first-param (cdr cand))))
        (when (and param (tl-gnode-unify param operand-type))
          (push (car cand) matches))))
    (when (= 1 (length matches))
      (car matches))))

(provide 'termlisp-resolve)
;;; termlisp-resolve.el ends here
