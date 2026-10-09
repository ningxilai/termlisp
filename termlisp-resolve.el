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

(defun tl-scheme-nth-param (scheme n)
  "Return the N-th parameter type node of arrow scheme SCHEME, or nil.
The scheme is instantiated so its quantified variables become fresh."
  (let ((ty (car (tl-instantiate-scheme scheme))))
    (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
      (nth n (tl-tcon-args ty)))))

(defun tl-scheme-first-param (scheme)
  "Return the first parameter type node of arrow scheme SCHEME, or nil."
  (tl-scheme-nth-param scheme 0))

(defun tl-resolve-overload-params (operand-type candidates)
  "Return the resolved tag for OPERAND-TYPE among CANDIDATES.
CANDIDATES is a list of `(TAG . PARAM-TYPE)'.  A candidate matches when
PARAM-TYPE unifies with OPERAND-TYPE.  Among the matches the most
specific wins: a candidate whose parameter is concrete (a constructor,
not a bare variable) beats a polymorphic one.  Returns nil when none
match or the specificity is ambiguous."
  (let ((specific nil) (any nil))
    (dolist (cand candidates)
      (let* ((param (cdr cand))
             ;; Specificity is judged before unifying, since unifying a
             ;; bare variable parameter would bind it.
             (specific-p (and param (not (tl-tvar-p param)))))
        (when (and param (tl-gnode-unify param operand-type))
          (push (car cand) any)
          (when specific-p
            (push (car cand) specific)))))
    (cond ((= 1 (length specific)) (car specific))
          ((null specific) (and (= 1 (length any)) (car any)))
          (t nil))))

(defun tl-resolve-overload (operand-type candidates)
  "Return the resolved tag for OPERAND-TYPE among CANDIDATES.
CANDIDATES is a list of `(TAG . SCHEME)'; each scheme's first parameter
type is the candidate's parameter."
  (tl-resolve-overload-params
   operand-type
   (mapcar (lambda (c) (cons (car c) (tl-scheme-first-param (cdr c))))
           candidates)))

(provide 'termlisp-resolve)
;;; termlisp-resolve.el ends here
