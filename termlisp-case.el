;;; termlisp-case.el --- Case-tree matcher for the TGR -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A compiled pattern is a tagged list:
;;   (pvar NAME)       bind NAME
;;   (pwild)           match anything, bind nothing
;;   (plit VALUE)      match a literal VALUE
;;   (pcon HEAD PAT...) match constructor HEAD with subpatterns PAT...
;;   (pas NAME PAT)    match PAT and also bind the whole value to NAME
;;   (pnil)            match the empty list
;; `tl-pat-parse' turns surface patterns into these compiled patterns.

;;; Code:

(require 'termlisp-base)

(defun tl-pat-parse (sexp)
  "Parse surface pattern SEXP into a compiled pattern.
Signal `termlisp-error' on an unknown form."
  (pcase sexp
    (`(pvar ,name) (list 'pvar name))
    (`(pwild) '(pwild))
    (`(plit ,value) (list 'plit value))
    (`(pcon ,head . ,pats) (cons 'pcon (cons head (mapcar #'tl-pat-parse pats))))
    (`(pas ,name ,pat) (list 'pas name (tl-pat-parse pat)))
    (`(plist . ,pats) (tl-pat-parse-list pats))
    (_ (signal 'termlisp-error (list (format "Bad pattern: %S" sexp))))))

(defun tl-pat-parse-list (pats)
  "Parse PATS as the elements of a `plist' pattern into a cons/nil chain."
  (if (null pats)
      '(pnil)
    (list 'pcon 'cons (tl-pat-parse (car pats)) (tl-pat-parse-list (cdr pats)))))

(provide 'termlisp-case)
;;; termlisp-case.el ends here
