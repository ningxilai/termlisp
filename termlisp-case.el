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
(require 'termlisp-graph)

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

(defun tl-pat-match (pat node bindings)
  "Match compiled pattern PAT against graph NODE, extending BINDINGS.
Return `(t . bindings)' on success and nil on failure, following the
`tl-unify' convention.  BINDINGS is a proper alist mapping pattern
variables to nodes; a successful match with no bindings still returns a
truthy `(t)' so it is distinguishable from failure.

A `(pcon HEAD)' with no subpatterns matches a non-application node whose
head is `eq' to HEAD.  A zero-child application `(HEAD)' is deliberately
not matched, preserving the TGR distinction between the atom `HEAD' and
the nullary application `(HEAD)'."
  (pcase pat
    (`(pvar ,name)
     (let ((cell (assq name bindings)))
       (cond ((null cell) (cons t (cons (cons name node) bindings)))
             ((eq (cdr cell) node) (cons t bindings))
             (t nil))))
    (`(pwild) (cons t bindings))
    (`(plit ,value)
     (when (and (not (tl-node-application node))
                (equal (tl-node-head node) value))
       (cons t bindings)))
    (`(pnil)
     (when (and (not (tl-node-application node))
                (eq (tl-node-head node) nil))
       (cons t bindings)))
    (`(pcon ,head . ,pats)
     (if (null pats)
         (when (and (not (tl-node-application node))
                    (eq (tl-node-head node) head))
           (cons t bindings))
       (when (and (tl-node-application node)
                  (eq (tl-node-head node) head))
         (tl-pat-match-seq pats (tl-node-children node) bindings))))
    (`(pas ,name ,sub)
     (let ((r (tl-pat-match sub node bindings)))
       (when r
         (let ((cell (assq name (cdr r))))
           (cond ((null cell) (cons t (cons (cons name node) (cdr r))))
                 ((eq (cdr cell) node) r)
                 (t nil))))))
    (_ (signal 'termlisp-error (list (format "Bad compiled pattern: %S" pat))))))

(defun tl-pat-match-seq (pats nodes bindings)
  "Match PATS against NODES positionally, extending BINDINGS.
Exact arity is required; a leftover pattern or node fails the match."
  (let ((ok t))
    (while (and ok pats)
      (if (null nodes)
          (setq ok nil)
        (let ((r (tl-pat-match (car pats) (car nodes) bindings)))
          (if r
              (setq bindings (cdr r) pats (cdr pats) nodes (cdr nodes))
            (setq ok nil)))))
    (when (and ok (null pats) (null nodes))
      (cons t bindings))))

(provide 'termlisp-case)
;;; termlisp-case.el ends here
