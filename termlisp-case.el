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
;;
;; `tl-case-compile' turns a list of `(PATTERN . TEMPLATE)' clauses into a
;; decision tree (an Idris `CaseBuilder'-style dispatcher):
;;   (ct-case COLUMN ALTS)     scrutinise position COLUMN
;;   (ct-leaf INDEX)           clause INDEX matched (first match wins)
;;   (ct-fail)                 no clause matches
;;   (ct-con HEAD ARITY TREE)  value is constructor HEAD applied to ARITY args
;;   (ct-const VALUE TREE)     value is the literal VALUE
;;   (ct-default TREE)         value is anything else (a variable clause)
;;
;; COLUMN addresses a position in a clause's flat pattern vector.  A clause
;; starts as the one-element vector (PATTERN); refining a constructor at
;; column C replaces that entry with the constructor's subpatterns, which
;; then occupy columns C..C+N-1, mirroring Idris's splicing of a
;; constructor's arguments into the pattern vector.
;;
;; `pas' is transparent to dispatch (its inner pattern decides the group).
;; All bindings, including the whole-subterm binding of a `pas', are
;; recovered when the winning clause's original pattern is matched, so the
;; tree only records the winning clause index.

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

(defun tl-pat-strip-pas (pat)
  "Return PAT with any outer `pas' wrappers removed."
  (while (eq (car-safe pat) 'pas)
    (setq pat (nth 2 pat)))
  pat)

(defun tl-pat-variable-p (pat)
  "Return non-nil when PAT is irrefutable (matches any value).
A `pvar', a `pwild', or a `pas' wrapping either is irrefutable.  `pas' is
transparent here because its binding is recovered when the winning clause
is matched, not while dispatching."
  (memq (car-safe (tl-pat-strip-pas pat)) '(pvar pwild)))

(defun tl-pat-dispatch-key (pat)
  "Return the dispatch key for refutable pattern PAT, or nil.
The key is `(con HEAD ARITY)' for a constructor, `(const VALUE)' for a
literal, and nil for an irrefutable pattern (see `tl-pat-variable-p')."
  (pcase (tl-pat-strip-pas pat)
    (`(pcon ,head . ,subs) (list 'con head (length subs)))
    (`(plit ,value) (list 'const value))
    (`(pnil) (list 'const nil))
    (_ nil)))

(defun tl-ct-refutable-column (rows)
  "Return the leftmost column holding a refutable pattern in ROWS, or nil.
Every ROW is `(PATTERNS . CLAUSE-INDEX)' and all rows have equal width."
  (let ((width (length (car (car rows))))
        (col nil)
        (c 0))
    (while (and (null col) (< c width))
      (when (cl-some (lambda (row)
                       (not (tl-pat-variable-p (nth c (car row)))))
                     rows)
        (setq col c))
      (setq c (1+ c)))
    col))

(defun tl-ct-row-drop (row col)
  "Return ROW with the pattern at COL removed."
  (cons (append (cl-subseq (car row) 0 col)
                (nthcdr (1+ col) (car row)))
        (cdr row)))

(defun tl-ct-row-refine (row col key)
  "Return ROW refined at COL for dispatch KEY.
A constructor key splices its subpatterns into COL; a constant key
consumes COL.  Any `pas' wrapper is stripped."
  (if (eq (car key) 'con)
      (let ((pat (tl-pat-strip-pas (nth col (car row)))))
        (cons (append (cl-subseq (car row) 0 col)
                      (cddr pat)
                      (nthcdr (1+ col) (car row)))
              (cdr row)))
    (tl-ct-row-drop row col)))

(defun tl-ct-row-specialize (row col key)
  "Return irrefutable ROW specialised at COL for dispatch KEY.
A constructor key replaces the variable with ARITY wildcards; a constant
key consumes COL.  Duplicating an irrefutable row into every constructor
alternative is what keeps an earlier catch-all ahead of a later
constructor (first match wins)."
  (if (eq (car key) 'con)
      (cons (append (cl-subseq (car row) 0 col)
                    (make-list (nth 2 key) '(pwild))
                    (nthcdr (1+ col) (car row)))
            (cdr row))
    (tl-ct-row-drop row col)))

(defun tl-ct-groups (rows col)
  "Group refutable ROWS by their dispatch key at COL.
Return an alist of (KEY . ROWS) in first-occurrence order."
  (let (groups)
    (dolist (row rows)
      (let* ((key (tl-pat-dispatch-key (nth col (car row))))
             (cell (assoc key groups)))
        (if cell
            (setcdr cell (append (cdr cell) (list row)))
          (setq groups (append groups (list (cons key (list row))))))))
    groups))

(defun tl-ct-alt (key subtree)
  "Build the constructor or constant alternative for KEY and SUBTREE."
  (pcase key
    (`(con ,head ,arity) (list 'ct-con head arity subtree))
    (`(const ,value) (list 'ct-const value subtree))))

(defun tl-ct-build-rows (rows)
  "Compile equal-width pattern ROWS into a decision tree.
Return `(ct-fail)' when ROWS is empty and `(ct-leaf INDEX)' when the first
row is irrefutable (it matches everything left to match)."
  (if (null rows)
      '(ct-fail)
    (let ((col (tl-ct-refutable-column rows)))
      (if (null col)
          (list 'ct-leaf (cdr (car rows)))
        (tl-ct-build-case col rows)))))

(defun tl-ct-build-case (col rows)
  "Compile ROWS by dispatching on column COL."
  (let (vars refs)
    (dolist (row rows)
      (if (tl-pat-variable-p (nth col (car row)))
          (setq vars (append vars (list row)))
        (setq refs (append refs (list row)))))
    (let ((alts nil))
      (dolist (group (tl-ct-groups refs col))
        (let* ((key (car group))
               (combined (append
                          (mapcar (lambda (r) (tl-ct-row-refine r col key))
                                  (cdr group))
                          (mapcar (lambda (r) (tl-ct-row-specialize r col key))
                                  vars))))
          (setq combined (sort combined (lambda (a b) (< (cdr a) (cdr b)))))
          (setq alts (append alts
                             (list (tl-ct-alt key (tl-ct-build-rows combined)))))))
      ;; The default alternative is taken without consuming COLUMN, so the
      ;; irrefutable rows keep their column and the later columns stay put.
      (when vars
        (setq alts (append alts
                           (list (list 'ct-default (tl-ct-build-rows vars))))))
      (list 'ct-case col alts))))

(defun tl-case-compile (clauses)
  "Compile CLAUSES into a decision tree.
Each clause is `(PATTERN . TEMPLATE)' where PATTERN is a compiled pattern
from `tl-pat-parse'.  Clauses are matched in order; the tree dispatches on
the leftmost column with a refutable pattern and, at a leaf, records the
index of the winning clause."
  (let ((rows nil)
        (index 0))
    (dolist (clause clauses)
      (setq rows (append rows (list (cons (list (car clause)) index))))
      (setq index (1+ index)))
    (tl-ct-build-rows rows)))

(provide 'termlisp-case)
;;; termlisp-case.el ends here
