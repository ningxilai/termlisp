;;; termlisp-pattern.el --- Pattern parsing and matching -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A compiled pattern is a list whose car is a tag:
;;   (wild)            match anything, bind nothing
;;   (var . NAME)      bind NAME
;;   (lit EXPR)        compare with value of EXPR
;;   (dot EXPR)        compare with value of EXPR, and say what it means
;;   (con . (NAME . SUBPATTERNS))
;;   (rest . NAME)     bind remaining sequence elements
;;   (lam . NAME)      bind a function value
;;   (guard SUBPAT EXPR)
;;   (or PAT...)
;;   (and PAT...)
;; `tl-match' returns a cons `(ok . bindings)' or nil.
;;
;; `lit' and `dot' run the same check -- evaluate the expression in the
;; definition's scope and compare it with the value on offer -- and are
;; still different patterns, because the checker reads them differently
;; and only one of them says what the value *is*.
;;
;; A literal is a constant the checker cannot enumerate: `(:literal 1)'
;; matches one value out of a type whose values it has no way to list,
;; so a column of literals can never be shown complete.  A dot is a
;; computed term, and the reason it exists is the opposite one.  It is
;; the programmer telling the checker what stands at a position that a
;; constructor pattern could not name -- a variable that must already be
;; *that* value, or an expression that has been reduced to one:
;;
;;   (define (f (:dot (plus n m))) ...)   ; only when the argument is
;;                                        ; already `plus n m' reduced
;;   (define (g (:dot k))) ...)           ; only when the argument is
;;                                        ; the value of `k', which is
;;                                        ; not a pattern otherwise --
;;                                        ; a bare `k' would bind it
;;
;; At the value level it constrains nothing that a literal would not.
;; What it buys is at the type level: `tl-clause--pattern-term' hands
;; the checker the term itself, so the codomain can reduce under it the
;; way it reduces under a constructor.  Without the dot there is no way
;; to say "assume this position is that term" -- the alternative is to
;; bind it and hope, which constrains nothing.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-machine)

(cl-defstruct (tl-match-ctx (:constructor tl-make-match-ctx))
  force lit-eval guard-eval lambda-value)

(defun tl-pattern-parse (pat &optional constructor-p)
  "Parse surface pattern PAT into a compiled pattern.
When CONSTRUCTOR-P is non-nil, a bare symbol satisfying it is parsed as a
nullary constructor pattern instead of a variable."
  (cond
   ((eq pat '_) '(wild))
   ((symbolp pat)
    (if (and constructor-p (funcall constructor-p pat))
        (list 'con pat)
      (cons 'var pat)))
   ((and (consp pat) (eq (car pat) :literal)) (list 'lit (cadr pat)))
   ;; Before the generic cons branch below, which would take `:dot' for a
   ;; constructor called `:dot' and parse its argument as a subpattern.
   ((and (consp pat) (eq (car pat) :dot)) (list 'dot (cadr pat)))
   ((and (consp pat) (eq (car pat) :list)) (cons 'rest (cadr pat)))
   ((and (consp pat) (eq (car pat) :lambda)) (cons 'lam (cadr pat)))
   ((and (consp pat) (eq (car pat) 'guard))
    (list 'guard (tl-pattern-parse (nth 1 pat) constructor-p) (nth 2 pat)))
   ((and (consp pat) (eq (car pat) 'or))
    (cons 'or (mapcar (lambda (p) (tl-pattern-parse p constructor-p)) (cdr pat))))
   ((and (consp pat) (eq (car pat) 'and))
    (cons 'and (mapcar (lambda (p) (tl-pattern-parse p constructor-p)) (cdr pat))))
   ((consp pat)
    (cons 'con (cons (car pat)
                     (mapcar (lambda (p) (tl-pattern-parse p constructor-p)) (cdr pat)))))
   (t (signal 'termlisp-error (list (format "Bad pattern: %S" pat))))))

(defun tl-match (pat value bindings ctx)
  "Match compiled pattern PAT against VALUE, extending BINDINGS.
Return `(ok . bindings)'.  CTX provides force/lit-eval/guard-eval/lambda-value."
  (pcase (car pat)
    ('wild (cons t bindings))
    ('var
     (let* ((name (cdr pat))
            (cell (assq name bindings)))
       (if cell
           (if (tl-value-equal (cdr cell) value (tl-match-ctx-force ctx))
               (cons t bindings)
             nil)
         (cons t (cons (cons name value) bindings)))))
    ('lit
     (let ((expected (funcall (tl-match-ctx-lit-eval ctx) (cadr pat))))
       (if (tl-value-equal expected value (tl-match-ctx-force ctx))
           (cons t bindings)
         nil)))
    ;; The same check as a literal, reached by a different road and
    ;; meaning a different thing.  The expression is evaluated in the
    ;; definition's scope, with no clause bindings in force -- a dot
    ;; cannot refer to a name this very pattern would bind, because
    ;; nothing it says is available until after it has been decided.
    ;; It binds nothing either: what it constrains is the value on
    ;; offer, not a name for it.  Running it through `lit-eval' rather
    ;; than a dot-specific hook is deliberate -- there is only one
    ;; expression to evaluate and one value to compare, and a second
    ;; hook would be a place for the two to drift apart.
    ('dot
     (let ((expected (funcall (tl-match-ctx-lit-eval ctx) (cadr pat))))
       (if (tl-value-equal expected value (tl-match-ctx-force ctx))
           (cons t bindings)
         nil)))
    ('con
     (let* ((name (cadr pat))
            (subpats (cddr pat))
            (v (funcall (tl-match-ctx-force ctx) value)))
       (cond
        ((null subpats)
         (when (eq v name) (cons t bindings)))
        ((and (consp v) (eq (car v) name))
         (tl-match-seq subpats (cdr v) bindings ctx))
        (t nil))))
    ('lam
     (cons t (cons (cons (cdr pat)
                         (funcall (tl-match-ctx-lambda-value ctx) value))
                   bindings)))
    ('guard
     (let ((r (tl-match (nth 1 pat) value bindings ctx)))
       (when r
         (let ((g (funcall (tl-match-ctx-guard-eval ctx) (nth 2 pat) (cdr r))))
           (when (tl-true-value-p g) r)))))
    ('or
     (let ((pats (cdr pat)) (result nil))
       (while (and pats (not result))
         (setq result (tl-match (car pats) value bindings ctx))
         (setq pats (cdr pats)))
       result))
    ('and
     (let ((pats (cdr pat)) (r (cons t bindings)) (ok t))
       (while (and pats ok)
         (setq r (tl-match (car pats) value (cdr r) ctx))
         (unless r (setq ok nil))
         (setq pats (cdr pats)))
       (when ok r)))
    (_ (signal 'termlisp-error (list (format "Bad compiled pattern: %S" pat))))))

(defun tl-match-seq (pats values bindings ctx)
  "Match PATS against VALUES; exact arity unless a `rest' pattern is present."
  (let ((ok t) (pats pats) (values values) (bindings bindings))
    (while (and pats ok)
      (let ((pat (car pats)))
        (if (eq (car pat) 'rest)
            (if (cdr pats)
                (signal 'termlisp-error
                        (list (format "`:list' pattern must be last: %S" pats)))
              (progn
                (setq bindings (cons (cons (cdr pat) values) bindings))
                (setq pats nil values nil)))
          (if (null values)
              (setq ok nil)
            (let ((r (tl-match pat (car values) bindings ctx)))
              (if r
                  (progn (setq bindings (cdr r))
                         (setq values (cdr values))
                         (setq pats (cdr pats)))
                (setq ok nil)))))))
    (when (and ok (null pats) (null values))
      (cons t bindings))))

(provide 'termlisp-pattern)
;;; termlisp-pattern.el ends here
