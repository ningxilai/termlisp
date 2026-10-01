;;; termlisp-pattern.el --- Pattern parsing and matching -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A compiled pattern is a list whose car is a tag:
;;   (wild)            match anything, bind nothing
;;   (var . NAME)      bind NAME
;;   (lit . EXPR)      compare with value of EXPR
;;   (con . (NAME . SUBPATTERNS))
;;   (rest . NAME)     bind remaining sequence elements
;;   (lam . NAME)      bind a function value
;;   (guard SUBPAT EXPR)
;;   (or PAT...)
;;   (and PAT...)
;; `tl-match' returns a cons `(ok . bindings)' or nil.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-machine)

(cl-defstruct (tl-match-ctx (:constructor tl-make-match-ctx))
  force lit-eval guard-eval lambda-value)

(defun tl-pattern-parse (pat)
  "Parse surface pattern PAT into a compiled pattern."
  (cond
   ((eq pat '_) '(wild))
   ((symbolp pat) (cons 'var pat))
   ((and (consp pat) (eq (car pat) :literal)) (list 'lit (cadr pat)))
   ((and (consp pat) (eq (car pat) :list)) (cons 'rest (cadr pat)))
   ((and (consp pat) (eq (car pat) :lambda)) (cons 'lam (cadr pat)))
   ((and (consp pat) (eq (car pat) 'guard))
    (list 'guard (tl-pattern-parse (nth 1 pat)) (nth 2 pat)))
   ((and (consp pat) (eq (car pat) 'or))
    (cons 'or (mapcar #'tl-pattern-parse (cdr pat))))
   ((and (consp pat) (eq (car pat) 'and))
    (cons 'and (mapcar #'tl-pattern-parse (cdr pat))))
   ((consp pat)
    (cons 'con (cons (car pat) (mapcar #'tl-pattern-parse (cdr pat)))))
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
            (progn
              (setq bindings (cons (cons (cdr pat) values) bindings))
              (setq pats nil values nil))
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
