;;; termlisp-unify.el --- Unification kernel -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Shared by pattern matching (open terms) and, in Plan 2, type inference.
;; A logic variable is a `tl-lvar' struct; bindings are an alist lvar -> term.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(cl-defstruct (tl-lvar (:constructor tl-make-lvar (id))) id)

(defun tl-deref (term bindings)
  "Follow variable BINDINGS on TERM until a non-variable or unbound."
  (let (cell)
    (while (and (tl-lvar-p term)
                (setq cell (assq term bindings)))
      (setq term (cdr cell)))
    term))

(defun tl-occurs (var term bindings)
  "Return non-nil if VAR occurs in TERM under BINDINGS."
  (let ((work (list term)) (found nil))
    (while (and work (not found))
      (let ((t0 (tl-deref (pop work) bindings)))
        (cond ((eq t0 var) (setq found t))
              ((consp t0)
               (push (car t0) work)
               (push (cdr t0) work)))))
    found))

(defun tl-unify (a b bindings &optional occurs-check)
  "Unify A and B under BINDINGS.
Return a cons `(ok . bindings)'; ok is t on success, nil on failure.
On failure returns `(nil . nil)'; the bindings are not meaningful.
When OCCURS-CHECK is non-nil, reject cyclic bindings."
  (let ((pending (list (cons a b))) (ok t))
    (while (and pending ok)
      (let* ((pair (pop pending))
             (x (tl-deref (car pair) bindings))
             (y (tl-deref (cdr pair) bindings)))
        (cond
         ((eq x y))
         ((tl-lvar-p x)
          (if (and occurs-check (tl-occurs x y bindings))
              (setq ok nil)
            (setq bindings (cons (cons x y) bindings))))
         ((tl-lvar-p y)
          (if (and occurs-check (tl-occurs y x bindings))
              (setq ok nil)
            (setq bindings (cons (cons y x) bindings))))
         ((and (consp x) (consp y))
          (push (cons (car x) (car y)) pending)
          (push (cons (cdr x) (cdr y)) pending))
         ((equal x y))
         (t (setq ok nil)))))
    (if ok (cons t bindings) (cons nil nil))))

(provide 'termlisp-unify)
;;; termlisp-unify.el ends here
