;;; termlisp-unify.el --- Unification kernel -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Shared by pattern matching (open terms) and type inference.
;; A logic variable is a `tl-lvar' struct; bindings are an alist lvar -> term.
;;
;; The unifier is generic over the representation of compound values.  A
;; representation provides `tl-decompose' (split a compound into a head and a
;; proper list of children) and, for rebuilding, `tl-rebuild' (types) or
;; `tl-rebuild-term' (terms).  Terms are cons cells; types add a `tl-tcon'
;; method in `termlisp-types.el'.  This lets one unifier and one occurs check
;; serve both.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(cl-defstruct (tl-lvar (:constructor tl-make-lvar (id &optional level))) id (level 0))

(cl-defgeneric tl-decompose (x)
  "Return (HEAD . CHILDREN) if X is compound, else nil.
CHILDREN is always a proper list.")

(cl-defmethod tl-decompose ((x cons))
  "Decompose a term cell into its head and its single tail child."
  (cons (car x) (list (cdr x))))

(cl-defmethod tl-decompose (_x)
  "Atoms (and any other non-compound value) have no decomposition."
  nil)

(cl-defgeneric tl-rebuild (head children)
  "Rebuild a compound from HEAD and CHILDREN (inverse of `tl-decompose').")

(defun tl-rebuild-term (head children)
  "Rebuild a term cell from HEAD and its CHILDREN (inverse of `tl-decompose')."
  (cons head (car children)))

(defun tl-deref (term bindings)
  "Follow variable BINDINGS on TERM until a non-variable or unbound."
  (let (cell)
    (while (and (tl-lvar-p term)
                (setq cell (assq term bindings)))
      (setq term (cdr cell)))
    term))

(defun tl-occurs (var term bindings)
  "Return non-nil if VAR occurs in TERM under BINDINGS (generic).
Traverses compounds via `tl-decompose', so it works for both terms and types."
  (let ((work (list term)) (found nil))
    (while (and work (not found))
      (let* ((t0 (tl-deref (pop work) bindings))
             (d (tl-decompose t0)))
        (cond ((eq t0 var) (setq found t))
              (d (push (car d) work)
                 (dolist (c (cdr d)) (push c work))))))
    found))

(defun tl-unify-generic (a b bindings var-p occurs-check)
  "Generic worklist unifier.  VAR-P tests variables; OCCURS-CHECK enables
the occurs check.  Return `(ok . bindings)' (no-change-loser on failure)."
  (let ((pending (list (cons a b))) (ok t))
    (while (and pending ok)
      (let* ((pair (pop pending))
             (x (tl-deref (car pair) bindings))
             (y (tl-deref (cdr pair) bindings)))
        (cond
         ((eq x y))
         ((funcall var-p x)
          (if (and occurs-check (tl-occurs x y bindings)) (setq ok nil)
            (setq bindings (cons (cons x y) bindings))))
         ((funcall var-p y)
          (if (and occurs-check (tl-occurs y x bindings)) (setq ok nil)
            (setq bindings (cons (cons y x) bindings))))
         (t
          (let ((dx (tl-decompose x)) (dy (tl-decompose y)))
            (cond
             ((and dx dy)
              (push (cons (car dx) (car dy)) pending)
              (let ((cx (cdr dx)) (cy (cdr dy)))
                (if (= (length cx) (length cy))
                    (while cx
                      (push (cons (car cx) (car cy)) pending)
                      (setq cx (cdr cx) cy (cdr cy)))
                  (setq ok nil))))
             ((equal x y))
             (t (setq ok nil))))))))
    (if ok (cons t bindings) (cons nil nil))))

(defun tl-unify (a b bindings &optional occurs-check)
  "Unify A and B under BINDINGS.
Return a cons `(ok . bindings)'; ok is t on success, nil on failure.
On failure returns `(nil . nil)'; the bindings are not meaningful.
When OCCURS-CHECK is non-nil, reject cyclic bindings."
  (tl-unify-generic a b bindings #'tl-lvar-p occurs-check))

(provide 'termlisp-unify)
;;; termlisp-unify.el ends here
