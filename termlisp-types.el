;;; termlisp-types.el --- HM type inference -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Types are either a type variable (a `tl-lvar') or a type constructor
;; application `tl-tcon'.  Substitutions are alists tvar -> type.  The type
;; unifier shares `tl-deref' with the term kernel and uses `tl-occurs-type' to
;; walk type constructors; like ACL2's one-way unifier, it leaves bindings
;; unchanged on failure.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-unify)

(cl-defstruct (tl-tcon (:constructor tl-tcon (name args))) name args)
(cl-defstruct (tl-tscheme (:constructor tl-tscheme (vars type))) vars type)

(defun tl-tvar-p (x) (tl-lvar-p x))
(defun tl-type-p (x) (or (tl-tvar-p x) (tl-tcon-p x)))

;; LEVEL is intentionally unused in Plan 2 (generalization uses tvars not free in the environment); reserved for level-based generalization in a later plan.
(defun tl-fresh-tvar (&optional level)
  "Return a fresh type variable."
  (tl-make-lvar (gensym "t") (or level 0)))

(defun tl-tarrow (a b) (tl-tcon '-> (list a b)))
(defun tl-tint () (tl-tcon 'Int nil))
(defun tl-tstring () (tl-tcon 'String nil))
(defun tl-tbool () (tl-tcon 'Bool nil))

(defun tl-tfun-args (ty)
  "If TY is `(-> a b)', return (a b), else nil."
  (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
    (tl-tcon-args ty)))

(defun tl-occurs-type (var type bindings)
  "Return non-nil if VAR occurs in TYPE under BINDINGS.
Like `tl-occurs', but traverses the argument types of a `tl-tcon'."
  (let ((work (list type)) (found nil))
    (while (and work (not found))
      (let ((t0 (tl-deref (pop work) bindings)))
        (cond ((eq t0 var) (setq found t))
              ((tl-tcon-p t0)
               (dolist (a (tl-tcon-args t0)) (push a work))))))
    found))

(defun tl-unify-types (a b bindings)
  "Unify types A and B under BINDINGS.  Return `(ok . bindings)'.
On failure returns `(nil . nil)'."
  (let ((pending (list (cons a b))) (ok t))
    (while (and pending ok)
      (let* ((pair (pop pending))
             (x (tl-deref (car pair) bindings))
             (y (tl-deref (cdr pair) bindings)))
        (cond
         ((eq x y))
         ((tl-tvar-p x)
          (if (tl-occurs-type x y bindings) (setq ok nil)
            (setq bindings (cons (cons x y) bindings))))
         ((tl-tvar-p y)
          (if (tl-occurs-type y x bindings) (setq ok nil)
            (setq bindings (cons (cons y x) bindings))))
         ((and (tl-tcon-p x) (tl-tcon-p y))
          (if (and (eq (tl-tcon-name x) (tl-tcon-name y))
                   (= (length (tl-tcon-args x)) (length (tl-tcon-args y))))
              (let ((ax (tl-tcon-args x)) (ay (tl-tcon-args y)))
                (while ax
                  (push (cons (car ax) (car ay)) pending)
                  (setq ax (cdr ax) ay (cdr ay))))
            (setq ok nil)))
         (t (setq ok nil)))))
    (if ok (cons t bindings) (cons nil nil))))

(defvar tl-type-parse-vars nil
  "Alist of type-variable symbols to type variables, bound during parsing.")

(defun tl-type-var-symbol-p (sym)
  "Return non-nil if SYM is a type variable (lowercase-initial)."
  (and (symbolp sym)
       (not (memq sym '(nil t)))
       (> (length (symbol-name sym)) 0)
       (let ((case-fold-search nil))
         (string-match-p "\\`[a-z]" (symbol-name sym)))))

(defun tl-split-arrow (sexp)
  "Split SEXP on `->' into its component type expressions."
  (let ((parts nil) (cur nil))
    (dolist (x sexp)
      (if (eq x '->)
          (progn
            (unless (consp cur)
              (signal 'termlisp-type-error
                      (list (format "Malformed arrow type: %S" sexp))))
            (push (nreverse cur) parts)
            (setq cur nil))
        (push x cur)))
    (unless (consp cur)
      (signal 'termlisp-type-error
              (list (format "Malformed arrow type: %S" sexp))))
    (push (nreverse cur) parts)
    (nreverse parts)))

(defun tl-type-parse-segment (segment)
  "Parse SEGMENT, one arrow operand's token list, into a type.
A single-token SEGMENT is that token; otherwise it is a constructor
application."
  (if (cdr segment)
      (tl-tcon (car segment) (mapcar #'tl-type-parse* (cdr segment)))
    (tl-type-parse* (car segment))))

(defun tl-type-parse-arrow (parts)
  "Parse PARTS as a right-associative arrow chain."
  (if (null (cdr parts))
      (tl-type-parse-segment (car parts))
    (tl-tarrow (tl-type-parse-segment (car parts))
               (tl-type-parse-arrow (cdr parts)))))

(defun tl-type-parse* (sexp)
  "Parse SEXP, sharing type variables via `tl-type-parse-vars'."
  (cond
   ((tl-type-var-symbol-p sexp)
    (let ((cell (assq sexp tl-type-parse-vars)))
      (if cell (cdr cell)
        (let ((tv (tl-fresh-tvar)))
          (push (cons sexp tv) tl-type-parse-vars)
          tv))))
   ((symbolp sexp) (tl-tcon sexp nil))
   ((and (consp sexp) (memq '-> sexp))
    (tl-type-parse-arrow (tl-split-arrow sexp)))
   ((consp sexp)
    (tl-tcon (car sexp) (mapcar #'tl-type-parse* (cdr sexp))))
   (t (signal 'termlisp-type-error (list (format "Bad type: %S" sexp))))))

(defun tl-type-parse (sexp)
  "Parse surface type expression SEXP into a type."
  (let ((tl-type-parse-vars nil))
    (tl-type-parse* sexp)))

(defun tl-free-tvars (type)
  "Return the list of type variables occurring in TYPE."
  (let ((acc nil))
    (cl-labels ((walk (node)
                  (cond ((tl-tvar-p node) (cl-pushnew node acc :test #'eq))
                        ((tl-tcon-p node) (mapc #'walk (tl-tcon-args node))))))
      (walk type))
    acc))

(defun tl-type-parse-scheme (sexp)
  "Parse SEXP into a type scheme, quantifying its free variables."
  (let ((ty (tl-type-parse sexp)))
    (tl-tscheme (tl-free-tvars ty) ty)))

(defun tl-type-subst (type sub)
  "Apply substitution SUB (alist tvar -> type) to TYPE."
  (cond
   ((tl-tvar-p type)
    (let ((cell (assq type sub))) (if cell (cdr cell) type)))
   ((tl-tcon-p type)
    (tl-tcon (tl-tcon-name type)
             (mapcar (lambda (arg) (tl-type-subst arg sub)) (tl-tcon-args type))))
   (t type)))

(defun tl-apply-bindings (type bindings)
  "Fully apply BINDINGS to TYPE."
  (let ((ty (tl-deref type bindings)))
    (if (tl-tcon-p ty)
        (tl-tcon (tl-tcon-name ty)
                 (mapcar (lambda (arg) (tl-apply-bindings arg bindings))
                         (tl-tcon-args ty)))
      ty)))

(defun tl-generalize (type env-tvars)
  "Generalize TYPE into a scheme, quantifying tvars not in ENV-TVARS."
  (let* ((ftv (tl-free-tvars type))
         (vars (cl-remove-if (lambda (v) (memq v env-tvars)) ftv)))
    (tl-tscheme vars type)))

(defun tl-instantiate (scheme)
  "Instantiate SCHEME (a `tl-tscheme') with fresh type variables."
  (if (tl-tscheme-p scheme)
      (let ((sub (mapcar (lambda (v) (cons v (tl-fresh-tvar)))
                         (tl-tscheme-vars scheme))))
        (tl-type-subst (tl-tscheme-type scheme) sub))
    scheme))

(defun tl-compose-bindings (b1 b2)
  "Compose substitutions B1 and B2 (apply B2 after B1).
Result is first-wins for `tl-deref' (assq); duplicate keys from B2 and
self-bindings are removed."
  (let ((composed
         (mapcar (lambda (cell)
                   (cons (car cell) (tl-apply-bindings (cdr cell) b2)))
                 b1))
        (rest (cl-remove-if (lambda (cell) (assq (car cell) b1)) b2)))
    (cl-remove-if (lambda (cell) (eq (car cell) (cdr cell)))
                  (append composed rest))))

(provide 'termlisp-types)
;;; termlisp-types.el ends here
