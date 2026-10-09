;;; termlisp-elaborate.el --- Dictionary-passing elaboration -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Elaboration of class-method calls and dictionary passing.  After type
;; inference resolves a constraint to a concrete instance, each call
;; `(method arg...)' is rewritten to `(method DICT arg...)', where DICT is
;; the instance's runtime dictionary value (e.g. `FunctorMaybeDict').
;;
;; A *constrained* definition is additionally transformed into a
;; dictionary-passing one: its generalized class constraints become extra
;; dictionary parameters, and the method calls in its body that use those
;; constraints are rewritten to the corresponding parameter.  Calls to
;; such a function pass the dictionary resolved at the call site (a ground
;; instance) or the in-scope dictionary parameter (when the same
;; constraint is itself being passed through).
;;
;; The pass runs per top-level form:
;;   1. inference runs with `tl-elab-active' bound, recording method-call
;;      sites (`tl-elab-sites') and constrained-function call sites
;;      (`tl-elab-fn-sites');
;;   2. the final substitution (`tl-elab-bindings') zonks each constraint
;;      and either matches a given dictionary parameter or a ground
;;      instance (`tl-resolve-instance-dict', `tl-elab-given-dict');
;;   3. the form is rebuilt with the dictionaries inserted.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-types)

(declare-function tl-desugar-do "termlisp-eval" (form))

(defun tl-resolve-instance-dict (env constraint bindings)
  "Return the dictionary for CONSTRAINT solved in ENV under BINDINGS.
Return nil when the constraint type is not ground or has no instance."
  (let ((ty (tl-apply-bindings (tl-constraint-type constraint) bindings)))
    (when (null (tl-free-tvars ty))
      (let ((insts (gethash (tl-constraint-class constraint)
                            (tl-env-instance-env env)))
            (found nil))
        (while (and insts (not found))
          (when (tl-match-instance (tl-instance-head (car insts)) ty)
            (setq found (tl-instance-dict (car insts))))
          (setq insts (cdr insts)))
        found))))

(defun tl-elab-given-dict (constraint given)
  "Return the dictionary parameter for CONSTRAINT in GIVEN, or nil.
GIVEN is an alist of constraint key -> dictionary parameter symbol."
  (cdr (assoc (tl-constraint-canonical-key constraint) given)))

(defun tl-elaborate-tree (env bindings form given)
  "Rebuild FORM, inserting dictionaries at method and function call sites.
BINDINGS is the substitution from the inference pass; GIVEN maps the
enclosing define's constraints to their dictionary parameters."
  (cond
   ((atom form) form)
   ;; A class-method call: a given dictionary or a resolved instance one.
   ((assq form tl-elab-sites)
    (let* ((c (cdr (assq form tl-elab-sites)))
           (dict (or (tl-elab-given-dict c given)
                     (tl-resolve-instance-dict env c bindings))))
      (if dict
          (cons (car form)
                (cons dict
                      (mapcar (lambda (a) (tl-elaborate-tree env bindings a given))
                              (cdr form))))
        (cons (car form)
              (mapcar (lambda (a) (tl-elaborate-tree env bindings a given))
                      (cdr form))))))
   ;; A call to a constrained function: pass each dictionary.
   ((assq form tl-elab-fn-sites)
    (let* ((cs (cdr (assq form tl-elab-fn-sites)))
           (dicts (mapcar (lambda (c)
                            (or (tl-elab-given-dict c given)
                                (tl-resolve-instance-dict env c bindings)))
                          cs)))
      (cons (car form)
            (append dicts
                    (mapcar (lambda (a) (tl-elaborate-tree env bindings a given))
                            (cdr form))))))
   (t (cons (tl-elaborate-tree env bindings (car form) given)
            (tl-elaborate-tree env bindings (cdr form) given)))))

(defun tl-elaborate-constrained-define (env form target cs)
  "Rewrite a constrained definition FORM with dictionary parameters.
TARGET is the define's `(NAME . PARAMS)'; CS are its generalized class
constraints.  Return the transformed define."
  (let ((given nil) (dicts nil) (i 0))
    (dolist (c cs)
      (let ((key (tl-constraint-canonical-key c)))
        (unless (assoc key given)
          (let ((dn (intern (format "$d%s%d" (tl-constraint-class c) i))))
            (setq i (1+ i))
            (push (cons key dn) given)
            (push dn dicts)))))
    (setq dicts (nreverse dicts))
    (cons 'define
          (cons (cons (car target) (append dicts (cdr target)))
                (list (tl-elaborate-tree env tl-elab-bindings
                                         (caddr form) given))))))

(defun tl-desugar-do-tree (form)
  "Return FORM with every `(do ...)' subterm replaced by its desugaring."
  (cond
   ((atom form) form)
   ((eq (car form) 'do) (tl-desugar-do-tree (tl-desugar-do form)))
   (t (cons (tl-desugar-do-tree (car form))
            (tl-desugar-do-tree (cdr form))))))

(defun tl-elaborate-form (env form)
  "Infer top-level FORM in ENV, then apply dictionary-passing elaboration."
  (let ((form (tl-desugar-do-tree form))
        (tl-infer-constraints nil)
        (tl-occurrence-check (tl-env-option env :occurs-check))
        (tl-elab-active t)
        (tl-elab-sites nil)
        (tl-elab-fn-sites nil)
        (tl-elab-bindings nil))
    (cond
     ((and (consp form) (memq (car form) '(datatype datatype-extension))) form)
     ((and (consp form) (eq (car form) ':)) (tl-register-signature env form) form)
     ((and (consp form) (eq (car form) 'class)) (tl-register-class env form) form)
     ((and (consp form) (eq (car form) 'instance)) (tl-register-instance env form) form)
     ((and (consp form) (eq (car form) 'define))
      (let ((target (cadr form)))
        (if (and (consp target) (gethash (car target) (tl-env-method-env env)))
            form
          (tl-typecheck-define env form)
          (let* ((name (if (consp target) (car target) target))
                 (scheme (gethash name (tl-env-type-env env)))
                 (cs (and (tl-tscheme-p scheme) (tl-tscheme-constraints scheme))))
            (cond
             ((and cs (consp target))
              (tl-elaborate-constrained-define env form target cs))
             ((or tl-elab-sites tl-elab-fn-sites)
              (tl-elaborate-tree env tl-elab-bindings form nil))
             (t form))))))
     (t
      (let ((r (tl-infer (cons nil env) form)))
        (tl-close-constraints env nil tl-infer-constraints (cdr r) t)
        (if (or tl-elab-sites tl-elab-fn-sites)
            (tl-elaborate-tree env (cdr r) form nil)
          form))))))

(provide 'termlisp-elaborate)
;;; termlisp-elaborate.el ends here
