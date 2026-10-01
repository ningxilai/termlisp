;;; termlisp-elaborate.el --- Dictionary-passing elaboration -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Type-directed elaboration of class-method calls.  After type inference
;; resolves a method's class constraint to a concrete instance, each call
;; `(method arg...)' is rewritten to `(method DICT arg...)', where DICT is
;; the instance's runtime dictionary value (e.g. `FunctorMaybeDict').
;;
;; The pass runs per top-level form, immediately after inference:
;;
;;   1. inference is run with `tl-elab-sites' bound, recording every
;;      class-method call site together with the `tl-constraint' emitted
;;      for it;
;;   2. the final substitution (`tl-elab-bindings') is used to zonk each
;;      recorded constraint and match it against `tl-env-instance-env';
;;   3. the form is rebuilt, inserting the matched instance's dictionary.
;;
;; Because resolution is type-directed, calls whose class variable is
;; generalized (e.g. `(define (twice g x) (fmap g (fmap g x)))') have no
;; ground instance at definition time and are left unelaborated; those
;; would require a full dictionary-passing transform of polymorphic
;; functions, which is out of scope here.

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

(defun tl-elaborate-tree (env bindings form)
  "Rebuild FORM, inserting instance dictionaries at class-method calls.
BINDINGS is the substitution from the inference pass that produced
`tl-elab-sites'."
  (cond
   ((atom form) form)
   ((assq form tl-elab-sites)
    (let ((dict (tl-resolve-instance-dict
                 env (cdr (assq form tl-elab-sites)) bindings)))
      (if dict
          (cons (car form)
                (cons dict
                      (mapcar (lambda (arg) (tl-elaborate-tree env bindings arg))
                              (cdr form))))
        (cons (tl-elaborate-tree env bindings (car form))
              (tl-elaborate-tree env bindings (cdr form))))))
   (t (cons (tl-elaborate-tree env bindings (car form))
            (tl-elaborate-tree env bindings (cdr form))))))

(defun tl-desugar-do-tree (form)
  "Return FORM with every `(do ...)' subterm replaced by its desugaring.
Desugaring before inference (rather than letting `tl-infer' desugar
internally) ensures the `bind'/`return' application cons cells the
elaborator records are the same objects it later rewrites."
  (cond
   ((atom form) form)
   ((eq (car form) 'do) (tl-desugar-do-tree (tl-desugar-do form)))
   (t (cons (tl-desugar-do-tree (car form))
            (tl-desugar-do-tree (cdr form))))))

(defun tl-elaborate-form (env form)
  "Infer top-level FORM in ENV, then rewrite class-method calls.
Registration forms (`datatype', `class', `instance', signatures) are
handled here so they are available to inference; runtime evaluation of
`datatype' forms is left to `tl-eval-top'.  Any `do' subterm (top-level
or nested) is desugared first so its method calls are elaborated."
  (let ((form (tl-desugar-do-tree form))
        (tl-infer-constraints nil)
        (tl-elab-active t)
        (tl-elab-sites nil)
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
          (if tl-elab-sites
              (tl-elaborate-tree env tl-elab-bindings form)
            form))))
     (t
      (let ((r (tl-infer (cons nil env) form)))
        (tl-close-constraints env nil tl-infer-constraints (cdr r))
        (if tl-elab-sites
            (tl-elaborate-tree env (cdr r) form)
          form))))))

(provide 'termlisp-elaborate)
;;; termlisp-elaborate.el ends here
