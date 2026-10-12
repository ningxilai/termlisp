;;; termlisp-nbe.el --- type-layer reduction over the term graph -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Stage 2(c).  `tl-type-parse*' now lets terms appear inside types --
;; `Vec a (plus n m)' -- so types must be able to *compute*: two of them
;; are equal only if what they index by reduces to the same thing.
;;
;; This is normalization by rewriting rather than by evaluation.  A type
;; is reduced in place on the term graph: a beta redex or a function
;; application whose clause matches is replaced by its reduct, and the
;; result is reduced again.  Nothing is reified into a separate value
;; language, which is the point -- the decision page for this stage chose
;; the node representation precisely so that the reducer and the
;; unifier work on one structure instead of two (see
;; `DECISION-unified-term-graph.md').  `tl-gnode-subst''s sharing is what
;; keeps substitution from rebuilding what it does not have to.
;;
;; What is traded away is efficiency: rewriting substitutes afresh at
;; every step, so a term that a normalizer would evaluate in linear time
;; can blow up here.  Type-level terms in this system are small and the
;; reduction is memoized per node, so the trade is deliberate.
;;
;; A term that *cannot* reduce -- a Pi-bound variable applied to
;; something, say -- is simply returned unchanged.  Stuck is a normal
;; state, not an error: `plus n m' with `n' still unknown is exactly what
;; `append''s type looks like before it is called.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-graph)
(require 'termlisp-graph-unify)
(require 'termlisp-types)

(cl-defstruct (tl-nbe (:constructor tl-nbe (env locals)))
  "A reduction environment.
ENV is the `tl-env' holding the function clauses to unfold; LOCALS is an
alist from a variable's *name symbol* to the node it stands for.  Names
rather than nodes because that is what a clause's compiled patterns bind
-- the same discipline the value-level evaluator uses, so a function
means the same thing at the type level as it does at the value level."
  env (locals nil))

(defun tl-nbe-extend (nbe name node)
  "Return NBE with NAME bound to NODE."
  (tl-nbe (tl-nbe-env nbe) (cons (cons name node) (tl-nbe-locals nbe))))

(defun tl-nbe-resolve (node nbe)
  "Return what leaf NODE stands for in NBE, or NODE itself.
Only a leaf can stand for something: an application's head is resolved
separately, so `(plus n m)' is never mistaken for a binding."
  (if (and (tl-node-p node) (not (tl-node-application node))
           (not (tl-node-var-p node)))
      (let ((cell (assq (tl-node-head node) (tl-nbe-locals nbe))))
        (if cell (cdr cell) node))
    node))

(defun tl-nbe-subst (node locals)
  "Return NODE with each name in LOCALS replaced by the node it stands for.
Subtrees that contain none of those names are shared rather than
rebuilt, so a variable reached through the result is still the node it
was in NODE.  A `Pi' or `lambda' that rebinds one of those names
shadows it, and substitution stops there."
  (let ((memo (make-hash-table :test #'eq))
        (names (mapcar #'car locals)))
    (tl-nbe--go node locals memo names)))

(defun tl-nbe--go (node locals memo names)
  "Rebuild NODE substituting LOCALS, sharing what is unchanged.
MEMO is the node-to-copy table and NAMES the list of bound names."
  (let ((node (tl-gnode-deref node)))
    (cond
     ;; A leaf standing for one of the bound names.  Rigid (Pi/lambda)
     ;; binders are unification variables too, so the variable case is
     ;; not excluded here -- that is exactly what beta has to reach.
     ((and (tl-node-p node) (not (tl-node-application node))
           (memq (tl-node-head node) names))
      (cdr (assq (tl-node-head node) locals)))
     ((not (tl-node-application node)) node)
     ((memq (tl-node-head node) '(Pi lambda))
      (let* ((kids (tl-node-children node))
             (binder (and (car kids) (tl-node-head (car kids)))))
        (if (memq binder names)
            ;; Shadowed: this binder re-declares one of the names being
            ;; substituted, so nothing below it may be touched.
            node
          (tl-make-node (tl-node-head node)
                        (mapcar (lambda (k) (tl-nbe--go k locals memo names))
                                kids)
                        t))))
     (t (or (gethash node memo)
            (let ((new (tl-make-node
                        (tl-node-head node)
                        (mapcar (lambda (k) (tl-nbe--go k locals memo names))
                                (tl-node-children node))
                        t)))
              (puthash node new memo)
              new))))))

(defun tl-nbe-match (pat node nbe bindings)
  "Match compiled pattern PAT against NODE under NBE, extending BINDINGS.
Return `(ok . bindings)', where BINDINGS maps a pattern's name symbol to
the node it captured, or nil when PAT does not apply.  Only the pattern
forms a clause can actually take at the type level are handled: a
constructor, a name, a literal, and the wildcard.  Guards and `or' are
value-level concerns and have no meaning here."
  (pcase (car pat)
    ('wild (cons t bindings))
    ('var (cons t (cons (cons (cdr pat) node) bindings)))
    ('lit
     (let ((n (tl-nbe-whnf node nbe)))
       (when (and (tl-node-p n) (not (tl-node-var-p n))
                  (equal (tl-node-head n) (cadr pat)))
         (cons t bindings))))
    ('con
     (let* ((name (cadr pat))
            (subs (cddr pat))
            (n (tl-nbe-whnf node nbe)))
       (when (and (tl-node-p n) (not (tl-node-var-p n))
                  (eq (tl-node-head n) name))
         (let ((args (tl-node-children n))
               (bs bindings)
               (ok t))
           (unless (= (length args) (length subs)) (setq ok nil))
           (while (and ok subs args)
             (let ((r (tl-nbe-match (car subs) (car args) nbe bs)))
               (if r
                   (progn (setq bs (cdr r))
                          (setq args (cdr args))
                          (setq subs (cdr subs)))
                 (setq ok nil))))
           (when (and ok (null subs) (null args))
             (cons t bs))))))
    (_ nil)))

(defun tl-nbe-clauses (name nbe)
  "Return the clause list NAME has in NBE's environment, or nil.
`tl-env-functions' already maps a name to its list of clauses, so this
looks it up and nothing more."
  (and (symbolp name)
       (gethash name (tl-env-functions (tl-nbe-env nbe)))))

(defun tl-nbe-match-all (params args nbe bindings)
  "Match every pattern in PARAMS against the corresponding node in ARGS.
Return `(ok . bindings)' where BINDINGS maps each pattern's name symbol
to the node it captured, or nil when any pattern does not apply.  NBE is
threaded through because a pattern may have to reduce an argument before
it can tell whether it matches."
  (let ((bs bindings) (ps params) (as args) (ok t))
    (while (and ok ps as)
      (let ((r (tl-nbe-match (car ps) (car as) nbe bs)))
        (if r
            (setq bs (cdr r) ps (cdr ps) as (cdr as))
          (setq ok nil))))
    (and ok (null ps) (null as) (cons t bs))))

(defun tl-nbe-unfold (node nbe)
  "Take one unfolding step on the function application NODE under NBE.
Return the reduct, or nil when no clause matches every argument -- a
term whose arguments are not yet known simply does not unfold."
  (let ((clauses (tl-nbe-clauses (tl-node-head node) nbe))
        (args (tl-node-children node)))
    (catch 'tl-nbe-unfold
      (dolist (clause clauses)
        (let ((r (and (= (length (tl-clause-params clause)) (length args))
                      (tl-nbe-match-all (tl-clause-params clause) args nbe nil))))
          (when r
            (throw 'tl-nbe-unfold
                   (tl-nbe-subst
                    (tl-graph-root (tl-graph-build (tl-clause-body clause)))
                    (cdr r))))))
      nil)))

(defun tl-nbe-lambda-p (node)
  "Return non-nil when NODE is a type-level lambda application."
  (and (tl-node-p node) (eq (tl-node-head node) 'lambda)))

(defun tl-nbe-beta (lam args)
  "Beta-reduce the type-level lambda LAM applied to ARGS.
LAM is the lambda node that was reached as an application's head, so its
own children are the parameter and the body while ARGS are the
arguments; they are not in the same list.  Return the reduct, or nil
when LAM is not something that can be applied.  No environment is needed:
substitution is by name, and a lambda's parameter is not in scope
anywhere else."
  (let ((lp (tl-node-children lam)))
    (when (and (tl-nbe-lambda-p lam) (nth 1 lp) args)
      (tl-nbe-subst (nth 1 lp)
                    (list (cons (tl-node-head (car lp)) (car args)))))))

(defun tl-nbe-whnf (node nbe)
  "Reduce NODE to weak head normal form under NBE.  Return a node.
A term that cannot reduce is returned unchanged; stuck is normal."
  (let ((node (tl-gnode-deref node)))
    (if (not (tl-node-application node))
        (tl-nbe-resolve node nbe)
      (let* ((head (tl-node-head node))
             (target (if (symbolp head)
                         (let ((cell (assq head (tl-nbe-locals nbe))))
                           (if cell (cdr cell) node))
                       node))
             (reduced
              (cond
               ;; The head resolved to a type-level lambda: beta.  The
               ;; lambda is the *head*, so its children are parameter and
               ;; body while the application's children are the arguments.
               ((tl-nbe-lambda-p (tl-gnode-deref target))
                (tl-nbe-beta target (tl-node-children node)))
               ;; A named function with clauses: unfold one step, then
               ;; keep going in case the reduct reduces further.
               ((and (symbolp head) (tl-nbe-clauses head nbe))
                (tl-nbe-unfold node nbe))
               (t nil))))
        (if reduced
            (tl-nbe-whnf reduced nbe)
          target)))))

(defun tl-nbe-nf (node nbe)
  "Reduce NODE to normal form under NBE.  Return a node.
The result is shared where nothing was reduced, so normalizing a type
twice does not allocate twice."
  (let ((w (tl-nbe-whnf node nbe)))
    (if (not (tl-node-application w))
        w
      (let ((name (tl-node-head w))
            (args (tl-node-children w)))
        (if (memq name '(Pi lambda))
            ;; The binder is in scope in the body, and it stands for
            ;; itself: binding it to its own node is what stops an
            ;; outer name of the same spelling from reaching in.
            (let* ((binder (car args))
                   (inner (tl-nbe-extend nbe (tl-node-head binder) binder)))
              (tl-make-node name (mapcar (lambda (a) (tl-nbe-nf a inner)) args)
                            t))
          (tl-make-node name (mapcar (lambda (a) (tl-nbe-nf a nbe)) args)
                        (tl-node-application w)))))))

(defun tl-nbe-equal (a b nbe)
  "Return non-nil when A and B reduce to the same normal form under NBE.
This is definitional equality: `plus Zero n' and `n' are equal because
one reduces to the other, which is what makes `Vec a (plus Zero n)' and
`Vec a n' the same type.  Normal forms are compared with
`tl-canonical-key' so that free variables match up to renaming -- two
occurrences of the same unknown have no reason to carry the same name,
and insisting on it would make a type depend on how it was written."
  (equal (tl-canonical-key (tl-nbe-nf a nbe))
         (tl-canonical-key (tl-nbe-nf b nbe))))

(provide 'termlisp-nbe)
;;; termlisp-nbe.el ends here
