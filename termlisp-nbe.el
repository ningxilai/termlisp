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
;; The engine underneath is `termlisp-graph''s: a function's clauses become
;; a clause-based rewrite rule, `termlisp-case' compiles them into a
;; decision tree so the first argument's constructor picks the clause
;; instead of every clause being tried in turn, and `tl-graph-rewrite' walks
;; the graph until nothing more applies.  What this module adds on top is
;; the environment a rule unfolds against and the reduction an argument
;; needs before its constructor is visible -- offered through
;; `tl-graph-whnf', the hook `termlisp-case' calls while it matches.  The
;; graph is rewritten copy-on-write, so normalising a type never edits the
;; type it came from.
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
(require 'termlisp-dpo)
(require 'termlisp-graph)
(require 'termlisp-graph-unify)
(require 'termlisp-types)

;; The clause struct is termlisp-eval's, and eval requires this file,
;; so it cannot be required back.  A batch byte-compile has eval loaded
;; by the time it reaches this file; native compilation compiles this
;; file alone in a fresh process, where only these declarations know the
;; accessors exist.
(declare-function tl-clause-params "termlisp-eval" (clause))
(declare-function tl-clause-body "termlisp-eval" (clause))

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

(defun tl-nbe-clauses (name nbe)
  "Return the clause list NAME has in NBE's environment, or nil.
`tl-env-functions' already maps a name to its list of clauses, so this
looks it up and nothing more."
  (and (symbolp name)
       (gethash name (tl-env-functions (tl-nbe-env nbe)))))

;;;; Rewriting rules

(defvar tl-nbe-fuel 100000
  "How many steps one reduction may take.
A type-level function that calls itself forever is a mistake in the
definition, not an invitation to hang Emacs; running out of fuel is
reported as a type error.")

(defvar tl-nbe--fuel nil
  "Remaining steps of the reduction in flight, as a cons cell, or nil.
Bound rather than passed down so that every nested reduction -- a match
that must reduce an argument before it can decide -- spends from the one
budget instead of opening a fresh one.")

(defvar tl-nbe--rule-tables (make-hash-table :test #'eq)
  "Environment -> hash of function name -> (CLAUSES . RULE).
A rule is rebuilt when the function's clause list changes identity, which
is what `tl-eval-define' hands out when it appends a clause, so a
redefinition is picked up without a second cache to invalidate by hand.")

(defun tl-nbe--spend ()
  "Take one step from the reduction budget, or signal when it is gone."
  (if (and tl-nbe--fuel (> (car tl-nbe--fuel) 0))
      (decf (car tl-nbe--fuel))
    (signal 'termlisp-type-error
            '("type-level reduction did not terminate"))))

(defun tl-nbe--type-pattern-p (pat)
  "Return non-nil when PAT is a pattern the type layer can match at all.
Guards, `or', `and', `:lambda', list-rest patterns and dot patterns are
value-level concerns with no meaning inside a type, so a clause built
from one could never be chosen; carrying it into the rule would only
give the decision tree a branch that must not be taken.

A dot is excluded for a reason the others are not.  Checking one
against a node means comparing two *terms*, and the comparison has to
happen in the environment the clause was written in -- the rule is
built before that environment is in hand, so the dotted term would be
carried around as an uninterpreted sexp and compared as one, which is
neither what it means nor what the value-level matcher does with it.
What the dot does buy the type layer it already gets elsewhere:
`tl-clause--pattern-term' hands the checker the dotted term, so the
codomain reduces under it.  Only the unfolding is given up, and only
for clauses that asked for a dot."
  (pcase (car-safe pat)
    ((or 'wild 'var 'lit) t)
    ('con (and (cl-every #'tl-nbe--type-pattern-p (cddr pat)) t))
    (_ nil)))

(defun tl-nbe--case-pattern (pat)
  "Return PAT written the way `termlisp-case' writes a compiled pattern.
A function's clauses are parsed by `tl-pattern-parse' because the
evaluator, the checker and the coverage pass all read them; the case tree
speaks `tl-pat-parse''s tags.  The two describe the same shapes under
different names, so this renames and nothing more."
  (pcase (car pat)
    ('wild '(pwild))
    ('var (list 'pvar (cdr pat)))
    ('lit (list 'plit (cadr pat)))
    ('con (cons 'pcon (cons (cadr pat)
                            (mapcar #'tl-nbe--case-pattern (cddr pat)))))
    (_ (signal 'termlisp-error
               (list (format "Not a type-level pattern: %S" pat))))))

(defun tl-nbe--template (clause)
  "Return the template that rebuilds CLAUSE's body once its pattern matched.
A function rather than a sexp because the body names its variables the
ordinary way -- `n', not `$n' -- and because `tl-nbe-subst' already knows
how to walk it, stop at a binder that redeclares one of those names, and
share every subtree the substitution does not touch.  Rebuilding the body
instead would hand back fresh leaves in place of the matched nodes, and a
fresh leaf is not the variable that was matched."
  (lambda (bindings)
    (tl-nbe-subst (tl-graph-root (tl-graph-build (tl-clause-body clause)))
                  bindings)))

(defun tl-nbe--make-rule (name clauses)
  "Return the rewrite rule that unfolds NAME from CLAUSES, or nil.
Clauses the type layer could never choose are dropped rather than kept as
dead branches, and a clause with no parameters is written so that it
matches the *application* `(NAME)' and not the bare name: the type layer
unfolds applications, and a function's name appearing by itself in a type
is not a call."
  (let ((kept nil))
    (dolist (clause clauses)
      (when (cl-every #'tl-nbe--type-pattern-p (tl-clause-params clause))
        (push clause kept)))
    (when kept
      (tl-make-crule
       name :normalize 0
       (mapcar (lambda (clause)
                 (let ((params (tl-clause-params clause)))
                   (cons (if params
                             (cons 'pcon (cons name (mapcar #'tl-nbe--case-pattern
                                                           params)))
                           (list 'pcon name '(pnil)))
                         (tl-nbe--template clause))))
               (nreverse kept))))))

(defun tl-nbe--rule (name nbe)
  "Return the rewrite rule unfolding NAME under NBE, or nil.
Compiled once per definition and reused, because the decision tree inside
it is the part worth keeping: `tl-graph-crule-match' memoises the tree on
the rule."
  (let ((clauses (tl-nbe-clauses name nbe)))
    (when clauses
      (let* ((table (or (gethash (tl-nbe-env nbe) tl-nbe--rule-tables)
                        (puthash (tl-nbe-env nbe) (make-hash-table :test #'eq)
                                 tl-nbe--rule-tables)))
             (entry (gethash name table)))
        (if (and entry (eq (car entry) clauses))
            (cdr entry)
          (let ((rule (tl-nbe--make-rule name clauses)))
            (puthash name (cons clauses rule) table)
            rule))))))

(defun tl-nbe--rules (nbe)
  "Return one rewrite rule per function NBE's environment can unfold.
The functions with nothing the type layer could match produce no rule and
are simply absent, which costs the dispatcher a hash lookup that misses."
  (let ((rules nil))
    (maphash (lambda (name _clauses)
               (let ((rule (tl-nbe--rule name nbe)))
                 (when rule (push rule rules))))
             (tl-env-functions (tl-nbe-env nbe)))
    rules))

(defun tl-nbe-unfold (node nbe)
  "Take one unfolding step on the function application NODE under NBE.
Return the reduct, or nil when no clause matches every argument -- a
term whose arguments are not yet known simply does not unfold.

Which clause applies is decided by the case tree `termlisp-case' compiles
from the function's clauses, so the first argument's constructor selects it
instead of every clause being tried in order.  Deciding still needs the
arguments reduced first, which is what the `tl-graph-whnf' bound here is
offered for: `(id Zero)' occupies an argument before it is known to be a
`Zero'."
  (let* ((head (tl-node-head node))
         (rule (and (symbolp head) (tl-nbe--rule head nbe)))
         (tl-graph-whnf (lambda (arg) (tl-nbe-whnf arg nbe))))
    (and rule (tl-graph-crule-reduce node rule))))

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
A term that cannot reduce is returned unchanged; stuck is normal.
Every reduction spends from one budget (`tl-nbe-fuel'), so a type-level
function that calls itself forever is reported as a type error rather
than hanging the session."
  (if tl-nbe--fuel
      (tl-nbe--whnf node nbe)
    (let ((tl-nbe--fuel (list tl-nbe-fuel)))
      (tl-nbe--whnf node nbe))))

(defun tl-nbe--whnf (node nbe)
  "Take NODE to weak head normal form under NBE, spending one step.
The budget in `tl-nbe--fuel' is bound by `tl-nbe-whnf', which is what makes
it shared by the reductions a match performs while it is deciding."
  (tl-nbe--spend)
  (let ((node (tl-gnode-deref node)))
    (if (not (tl-node-application node))
        (tl-nbe-resolve node nbe)
      (let* ((head (tl-node-head node))
             ;; A local's value stands in for the name; otherwise the
             ;; head itself when it is the type-level lambda, reached
             ;; so the test below can ask whether it beta-reduces;
             ;; otherwise the application as written.
             (cell (and (symbolp head)
                        (assq head (tl-nbe-locals nbe))))
             (target (cond (cell (cdr cell))
                           ((tl-node-p head) (tl-gnode-deref head))
                           (t node)))
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
          ;; Nothing moved: a local hands back its value and anything
          ;; else hands back the application itself -- never the head
          ;; alone, which was not what was asked for.
          (if cell (cdr cell) node))))))

(defun tl-nbe-nf (node nbe)
  "Reduce NODE to normal form under NBE.  Return a node.
Normalising is `tl-graph-rewrite' walking the node graph with the rules
NBE's environment provides: outermost first, one rule application at a
time, until nothing more applies.  A node a rule fits but cannot reduce is
left where it is -- stuck is a normal form -- and the walk is
copy-on-write, so the type NODE was taken from is never edited.  Fuel
bounds it, so a type-level function that never stops is reported as a type
error rather than hanging the session.

Weak head normal form is deliberately *not* this function: `tl-nbe-whnf'
stops at the outer constructor, which is what a comparison that only needs
to see which constructor it has must do."
  (let ((rules (tl-nbe--rules nbe))
        (tl-graph-whnf (lambda (arg) (tl-nbe-whnf arg nbe))))
    (if (null rules)
        node
      (tl-dpo-normalize node rules tl-nbe-fuel 'termlisp-type-error))))

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

(defvar tl-nbe-reduce-env nil
  "The environment unification reduces types in, or nil.
Bound around type checking so that `tl-nbe-reduce' knows which
definitions a type-level function may unfold to.  Nil means nothing is
reduced and unification compares structurally, which is what keeps
ordinary Hindley-Milner checking clear of any evaluator.")

(defun tl-nbe-reduce (node)
  "Return NODE's weak head normal form in `tl-nbe-reduce-env', or NODE.
This is what `tl-unify-reduce' calls when two types match nothing
structurally: a `Vec a (plus Zero n)' and a `Vec a n' look nothing alike
until the index is reduced.  With no environment bound there is nothing
to unfold a function against, so NODE comes back untouched and the
comparison proceeds as it always did."
  (if (null tl-nbe-reduce-env)
      node
    (tl-nbe-whnf node (tl-nbe tl-nbe-reduce-env nil))))

;; Installing here rather than in `termlisp-graph-unify' keeps the hook's
;; declaration and its implementation apart: the unifier says only that
;; two types *may* be equal after being reduced, and this module is what
;; supplies the reduction.  Loading `termlisp-nbe' is therefore what turns
;; definitional equality on -- a session that never loads it keeps
;; structural unification and no evaluator at all.
(setq tl-unify-reduce #'tl-nbe-reduce)

(provide 'termlisp-nbe)
;;; termlisp-nbe.el ends here
