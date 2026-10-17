;;; termlisp-eval.el --- Evaluator -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; CEK-style evaluator.  Function application and forcing a variable-bound
;; thunk are tail steps in the driver loop (TCO); arguments become memoized
;; thunks forced on demand (laziness).

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-reader)
(require 'termlisp-machine)
(require 'termlisp-pattern)
(require 'termlisp-builtins)
(require 'termlisp-types)
(require 'termlisp-elaborate)
;; The builtin type schemes (`seq', `first', ...) register themselves
;; when `termlisp-ir-types' loads, and this is the layer that needs
;; them: `tl-typecheck-form' falls back to that table for any global the
;; environment does not define, and `termlisp-load-prelude' walks the
;; prelude -- which calls `seq' -- through this module's `:type-check'
;; path.  Requiring it from the umbrella alone is what let a fresh image
;; with `termlisp-load' alone die of "Unknown symbol: seq".
(require 'termlisp-ir-types)
;; The unifier reduces types through this module's `tl-nbe-reduce'
;; whenever two types match nothing structurally.  Requiring it here (and
;; not from `termlisp-graph-unify', which it depends on) is what keeps the
;; dependency pointing the right way: the unifier declares a hook, the
;; layer that owns an evaluator fills it in.
(require 'termlisp-nbe)
;; The rewrite gate in this module is where a clause pays for the two
;; obligations a value verdict cannot speak for: `tl-kind-preserve-check'
;; asks whether the rule preserves the kinds of the types it could be
;; unfolded inside, and the locality trial runs the rule through
;; `tl-dpo-normalize'.  Both are kind-level questions, and kinds is
;; where their checker lives; the dependency is acyclic (kinds needs
;; only `termlisp-types').
(require 'termlisp-kinds)

(define-error 'termlisp-hole "Unsolved goal")
;; Inheriting from `error' and not from `termlisp-type-error' is
;; deliberate: a hole is not a mistake in the program, it is the program
;; asking a question, and a caller that handles type errors should not
;; find goals arriving inside that handling.

(defvar termlisp--current-env nil
  "Dynamically bound evaluation context during `tl-run'.")

(defvar termlisp--load-env nil
  "Term-lisp environment used while loading `.tls' files.
Defined in `termlisp-load.el'; declared here so `termlisp-load-prelude'
byte-compiles without a free-variable warning.")

(defconst termlisp--magic-string
  ";;; -*- lexical-binding: t; mode: scheme; -*-"
  "First-line magic string marking a term-lisp (.tls) source file.
It names `scheme-mode' because that is the language the file is
written in; it is only read as elisp.  `load' ignores the file-local
part, so the line decides how the buffer looks and nothing else.")

;;; Thunks ---------------------------------------------------------------

(defun tl-force (value)
  "Force VALUE to weak head normal form; memoize if it is a thunk."
  (cond
   ((not (tl-thunk-p value)) value)
   ((tl-thunk-forced-p value) (tl-thunk-value value))
   ((tl-thunk-busy-p value)
    (signal 'termlisp-eval-error '("<<loop>> detected while forcing a thunk")))
   (t
    (setf (tl-thunk-busy-p value) t)
    (let ((saved termlisp--current-env))
      (unwind-protect
          (let* ((termlisp--current-env
                  (or (tl-thunk-ctx value)
                      (and (tl-thunk-env value)
                           (tl-env-resolve-current (tl-thunk-env value)))
                      termlisp--current-env))
                 (v (tl-run (tl-thunk-expr value) (tl-thunk-env value))))
            (setf (tl-thunk-value value) v)
            (setf (tl-thunk-forced-p value) t)
            v)
        (setq termlisp--current-env saved)
        (setf (tl-thunk-busy-p value) nil))))))

(defun tl-make-arg-thunks (exprs env)
  "Turn argument expressions EXPRS into thunks capturing ENV."
  (mapcar (lambda (e) (tl-make-thunk e env)) exprs))

;;; Lambda application ---------------------------------------------------

(defun tl-bind-params (params args base-env caller-env)
  "Extend BASE-ENV binding PARAMS to thunks of ARGS evaluated in CALLER-ENV."
  (let ((new base-env) (params params) (args args))
    (while params
      (push (cons (car params) (tl-make-thunk (car args) caller-env)) new)
      (setq params (cdr params) args (cdr args)))
    new))

;;; Clause selection -----------------------------------------------------

(cl-defstruct (tl-clause (:constructor tl-make-clause (name params body)))
  name params body)

(defun tl-match-ctx-for-eval ()
  "Build a match context that forces thunks and evaluates literals/guards."
  (tl-make-match-ctx
   :force #'tl-force
   :lit-eval (lambda (expr) (tl-run expr nil))
   :guard-eval (lambda (expr bindings) (tl-run expr bindings))
   :lambda-value
   (lambda (value)
     (let ((v (tl-force value)))
       (cond
        ((tl-closure-p v) v)
        ((tl-function-p v) v)
        ((and (symbolp v)
              (gethash v (tl-env-functions termlisp--current-env)))
         (tl-make-function (gethash v (tl-env-functions termlisp--current-env))))
        (t v))))))

(defun tl-select-clause (clauses arg-thunks)
  "Return `(clause . bindings)' for the first matching CLAUSES, or nil."
  (let ((ctx (tl-match-ctx-for-eval)) (result nil))
    (while (and clauses (not result))
      (let ((r (tl-match-seq (tl-clause-params (car clauses)) arg-thunks nil ctx)))
        (when r
          (setq result (cons (car clauses) (cdr r)))))
      (setq clauses (cdr clauses)))
    result))

(defun tl-apply-step (fv args caller-env)
  "Return `(BODY . ENV)' to continue applying FV to ARGS, or signal."
  (cond
   ((tl-closure-p fv)
    (cons (tl-closure-body fv)
          (tl-bind-params (tl-closure-params fv) args (tl-closure-env fv) caller-env)))
   ((tl-function-p fv)
    (let ((sel (tl-select-clause (tl-function-clauses fv)
                                 (tl-make-arg-thunks args caller-env))))
      (if sel
          (cons (tl-clause-body (car sel)) (cdr sel))
        (signal 'termlisp-eval-error '("No matching clause for function value")))))
   (t (signal 'termlisp-eval-error
              (list (format "Not a function: %S" fv))))))

(defun tl-resolve-callable (fv)
  "Resolve FV to a closure/function object, or return it unchanged."
  (cond
   ((tl-closure-p fv) fv)
   ((tl-function-p fv) fv)
   ((and (symbolp fv) (gethash fv (tl-env-functions termlisp--current-env)))
    (tl-make-function (gethash fv (tl-env-functions termlisp--current-env))))
   (t fv)))

;;; do-notation ----------------------------------------------------------

(defun tl-do-has-dict-p (form)
  "Non-nil if FORM is `(do DICT STMT...)' (explicit monad operand)."
  (let ((second (cadr form)))
    (not (or (and (consp second) (eq (cadr second) '<-))
             (and (consp second) (eq (car second) 'return))))))

(defun tl-seq-begin (forms)
  "Fold FORMS into a single expression using the strict `seq' builtin.
The last form's value is returned; earlier forms are forced for their side
effects.  A single form is returned unchanged."
  (if (null (cdr forms))
      (car forms)
    (let ((acc (car (last forms))))
      (dolist (f (reverse (butlast forms)))
        (setq acc (list 'seq f acc)))
      acc)))

(defun tl-let-check-form (form)
  "Signal unless FORM is a well-shaped `(let ((NAME EXPR)...) BODY...)'.
The evaluator reaches a `let' through `tl-desugar-let'; inference no
longer does, because it hands the bindings to `tl-infer-ir-Let' instead
of wrapping them in a lambda.  Both ask the same questions of the same
form, so the questions live here once -- otherwise a malformed binding
reaches inference as an elisp `wrong-type-argument' where the evaluator
used to raise a termlisp error."
  (let ((bindings (cadr form)) (body (cddr form)))
    (when (and bindings (not (listp bindings)))
      (signal 'termlisp-eval-error '("let requires a binding list")))
    (dolist (b bindings)
      (unless (and (consp b) (consp (cdr b)) (null (cddr b)))
        (signal 'termlisp-eval-error
                (list (format "Invalid let binding: %S" b)))))
    (unless body
      (signal 'termlisp-eval-error '("let requires a body")))))

(defun tl-desugar-let (form)
  "Desugar FORM `(let ((NAME EXPR)...) BODY...)' into an inline-lambda application.
Bindings are sequential, so each EXPR is evaluated in the enclosing scope and
the names are bound together, matching Scheme's `let'.  The body is an
implicit `begin', returning its last expression.

This is the *evaluator's* lowering.  Inference does not come this way:
it keeps the bindings as bindings so that `tl-infer-ir-Let' can quantify
the ones worth quantifying, where a lambda application admits no
generalization at all."
  (tl-let-check-form form)
  (let ((bindings (cadr form)) (body (cddr form)) (names nil) (exprs nil))
    (dolist (b bindings)
      (push (car b) names)
      (push (cadr b) exprs))
    (cons (list 'lambda (nreverse names) (tl-seq-begin body))
          (nreverse exprs))))

(defun tl-desugar-list (form)
  "Desugar FORM `(list EXPR...)' into nested `Cons' applications.
`(list)' becomes `Nil'.  Coalton's `make'/`make-list' expand the same way:
a variadic form has no fixed arity to give a Hindley-Milner scheme, so it is
rewritten into constructor applications *before* inference, where `Cons'
already has one.  The result type is a homogeneous `List' of the elements'
type."
  (let ((acc 'Nil))
    (dolist (x (reverse (cdr form)) acc)
      (setq acc (list 'Cons x acc)))))

(defun tl-desugar-do-method (form)
  "Desugar `(do STMT...)' to `bind'/`return' class-method calls.
The monad type is left to inference; the elaborator inserts the resolved
instance dictionary at each method call site."
  (let* ((stmts (cdr form))
         (last (car (last stmts)))
         (init (butlast stmts))
         (acc nil))
    (unless (and (consp last) (eq (car last) 'return))
      (signal 'termlisp-eval-error '("do block must end with (return e)")))
    (setq acc (list 'return (cadr last)))
    (dolist (stmt (reverse init))
      (if (and (consp stmt) (eq (cadr stmt) '<-))
          (setq acc (list 'bind (caddr stmt) (list 'lambda (list (car stmt)) acc)))
        (setq acc (list 'bind stmt (list 'lambda (list (gensym "ignored")) acc)))))
    acc))

(defun tl-desugar-do (form)
  "Desugar `(do ...)' into nested bind/return calls.
With an explicit dictionary, `(do DICT STMT...)' becomes
monad-bind/monad-return calls; without one, `(do STMT...)' becomes
class-method `bind'/`return' calls for type-directed elaboration.  Each STMT
is `(NAME <- EXPR)' or a bare monadic expression; the block must end with
`(return EXPR)'.  The block is desugared here so it may appear as a top-level
or nested `do' form (handled in `tl-eval-top' and `tl-run')."
  (if (tl-do-has-dict-p form)
      (let* ((dict (cadr form))
             (stmts (cddr form))
             (last (car (last stmts)))
             (init (butlast stmts))
             (acc nil))
        (unless (and (consp last) (eq (car last) 'return))
          (signal 'termlisp-eval-error '("do block must end with (return e)")))
        (setq acc (list 'monad-return dict (cadr last)))
        (dolist (stmt (reverse init))
          (if (and (consp stmt) (eq (cadr stmt) '<-))
              (setq acc (list 'monad-bind dict (caddr stmt)
                              (list 'lambda (list (car stmt)) acc)))
            (setq acc (list 'monad-bind dict stmt
                            (list 'lambda (list (gensym "ignored")) acc)))))
        acc)
    (tl-desugar-do-method form)))

(defun tl-reduce--term (term)
  "Rewrite the `list' and `do' forms in TERM the way inference reads them.
Both are forms inference expands before it types them -- `list' into
constructor applications, `do' into its `bind'/`return' calls -- and a
reduction whose type side sees one spelling while the graph is built
from another would be answering about two different terms.  `let' and
`lambda' are left alone: inference keeps `let' as a binding, and
neither it nor a lambda is an application any rewrite rule of this
environment speaks about, so they stand in the term as written."
  (cl-labels ((walk (x)
                (cond
                 ((atom x) x)
                 ((eq (car x) 'list) (walk (tl-desugar-list x)))
                 ((eq (car x) 'do) (walk (tl-desugar-do x)))
                 (t (cons (walk (car x)) (walk (cdr x)))))))
    (walk term)))

(defun tl-reduce-term (term env)
  "Return the normal form of TERM under ENV's rewrite rules, as a term.
TERM is read as a term, not evaluated: it goes into a graph the way it
is written, every function of ENV that the type layer can read unfolds
through `tl-dpo-normalize' -- the same unfolding `tl-nbe-nf' performs,
the same `tl-graph-whnf' hooked to the same `tl-nbe-whnf' -- and the
graph is rendered back.  A name nothing unfolds stays as itself, so an
open term comes back open and a free variable is not mistaken for
anything it might be bound to later.  This is what a rewrite rule is
asked of at the value level: not `is this argument already a value',
which forcing answers, but what the rules do with the term underneath
the values.

The walk is bounded by the environment's `:fuel', and exhaustion
signals `termlisp-eval-error' -- a rewrite that will not stop is what
that error class is for.  The verdict of the DPO gluing condition, if
any cut along the way was not local, is left in `tl-dpo-last-gluing'."
  (let* ((nbe (tl-nbe env nil))
         (rules (tl-nbe--rules nbe))
         (tl-graph-whnf (lambda (arg) (tl-nbe-whnf arg nbe))))
    (tl-node->sexp
     (tl-dpo-normalize (tl-graph-root (tl-graph-build (tl-reduce--term term)))
                       rules
                       (or (tl-env-option env :fuel) 100000)
                       'termlisp-eval-error))))

;;; Driver ---------------------------------------------------------------

;; Known limitations (not addressed here):
;; * Forcing a variable-bound thunk in tail position pushes a `memoize'
;;   frame, so the continuation heap grows O(n) for the `if'-function loop
;;   idiom.  This avoids Elisp stack growth but is not constant-space.
;; * `:fuel' is a per-`tl-run' budget, not a global budget across nested
;;   `tl-run' calls (e.g. thunk forcing or literal/guard evaluation).

(defun tl-run (expr env)
  "Evaluate EXPR in lexical ENV to weak head normal form."
  (let* ((termlisp--current-env (or termlisp--current-env (termlisp-make-env)))
         (control expr) (cenv env) (kont nil) (value nil) (mode 'eval)
         (done nil)
         (fuel (or (tl-env-option termlisp--current-env :fuel) 100000)))
    (while (not done)
      (when (<= fuel 0)
        (signal 'termlisp-eval-error '("fuel exhausted")))
      (setq fuel (1- fuel))
      (if (eq mode 'eval)
          (cond
           ((symbolp control)
            (let* ((cell (tl-lookup control cenv))
                   (v (cond (cell (cdr cell))
                            ((not (tl-function-p control))
                             (let ((bf (tl-resolve-value control)))
                               (if bf bf control)))
                            (t control))))
              (cond
               ((and (tl-thunk-p v) (not (tl-thunk-forced-p v)))
                (let ((tk v))
                  (when (tl-thunk-busy-p tk)
                    (signal 'termlisp-eval-error '("<<loop>> detected")))
                  (setf (tl-thunk-busy-p tk) t)
                  (push (list 'memoize tk) kont)
                  (setq cenv (tl-thunk-env tk) control (tl-thunk-expr tk))))
               ((tl-thunk-p v)
                (setq value (tl-thunk-value v) mode 'ret))
               (t (setq value v mode 'ret)))))
           ((atom control) (setq value control mode 'ret))
           ((consp control)
            (let ((head (car control)) (args (cdr control)))
              (cond
               ((and (consp head) (eq (car head) 'lambda))
                (setq cenv (tl-bind-params (cadr head) args cenv cenv))
                (setq control (caddr head)))
               ((eq head 'lambda)
                (setq value (tl-make-closure (cadr control) (caddr control) cenv)
                      mode 'ret))
               ((eq head 'do)
                (setq control (tl-desugar-do control)))
               ((eq head 'let)
                (setq control (tl-desugar-let control)))
               ((eq head 'list)
                (setq control (tl-desugar-list control)))
               ((eq head 'reduce)
                (unless (and (consp args) (null (cdr args)))
                  (signal 'termlisp-eval-error
                          '("reduce takes exactly one term")))
                (setq value (tl-reduce-term (car args) termlisp--current-env)
                      mode 'ret))
               ((symbolp head)
                (let ((cell (assq head cenv))
                      (global (assq head (tl-env-globals termlisp--current-env)))
                      (fns (gethash head (tl-env-functions termlisp--current-env))))
                  (cond
                   ((or cell global)
                    (let* ((v (cdr (or cell global)))
                           (fv (tl-resolve-callable (if (tl-thunk-p v) (tl-force v) v))))
                      (if (tl-builtin-fn-p fv)
                          ;; First-class builtin bound as a value (e.g. `foldl + 0 xs').
                          ;; Force each arg via the `builtin' continuation frame, then call.
                          (let ((fn (gethash (tl-builtin-fn-name fv) tl-builtins))
                                (arg-thunks (tl-make-arg-thunks args cenv)))
                            (if (null arg-thunks)
                                (setq value (funcall fn nil) mode 'ret)
                              (push (list 'builtin fn nil (cdr arg-thunks)) kont)
                              (let ((tk (car arg-thunks)))
                                (setq cenv (tl-thunk-env tk)
                                      control (tl-thunk-expr tk)))))
                        (let ((step (tl-apply-step fv args cenv)))
                          (setq control (car step) cenv (cdr step))))))
                   (fns
                    (let ((sel (tl-select-clause fns (tl-make-arg-thunks args cenv))))
                      (if sel
                          (progn (setq cenv (cdr sel))
                                 (setq control (tl-clause-body (car sel))))
                        (signal 'termlisp-eval-error
                                (list (format "No matching clause for %S" head))))))
                   ((tl-builtin-p head)
                    (let ((fn (gethash head tl-builtins))
                          (arg-thunks (tl-make-arg-thunks args cenv)))
                      (if (null arg-thunks)
                          (setq value (funcall fn nil) mode 'ret)
                        (push (list 'builtin fn nil (cdr arg-thunks)) kont)
                        (let ((tk (car arg-thunks)))
                          (setq cenv (tl-thunk-env tk)
                                control (tl-thunk-expr tk))))))
                   (t
                    (setq value (if args
                                    (cons head (tl-make-arg-thunks args cenv))
                                  head)
                          mode 'ret)))))
               (t
                (let ((fv (tl-run head cenv)))
                  (if (tl-builtin-fn-p fv)
                      ;; First-class builtin (e.g. `foldl + 0 xs'): force each
                      ;; argument via the `builtin' continuation frame, then call.
                      (let ((fn (gethash (tl-builtin-fn-name fv) tl-builtins))
                            (arg-thunks (tl-make-arg-thunks args cenv)))
                        (if (null arg-thunks)
                            (setq value (funcall fn nil) mode 'ret)
                          (push (list 'builtin fn nil (cdr arg-thunks)) kont)
                          (let ((tk (car arg-thunks)))
                            (setq cenv (tl-thunk-env tk)
                                  control (tl-thunk-expr tk)))))
                    (let ((step (tl-apply-step fv args cenv)))
                      (setq control (car step) cenv (cdr step))))))))))
        ;; return mode
        (if (null kont)
            (setq done t)
          (let ((frame (pop kont)))
            (pcase (car frame)
              ('memoize
               (let ((tk (cadr frame)))
                 (setf (tl-thunk-value tk) value)
                 (setf (tl-thunk-forced-p tk) t)
                 (setf (tl-thunk-busy-p tk) nil)))
              ('builtin
               (let* ((fn (nth 1 frame))
                      (collected (cons value (nth 2 frame)))
                      (remaining (nth 3 frame)))
                 (if (null remaining)
                     (setq value (funcall fn (nreverse collected)) mode 'ret)
                   (push (list 'builtin fn collected (cdr remaining)) kont)
                   (let ((tk (car remaining)))
                     (setq cenv (tl-thunk-env tk)
                           control (tl-thunk-expr tk)
                           mode 'eval)))))
              (_ (signal 'termlisp-eval-error
                         (list (format "Unknown continuation frame: %S" frame)))))))))
    value))

;;; Formatting -----------------------------------------------------------

(defun termlisp-value->string (v)
  "Render runtime value V as a string, forcing thunks."
  (let ((out nil) (stack (list v)))
    (while stack
      (let ((x (pop stack)))
        (cond
         ((stringp x) (push x out))
         (t
          (setq x (if (tl-thunk-p x) (tl-force x) x))
          (let ((foreign (tl-foreign-repr x)))
            (cond
             ;; A foreign representation renders in its own notation
             ;; (see `tl-value-printers'), before the structural walk.
             (foreign (push foreign out))
             ((consp x)
              (push "(" out)
              (push ")" stack)
              (let* ((vec (vconcat x)) (n (length vec)))
                (dotimes (k n)
                  (let ((idx (- n 1 k)))
                    (push (aref vec idx) stack)
                    (when (> idx 0) (push " " stack))))))
             ((tl-closure-p x) (push "#<closure>" out))
             ((tl-function-p x) (push "#<function>" out))
             (t (push (format "%s" x) out))))))))
    (apply #'concat (nreverse out))))

;;; Top-level forms ------------------------------------------------------

(defun tl-eval-define (env form)
  "Handle a top-level `define' FORM in ENV."
  (let ((target (cadr form)))
    (if (consp target)
        (let* ((name (car target))
               (params (mapcar (lambda (p)
                                 (tl-pattern-parse
                                  p (lambda (s) (gethash s (tl-env-constructors env)))))
                               (cdr target)))
               (clause (tl-make-clause name params (caddr form))))
          (puthash name
                   (append (gethash name (tl-env-functions env)) (list clause))
                   (tl-env-functions env))
          name)
      (let ((value (tl-run (caddr form) nil)))
        (setf (tl-env-globals env)
              (cons (cons target value) (tl-env-globals env)))
        value))))

(defconst tl-rewrite--trial-fuel 100
  "How many steps a rewrite's locality trial may take.
The subject is the rule's own pattern, which one step already
rewrites; the rest of the budget is there for a reduct that keeps
rewriting itself, and a rule that needs more than this at its own
redex would not settle inside a type either.")

(defun tl-rewrite--locality (rule lhs)
  "Return why RULE's cut at its own pattern LHS is not local, or nil.
LHS is the pattern as written -- for a clause the type layer can
read, it is a term as well -- and it is built into a graph of its own
and reduced with this one rule.  `tl-dpo-normalize' checks every cut
as it happens and leaves the first verdict that is not local in
`tl-dpo-last-gluing'; this function reads the slot back, and leaves
the verdict there for the same callers `tl-reduce-term' documents --
the slot says what the most recent DPO normalisation found, and the
trial is one.  A redex at the root has no holder outside the match,
so the first cut is always local; what the rest of the walk can find
is the rule rewriting its own reduct again under a holder it does not
own -- dangling, the only verdict there is.  A pattern that spells
one subterm at two positions does not earn one: SPO folds the shared
node, and a fold wholly inside the redex cannot be observed from
outside; only a fold whose node is held outside leaks, and that is
the dangling case already asked.  A dangling verdict is recorded and
the value reduction goes on -- a value can be re-generalized after a
cut that reaches outside the redex -- and a kind cannot, which is why
the record becomes a refusal here.  A walk that runs out of fuel is
the rule not settling at its own redex.  Return a string naming what
was found, or nil when every cut was local."
  (let ((settled nil)
        (reason nil))
    (condition-case e
        (progn
          (tl-dpo-normalize (tl-graph-root (tl-graph-build lhs))
                            (list rule)
                            tl-rewrite--trial-fuel
                            'termlisp-type-error)
          (setq settled t))
      (termlisp-type-error
       (setq reason (format "the pattern does not settle: %s" (cadr e)))))
    (cond (tl-dpo-last-gluing
           (format "the cut is not local: %s" (car tl-dpo-last-gluing)))
          ((not settled) reason)
          (t nil))))

(defun tl-rewrite-desugar (env form)
  "Return FORM as the `define' form it means, having checked the rewrite.
FORM that is not a `rewrite' comes back untouched, so every dispatcher
may apply this to the forms it handles.

A `rewrite' is `define' with its obligation paid up front.  The form
spells itself `(rewrite (NAME PATTERN...) BODY)': it extends the clause
list of an existing NAME, and the clause goes through only when the
rule it adds preserves the types of the terms it would rewrite.
`tl-preserve-check' decides that against ENV, and `preserved' is the
only verdict that lets the clause in -- `violated' names what broke,
`cannot-check' what ENV could not see, so an environment without
`:type-check' refuses as surely as one that watched the rule fail.

Two further obligations follow from the clause being readable by the
type layer at all: a clause the type layer can choose may be unfolded
inside a type, so `tl-kind-preserve-check' must find the rule
preserving the kinds of both its sides as well, and the rule is tried
at its own pattern through `tl-dpo-normalize' so that
`tl-rewrite--locality' can ask whether every cut it takes is local.
A value can be re-generalized after a cut that reaches outside the
redex, which is why `tl-reduce-term' only records that verdict; a
kind cannot, so here it refuses.

Every refusal is a `termlisp-type-error'
raised before any dispatcher has appended anything, so a refused rewrite
leaves the environment exactly as it was.

What gets through is handed to `define''s own handler as the equivalent
`define' form, so the clause reaches the type side and the evaluation
side exactly as a `define' would -- coverage announcements,
forward-name registration and signature checking included."
  (if (not (and (consp form) (eq (car form) 'rewrite)))
      form
    (let* ((target (cadr form))
           (name (and (consp target) (car target)))
           (body (caddr form)))
      (unless (and (consp target) (symbolp (car target)))
        (signal 'termlisp-type-error
                '("rewrite extends a function: (rewrite (NAME pattern...) body)")))
      (when (gethash name (tl-env-method-env env))
        (signal 'termlisp-type-error
                (list (format "rewrite of %s: a class method's clauses come from its instances"
                              name))))
      (unless (or (gethash name (tl-env-functions env))
                  (gethash name (tl-env-clauses env)))
        (signal 'termlisp-type-error
                (list (format "rewrite of %s: no such function to extend" name))))
      (let* ((params (mapcar (lambda (p)
                               (tl-pattern-parse
                                p (lambda (s) (gethash s (tl-env-constructors env)))))
                             (cdr target)))
             ;; The rule a single clause is: NAME applied to the pattern,
             ;; rewriting to the body.  `tl-nbe--make-rule' returns nil
             ;; for a clause the type layer could never choose -- guard,
             ;; or, and, dot, rest -- and such a clause has no
             ;; preservation question to ask, which is the same as no
             ;; answer.
             (rule (tl-nbe--make-rule
                    name (list (tl-make-clause name params body)))))
        (unless rule
          (signal 'termlisp-type-error
                  (list (format "rewrite of %s: the pattern is not one the type layer can read"
                                name))))
        (let ((verdict (tl-preserve-check env rule)))
          (unless (eq (car verdict) 'preserved)
            (signal 'termlisp-type-error
                    (list (format "rewrite of %s refused: %s"
                                  name (cdr verdict))))))
        (let ((kverdict (tl-kind-preserve-check env rule)))
          (unless (eq (car kverdict) 'preserved)
            (signal 'termlisp-type-error
                    (list (format "rewrite of %s refused: %s"
                                  name (cdr kverdict))))))
        (let ((escape (tl-rewrite--locality rule target)))
          (when escape
            (signal 'termlisp-type-error
                    (list (format "rewrite of %s refused: %s"
                                  name escape)))))
        (cons 'define (cdr form))))))

(defun tl-eval-datatype (env form)
  "Handle `(datatype [open] HEAD (CON ARGTYPE...) ...)' in ENV.
HEAD is either the datatype's name or `(NAME PARAM...)', which declares
the type parameters explicitly instead of inferring them from the
constructors.  A constructor may end in `: RESULT' to declare its own
result type, see `tl-split-ctor'; that is what makes an indexed (GADT)
datatype possible.
Datatype declarations are type-checked even when `:type-check' is nil:
constructor argument types are parsed and their schemes registered."
  (let* ((rest (cdr form))
         (open (eq (car rest) 'open))
         (rest (if open (cdr rest) rest))
         (head (car rest))
         ;; `(datatype (Vec a n) ...)' declares its parameter list
         ;; explicitly, which fixes both their order and their scope;
         ;; `(datatype Vec ...)' still infers them from the constructors.
         ;; Only the spelling differs, and declaring them lets an index
         ;; variable be mentioned before any constructor that uses it.
         (declared-p (consp head))
         (name (if declared-p (car head) head))
         ;; A declared parameter may carry its kind: `(a : *)' or
         ;; `(x : (univ a))'.  The names still go where they always
         ;; went, and the annotations ride along beside them, because
         ;; only a kind can say that one parameter's values come out of
         ;; another's -- which is the whole content of `Eq a x y'.  A
         ;; bare symbol keeps meaning what it always meant: a parameter
         ;; whose kind nothing has pinned, left for each use to decide.
         (declared (and declared-p (cdr head)))
         (pnames (and declared
                      (mapcar (lambda (p) (if (consp p) (car p) p)) declared)))
         (pkind-sexps
          (and declared
               (let ((acc nil))
                 (dolist (p declared)
                   (cond
                    ((and (consp p) (eq (cadr p) ':) (= (length p) 3))
                     (push (cons (car p) (caddr p)) acc))
                    ((consp p)
                     (signal 'termlisp-error
                             (list (format "Malformed parameter %S in datatype %S; write it as (NAME : KIND)"
                                           p name))))))
                 (nreverse acc))))
         (ctors (cdr rest))
         (old (gethash name (tl-env-datatypes env))))
    (when old
      (dolist (c (plist-get old :constructors))
        (remhash c (tl-env-constructors env))
        (remhash c (tl-env-type-env env))))
    ;; `cl-defun' distinguishes an omitted optional argument from one
    ;; supplied as nil, and only the latter means "these are declared
    ;; parameters", so the argument must genuinely be left off for the
    ;; inferred spelling.
    (let ((syms (if declared-p
                    (tl-register-datatype-types env name ctors pnames pkind-sexps)
                  (tl-register-datatype-types env name ctors))))
      (puthash name (list :open open :constructors (mapcar #'car ctors) :params syms)
               (tl-env-datatypes env)))
    (dolist (ctor ctors)
      (puthash (car ctor) name (tl-env-constructors env)))
    name))

(defun tl-eval-datatype-extension (env form)
  "Handle `(datatype-extension NAME (CON ARGTYPE...) ...)' in ENV."
  (let* ((name (cadr form))
         (ctors (cddr form))
         (existing (gethash name (tl-env-datatypes env))))
    (unless (and existing (plist-get existing :open))
      (signal 'termlisp-eval-error
              (list (format "Cannot extend non-open datatype %S" name))))
    (tl-register-datatype-types env name ctors (plist-get existing :params))
    (puthash name
             (plist-put existing :constructors
                        (append (plist-get existing :constructors)
                                (mapcar #'car ctors)))
             (tl-env-datatypes env))
    (dolist (ctor ctors)
      (puthash (car ctor) name (tl-env-constructors env)))
    name))

(defun tl-eval-top (env form)
  "Evaluate one top-level FORM in ENV."
  (cond
   ((and (consp form) (eq (car form) 'rewrite))
    (tl-eval-define env (tl-rewrite-desugar env form)))
   ((and (consp form) (eq (car form) 'define)) (tl-eval-define env form))
   ((and (consp form) (eq (car form) 'datatype)) (tl-eval-datatype env form))
   ((and (consp form) (eq (car form) 'datatype-extension))
    (tl-eval-datatype-extension env form))
   ((and (consp form) (eq (car form) ':)) nil)
   ((and (consp form) (eq (car form) 'do)) (tl-run (tl-desugar-do form) nil))
   (t (tl-run form nil))))

(defun termlisp-eval-form (form &optional env)
  "Evaluate a single already-read term-lisp FORM in ENV.
Handles top-level `do' desugaring like `termlisp-eval', and honors the
`:type-check' and `:elaborate' options of ENV."
  (let* ((env (or env (termlisp-make-env)))
         (termlisp--current-env env)
         ;; Type-level reduction runs against this env, so that a
         ;; signature's `plus n m' can unfold while its type is being
         ;; compared with another.  Left unbound, unification is purely
         ;; structural -- which is exactly what ordinary Hindley-Milner
         ;; checking, with nothing to unfold, wants.
         (tl-nbe-reduce-env env)
         (tl-infer-holes nil)
         (form (if (and (consp form) (eq (car form) 'do))
                   (tl-desugar-do form)
                 form)))
    (if (tl-env-option env :elaborate)
        (setq form (tl-elaborate-form env form))
      (when (and (tl-env-option env :type-check)
                 (not (and (consp form)
                           (memq (car form) '(datatype datatype-extension)))))
        (tl-typecheck-form env form)))
    ;; A form left with holes is not something to run: the program
    ;; declined to say what belongs in those positions, so there is no
    ;; value to produce.  Evaluating it anyway would only answer `got _'
    ;; about a variable that was never meant to have one.  Report the
    ;; goals instead -- which is what the REPL is for -- and let a
    ;; batch caller see the same thing as a condition.
    (when tl-infer-holes
      (signal 'termlisp-hole (list (tl-goal-lines tl-infer-holes))))
    (tl-eval-top env form)))

(defun termlisp--eval-forms (forms env)
  "Evaluate FORMS in ENV as one batch and return the last value.
A name declared by a later form in FORMS is knowable while an earlier
one is checked, and forward references are linked once the whole batch
has run.  ENV defaults to a fresh environment."
  (let* ((env (or env (termlisp-make-env)))
         ;; One input is one unit: a name declared by a later form is
         ;; knowable here even though it is not yet in ENV.
         (tl-infer-forward-names (termlisp-collect-forward-names forms))
         (tl-infer-forward-vars (or tl-infer-forward-vars
                                    (make-hash-table :test #'eq)))
         (tl-infer-forward-order nil)
         (tl-infer-forward-regen (or tl-infer-forward-regen
                                     (make-hash-table :test #'eq)))
         (result nil))
    (prog1 (dolist (form forms result)
             (setq result (termlisp-eval-form form env)))
      ;; The whole batch is one unit, so every definition it declares
      ;; is now in ENV and the references made to a forward name before
      ;; its definition arrived can be told what it really was.
      (tl-forward--link))))

(defun termlisp-eval (string &optional env)
  "Parse and evaluate STRING in ENV (creating a fresh env if nil).

A top-level `do' is desugared before inference/elaboration so that a
type-directed `(do ...)' exposes its `bind'/`return' class-method calls to
the elaborator.  A `do' nested inside a larger expression is instead
desugared at evaluation time by `tl-run' and is therefore not elaborated:
nested type-directed `do' (without an explicit monad operand) remains a
known limitation."
  (termlisp--eval-forms (termlisp-parse string) env))

(defun termlisp-eval-submission (string &optional env)
  "Evaluate STRING in ENV as one submission and return its printed value.
ENV defaults to a fresh environment.  This is the driver every
front-end shares: STRING is parsed as one unit (so a name a later form
declares is knowable while an earlier one is checked), every form runs
through `termlisp-eval-form', forward references are linked, the
post-batch coverage check runs once the submission succeeded -- the
first moment every clause of a function typed across it is present --
and a queue left behind by a submission that failed partway is dropped
rather than reported at the next one.  Return nil when STRING holds no
top-level forms.  A form the checker leaves with holes signals
`termlisp-hole' with its goals from inside the batch."
  (let ((forms (termlisp-parse string)))
    (unwind-protect
        (when forms
          (prog1 (termlisp-value->string
                  (termlisp--eval-forms forms env))
            (tl-run-post-batch)))
      ;; A submission that failed partway left a function holding only
      ;; some of its clauses.  Reporting it now would name a clause the
      ;; user has not typed yet, so the queue is dropped instead -- the
      ;; same half-written state `tl-run-post-batch' refuses to report.
      (setq tl-coverage-announcements nil))))

(defun termlisp--ensure-magic-string (file)
  "Ensure FILE begins with `termlisp--magic-string', inserting it if absent.
Writes the file back only when the magic string is missing."
  (when (and (file-readable-p file) (file-writable-p file))
    (with-temp-buffer
      (insert-file-contents file)
      (goto-char (point-min))
      (unless (looking-at-p (regexp-quote termlisp--magic-string))
        (goto-char (point-min))
        (insert termlisp--magic-string "\n")
        (write-region (point-min) (point-max) file nil 'silent)))))

(defun termlisp-eval-file (file &optional env)
  "Evaluate the contents of FILE in ENV."
  (termlisp--ensure-magic-string file)
  (termlisp-eval (with-temp-buffer
                   (insert-file-contents file)
                   (buffer-string))
                 env))

(defun termlisp-load (file &optional env)
  "Load a `.tls' FILE into ENV (or a fresh env), ensuring its magic string.
Returns ENV."
  (termlisp--ensure-magic-string file)
  (let* ((termlisp--load-env (or env (termlisp-make-env)))
         ;; The whole file is one unit, so a `define' may mention a name
         ;; a later `define' declares.
         (tl-infer-forward-names (termlisp-collect-file-forward-names file))
         (tl-infer-forward-vars (or tl-infer-forward-vars
                                    (make-hash-table :test #'eq)))
         (tl-infer-forward-order nil)
         (tl-infer-forward-regen (or tl-infer-forward-regen
                                     (make-hash-table :test #'eq))))
    (load (expand-file-name file) nil t)
    ;; The file is one batch, so a use made of a forward name before
    ;; its definition was read can now be told what it really was.
    (tl-forward--link)
    ;; A file is one batch, so this is the first moment every definition
    ;; in it has all of its clauses and a coverage check can mean
    ;; anything.
    (tl-run-post-batch)
    termlisp--load-env))

(defconst termlisp--directory
  (file-name-directory (or load-file-name buffer-file-name))
  "Directory containing the termlisp sources.")

(defun termlisp-load-prelude (&optional env)
  "Load the bundled prelude into ENV (or a fresh env) and return it.
Loading goes through `load', so `termlisp-load' must be required for the
`datatype'/`define'/`class'/`instance' macros to be defined."
  (let ((termlisp--load-env (or env (termlisp-make-env)))
        (file (expand-file-name "termlisp-prelude.tls" termlisp--directory))
        ;; The prelude is a fixed library whose partial functions are
        ;; deliberate -- `head' and `tail' match only `Cons', and `if' is
        ;; written clause by clause -- so announcing into a throwaway
        ;; queue drops them instead of reporting them.  Nothing here
        ;; flushes, so the queue goes with this binding.
        (tl-coverage-announcements nil))
    (termlisp--ensure-magic-string file)
    (let ((tl-infer-forward-names
           (termlisp-collect-file-forward-names file))
          (tl-infer-forward-vars (or tl-infer-forward-vars
                                     (make-hash-table :test #'eq)))
          (tl-infer-forward-order nil)
          (tl-infer-forward-regen (or tl-infer-forward-regen
                                      (make-hash-table :test #'eq))))
      (load file nil t)
      ;; The file is one batch: a use made of a forward name before its
      ;; definition was read can now be told what it really was.  The
      ;; prelude has such uses -- the State functions -- and the schemes
      ;; they came out with depend on this.
      (tl-forward--link))
    termlisp--load-env))

(provide 'termlisp-eval)
;;; termlisp-eval.el ends here
