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

(defun tl-bind-param-thunks (params thunks base-env)
  "Extend BASE-ENV binding PARAMS to THUNKS in order."
  (let ((new base-env) (params params) (thunks thunks))
    (while params
      (push (cons (car params) (car thunks)) new)
      (setq params (cdr params) thunks (cdr thunks)))
    new))

(defun tl-bind-params (params args base-env caller-env)
  "Extend BASE-ENV binding PARAMS to thunks of ARGS evaluated in CALLER-ENV."
  (tl-bind-param-thunks params (tl-make-arg-thunks args caller-env) base-env))

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

(defun tl-clause-arity (clause)
  "Return the number of arguments CLAUSE binds.
That is its parameter count less any `rest' parameter, which
absorbs whatever else the call supplies."
  (cl-count-if-not (lambda (p) (eq (car p) 'rest)) (tl-clause-params clause)))

(defun tl-clauses-min-arity (clauses)
  "Return the smallest arity among CLAUSES."
  (cl-loop for c in clauses minimize (tl-clause-arity c)))

(defun tl-clauses-max-arity (clauses)
  "Return the largest arity among CLAUSES."
  (cl-loop for c in clauses maximize (tl-clause-arity c)))

(defun tl-apply-clauses (clauses arg-thunks label)
  "Return (BODY ENV SURPLUS) for the first CLAUSES member matching ARG-THUNKS.
Fewer arguments than every clause binds yields the pending
application itself, a `tl-partial' over the clause list; more
arguments than any clause binds runs the clause that takes the
leading ones and leaves the rest in SURPLUS, for the caller to
apply to what the body produces.  LABEL names the callee in the
error when no clause matches."
  (let ((n (length arg-thunks))
        (sel (tl-select-clause clauses arg-thunks)))
    (cond
     (sel (list (tl-clause-body (car sel)) (cdr sel) nil))
     ((< n (tl-clauses-min-arity clauses))
      (tl-make-partial (tl-make-function clauses) arg-thunks))
     ((> n (tl-clauses-max-arity clauses))
      (let ((lead (tl-select-clause
                   clauses
                   (cl-subseq arg-thunks 0 (tl-clauses-max-arity clauses)))))
        (if lead
            (list (tl-clause-body (car lead)) (cdr lead)
                  (nthcdr (tl-clause-arity (car lead)) arg-thunks))
          (signal 'termlisp-eval-error
                  (list (format "No matching clause for %s" label))))))
     (t (signal 'termlisp-eval-error
                (list (format "No matching clause for %s" label)))))))

(defun tl-apply-thunks (fv arg-thunks label)
  "Return (BODY ENV SURPLUS) to continue applying FV to ARG-THUNKS, or signal.
A callee that binds more arguments than arrived yields the
`tl-partial' value itself, which remembers this call and continues
it on the next application; SURPLUS holds the argument thunks FV
did not consume, for the caller to apply to what the body
produces.  LABEL names the callee in the no-clause error."
  (cond
   ((tl-partial-p fv)
    (tl-apply-thunks (tl-partial-fv fv)
                     (append (tl-partial-args fv) arg-thunks)
                     label))
   ((tl-closure-p fv)
    (let ((params (tl-closure-params fv)))
      (if (< (length arg-thunks) (length params))
          (tl-make-partial fv arg-thunks)
        (list (tl-closure-body fv)
              (tl-bind-param-thunks params arg-thunks (tl-closure-env fv))
              (nthcdr (length params) arg-thunks)))))
   ((tl-function-p fv)
    (tl-apply-clauses (tl-function-clauses fv) arg-thunks label))
   ((and (symbolp fv)
         (gethash fv (tl-env-functions termlisp--current-env)))
    (tl-apply-thunks
     (tl-make-function (gethash fv (tl-env-functions termlisp--current-env)))
     arg-thunks label))
   (t (signal 'termlisp-eval-error
              (list (format "Not a function: %S" fv))))))

(defun tl-apply-step (fv args caller-env label)
  "Return (BODY ENV SURPLUS) to continue applying FV to ARGS, or signal.
CALLER-ENV is where ARGS are evaluated when their parameter is
bound; see `tl-apply-thunks' for the pending application a partial
one yields and the SURPLUS a caller must apply to the body's
result.  LABEL names the callee in errors."
  (tl-apply-thunks fv (tl-make-arg-thunks args caller-env) label))

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
                (let ((step (tl-apply-step
                             (tl-make-closure (cadr head) (caddr head) cenv)
                             args cenv "lambda")))
                  (if (tl-partial-p step)
                      (setq value step mode 'ret)
                    (when (caddr step)
                      (push (list 'apply (caddr step)) kont))
                    (setq control (car step) cenv (cadr step)))))
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
                        (let ((step (tl-apply-step fv args cenv "value")))
                          (if (tl-partial-p step)
                              (setq value step mode 'ret)
                            (when (caddr step)
                              (push (list 'apply (caddr step)) kont))
                            (setq control (car step) cenv (cadr step)))))))
                   (fns
                    (let ((step (tl-apply-clauses fns
                                                  (tl-make-arg-thunks args cenv)
                                                  (format "%S" head))))
                      (if (tl-partial-p step)
                          (setq value step mode 'ret)
                        (when (caddr step)
                          (push (list 'apply (caddr step)) kont))
                        (setq cenv (cadr step) control (car step)))))
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
                    (let ((step (tl-apply-step fv args cenv "value")))
                      (if (tl-partial-p step)
                          (setq value step mode 'ret)
                        (when (caddr step)
                          (push (list 'apply (caddr step)) kont))
                        (setq control (car step) cenv (cadr step)))))))))))
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
              ('apply
               ;; A surplus of arguments: apply what the body produced to
               ;; the thunks the callee did not consume.
               (let* ((extra (nth 1 frame))
                      (fv (tl-resolve-callable
                           (if (tl-thunk-p value) (tl-force value) value))))
                 (if (tl-builtin-fn-p fv)
                     (let ((fn (gethash (tl-builtin-fn-name fv) tl-builtins)))
                       (push (list 'builtin fn nil (cdr extra)) kont)
                       (let ((tk (car extra)))
                         (setq cenv (tl-thunk-env tk)
                               control (tl-thunk-expr tk)
                               mode 'eval)))
                   (let ((step (tl-apply-thunks fv extra "surplus")))
                     (if (tl-partial-p step)
                         (setq value step mode 'ret)
                       (when (caddr step)
                         (push (list 'apply (caddr step)) kont))
                       (setq control (car step) cenv (cadr step) mode 'eval))))))
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
             ((tl-partial-p x) (push "#<partial>" out))
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
Returns ENV.  The load is a transaction (`termlisp--load-invoke'):
success journals FILE so `remove' can undo it, and a failure restores
the environment and installs nothing."
  (termlisp--ensure-magic-string file)
  (let ((env (or env (termlisp-make-env))))
    (termlisp--load-invoke
     env file
     (lambda ()
       (let ((termlisp--load-env env)
             ;; The whole file is one unit, so a `define' may mention a
             ;; name a later `define' declares.
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
         ;; A file is one batch, so this is the first moment every
         ;; definition in it has all of its clauses and a coverage
         ;; check can mean anything.
         (tl-run-post-batch))))
    env))

(defconst termlisp--directory
  (file-name-directory (or load-file-name buffer-file-name))
  "Directory containing the termlisp sources.")

(defun termlisp-load-prelude (&optional env)
  "Load the bundled prelude into ENV (or a fresh env) and return it.
Loading goes through `load', so `termlisp-load' must be required for the
`datatype'/`define'/`class'/`instance' macros to be defined.  The load
is a transaction (`termlisp--load-invoke'): success journals the
prelude like any other library, so `remove' can undo it too, and a
failure installs nothing."
  (let ((env (or env (termlisp-make-env)))
        (file (expand-file-name "termlisp-prelude.tls" termlisp--directory)))
    (termlisp--ensure-magic-string file)
    (termlisp--load-invoke
     env file
     (lambda ()
       ;; The prelude is a fixed library whose partial functions are
       ;; deliberate -- `head' and `tail' match only `Cons', and `if' is
       ;; written clause by clause -- so announcing into the throwaway
       ;; queue `termlisp--load-invoke' binds drops them instead of
       ;; reporting them.  Nothing here flushes.
       (let ((termlisp--load-env env)
             (tl-infer-forward-names (termlisp-collect-file-forward-names file))
             (tl-infer-forward-vars (or tl-infer-forward-vars
                                        (make-hash-table :test #'eq)))
             (tl-infer-forward-order nil)
             (tl-infer-forward-regen (or tl-infer-forward-regen
                                         (make-hash-table :test #'eq))))
         (load file nil t)
         ;; The file is one batch: a use made of a forward name before
         ;; its definition was read can now be told what it really was.
         ;; The prelude has such uses -- the State functions -- and the
         ;; schemes they came out with depend on this.
         (tl-forward--link))))
    env))

;;; load and remove ------------------------------------------------------
;; A termlisp program reaches its libraries through the `load' builtin:
;; it reads a `.tls' file and evaluates the file's forms into the
;; environment the call is running in, so the definitions the file makes
;; are visible to whatever runs next -- a later form of the same
;; submission, the rest of the calling function, or the REPL.  Two
;; properties of the evaluator make that work without new plumbing: a
;; call head resolves through `tl-env-functions'/`tl-env-globals' of
;; `termlisp--current-env' at the moment the call is applied, and
;; `tl-run' keeps that variable dynamically bound for as long as it
;; runs, thunk forcing included.  The primitives therefore live here and
;; not in `termlisp-builtins', which sits below the reader: loading
;; needs `termlisp-parse-file' and the batch machinery above it.
;;
;; Every load is a transaction over the environment's tables.  A load
;; that finishes journals a `tl-load-record' -- the file and the
;; snapshot `termlisp--env-snapshot' took before it ran -- so `remove'
;; can put the environment back; a load that fails partway restores
;; that snapshot itself and installs nothing, which is the same
;; machinery one step earlier.  The journal is a tree rather than a
;; list: a file loaded while another load is running is recorded under
;; that load, because its definitions go back with the outer load's
;; snapshot and a record left lying around would restore a state no
;; load owns any more.  `remove' takes the most recently completed
;; matching top-level load, so loading twice and removing once
;; returns to the first load's state, and a file loaded inside
;; another load comes out with that load rather than on its own.
;;
;; The file is read with the termlisp reader rather than through the
;; elisp `load' macros `termlisp-load' defines, so a `.tls' file is one
;; artifact whichever side loads it and a host that never required that
;; file can still load libraries.

(defvar termlisp--load-parent nil
  "Load record whose transaction is open, or nil at top level.
A load started while another is running journals itself under the
running one instead of at the head of `tl-env-loads'.  The record
tree is what `remove' walks, and it is what makes removing an outer
load drop the records of everything that load pulled in.")

(cl-defstruct (tl-load-record (:constructor tl-make-load-record (file)))
  "One completed load: FILE, the snapshot to restore, nested loads.
SNAPSHOT is what `termlisp--env-snapshot' took before FILE's forms
ran, and restoring it is the whole of `remove'.  CHILDREN are the
loads FILE itself performed, most recent first; they live here and
not in `tl-env-loads' because they only exist as part of FILE's
load -- removing FILE removes them with it, which is what stops a
stale child record from restoring a state the parent already undid.
`remove' refuses a nested record by name; the tree exists for the
parent's sake.  FILE is the expanded file name, recorded the way
`remove' expands its own argument."
  file snapshot children)

(defconst termlisp--snapshot-tables
  '((tl-env-functions . identity)
    (tl-env-datatypes . copy-sequence)
    (tl-env-constructors . identity)
    (tl-env-type-env . identity)
    (tl-env-sig-env . identity)
    (tl-env-kind-env . identity)
    (tl-env-class-env . identity)
    (tl-env-instance-env . identity)
    (tl-env-method-env . identity)
    (tl-env-clauses . identity))
  "The env tables a load can write, paired with the copier for their values.
`copy-sequence' earns its place in one row: `tl-eval-datatype-extension'
extends a datatype with `plist-put', which overwrites the value cell
of the stored plist in place, so a snapshot sharing that plist would
grow its constructors back on restore.  Every other table is written
only by replacing its value with a fresh one -- clause lists and
instance lists by `append', schemes and classes by `puthash' -- so
sharing those values is sound.")

(defun termlisp--env-snapshot (env)
  "Copy every part of ENV a load can change, for `termlisp--env-restore'.
The result is (TABLES . GLOBALS), where TABLES is an alist of
\(ACCESSOR . COPY) and GLOBALS a fresh copy of `tl-env-globals'.
`options' and `current' are not copied: no load form can reach
either, and `current' has no writer at all."
  (cons (mapcar (lambda (cell)
                  (let ((copy (make-hash-table :test #'eq)))
                    (maphash (lambda (k v)
                               (puthash k (funcall (cdr cell) v) copy))
                             (funcall (car cell) env))
                    (cons (car cell) copy)))
                termlisp--snapshot-tables)
        (copy-sequence (tl-env-globals env))))

(defun termlisp--env-restore (env snapshot)
  "Restore the tables of ENV from SNAPSHOT.
The live hash tables are cleared and refilled in place rather than
replaced, so anything already holding one keeps seeing the truth."
  (dolist (cell (car snapshot))
    (let ((live (funcall (car cell) env))
          (copy (cdr cell)))
      (clrhash live)
      (maphash (lambda (k v) (puthash k v live)) copy)))
  (setf (tl-env-globals env) (copy-sequence (cdr snapshot))))

(defun termlisp--load-invoke (env file run-forms)
  "Run FILE's load into ENV by evaluating RUN-FORMS, transactionally.
The environment is snapshotted before RUN-FORMS runs.  A run that
finishes journals its record -- at the head of `tl-env-loads' for a
top-level load, under `termlisp--load-parent' for a load FILE itself
started -- and a run that signals restores the snapshot and journals
nothing, so a failed load leaves the environment exactly as it was.
RUN-FORMS is called for effect; whatever it returns is ignored, and
it is responsible for its own forward-name machinery and for
flushing coverage (`tl-run-post-batch') if the load's file is to be
checked.  FILE is expanded against `default-directory' and recorded
expanded, which is also the rule `remove' expands its argument by."
  (let ((snapshot (termlisp--env-snapshot env))
        (record (tl-make-load-record (expand-file-name file)))
        (outer-parent termlisp--load-parent)
        (outer-queue tl-coverage-announcements)
        (loaded nil))
    (unwind-protect
        (let ((tl-coverage-announcements nil)
              (termlisp--load-parent record))
          (funcall run-forms)
          (setf (tl-load-record-snapshot record) snapshot)
          (if outer-parent
              (push record (tl-load-record-children outer-parent))
            (push record (tl-env-loads env)))
          (setq loaded t))
      (setq tl-coverage-announcements outer-queue)
      (unless loaded (termlisp--env-restore env snapshot)))))

(defun termlisp--load-match-p (record file)
  "Say whether RECORD is the load of FILE, an already-expanded name.
Recorded names are compared as strings first; a file reached through
a different spelling -- a symlink, another relative path -- still
matches when both files exist and `file-equal-p' says they are the
same one.  `file-equal-p' needs both files present and signals about
one that is gone, which is why the existence guards come first:
removing a library whose file has since been deleted must work."
  (or (string-equal (tl-load-record-file record) file)
      (and (file-exists-p (tl-load-record-file record))
           (file-exists-p file)
           (file-equal-p (tl-load-record-file record) file))))

(defun termlisp--find-load (records file top)
  "Find the most recent load of FILE among RECORDS or below one of them.
TOP is the top-level record a search has descended under, nil while it
is still at the top.  Return the record and its top-level ancestor as
\(RECORD . TOP), or nil.  A record is examined before its children
because a nested load finishes before the load that started it, so
parent-after-children is completion order and the first match is the
most recent one."
  (catch 'termlisp--found
    (dolist (record records)
      (when (termlisp--load-match-p record file)
        (throw 'termlisp--found (cons record top)))
      (let ((found (termlisp--find-load
                    (tl-load-record-children record)
                    file
                    (or top record))))
        (when found (throw 'termlisp--found found))))
    nil))

(defun termlisp--remove-load (file env)
  "Undo the most recent top-level load of FILE into ENV, answering `Unit'.
The snapshot taken before that load ran goes back over ENV's tables,
so every name the load declared becomes unknown again, every name it
extended returns to the clauses it had before, and the type layer's
tables return with the rest -- a later submission checks against the
same environment the value tables show.  The record is dropped with
the records of every load FILE itself performed: their definitions
went back with the snapshot, and a record left behind would restore
that state a second time from a load that no longer exists.
A file loaded as part of another load is refused rather than undone
on its own: its snapshot is a moment inside the enclosing
transaction, and restoring that moment would take the enclosing
load's later work with it, which is not what naming this file means.
What a remove cannot reach is a value already in hand -- a function
value carries its clauses, not its name -- so what a name resolves to
afterwards is decided here and not retroactively.
FILE expands against `default-directory' exactly as it did for
`load', and a file that is not loaded is an error rather than a
silently accepted no-op."
  (let* ((want (expand-file-name file))
         (found (termlisp--find-load (tl-env-loads env) want nil)))
    (unless found
      (signal 'termlisp-eval-error
              (list (format "remove: %s is not loaded" file))))
    (when (cdr found)
      (signal 'termlisp-eval-error
              (list (format "remove: %s was loaded inside %s; remove that file to undo them both"
                            file
                            (tl-load-record-file (cdr found))))))
    (let ((record (car found)))
      (setf (tl-env-loads env)
            (delq record (tl-env-loads env)))
      (termlisp--env-restore env (tl-load-record-snapshot record)))
    'Unit))

(defun termlisp--load-tls-file (file env)
  "Load the `.tls' FILE into ENV as one batch, answering `Unit'.
FILE's forms run through `termlisp-eval-form', so ENV's `:type-check'
and `:elaborate' options decide how each is checked and every name the
file declares lands in ENV's own tables -- which is where the evaluator
looks names up, so a later form sees them whether it belongs to the
loading submission or arrives afterwards.  The file is one batch: its
declarations are knowable forward inside it, by the same forward-name
machinery a submission gets, and its coverage is flushed once, so
loading in the middle of a submission cannot report that submission's
half-written functions -- the enclosing batch's queue is set aside and
restored by `termlisp--load-invoke', which also makes the load a
transaction: success journals FILE for `remove', failure restores the
environment and installs nothing.  A parse error is re-signalling
naming FILE, an unreadable file is refused before any form is
evaluated, and the file itself is only read, never rewritten -- the
`.tls' magic string is an editor convention the reader skips as a
comment."
  (unless (file-readable-p file)
    (signal 'termlisp-eval-error
            (list (format "load: cannot read %s" file))))
  (let ((forms
         (condition-case e
             (termlisp-parse-file file)
           (termlisp-parse-error
            (signal 'termlisp-parse-error
                    (list (format "%s: %s" file (cadr e))))))))
    (termlisp--load-invoke
     env file
     (lambda ()
       (let ((tl-infer-forward-names (termlisp-collect-forward-names forms))
             (tl-infer-forward-vars (or tl-infer-forward-vars
                                        (make-hash-table :test #'eq)))
             (tl-infer-forward-order nil)
             (tl-infer-forward-regen (or tl-infer-forward-regen
                                         (make-hash-table :test #'eq))))
         (dolist (form forms)
           (termlisp-eval-form form env))
         ;; The file is one batch, so this is the first moment every
         ;; definition in it has all of its clauses.
         (tl-forward--link)
         (tl-run-post-batch)))))
  'Unit)

(tl-register-builtin 'load
  (lambda (args)
    (unless (= (length args) 1)
      (signal 'termlisp-type-error
              (list (format "load expects 1 argument, got %d"
                            (length args)))))
    (let ((file (car args)))
      (unless (stringp file)
        (signal 'termlisp-type-error
                (list (format "load expects a String, got %S" file))))
      ;; A relative name expands against the host's `default-directory',
      ;; the same rule `load' itself follows for its own files.
      (termlisp--load-tls-file (expand-file-name file)
                               termlisp--current-env))))

(tl-register-builtin 'remove
  (lambda (args)
    (unless (= (length args) 1)
      (signal 'termlisp-type-error
              (list (format "remove expects 1 argument, got %d"
                            (length args)))))
    (let ((file (car args)))
      (unless (stringp file)
        (signal 'termlisp-type-error
                (list (format "remove expects a String, got %S" file))))
      (termlisp--remove-load file termlisp--current-env))))

(provide 'termlisp-eval)
;;; termlisp-eval.el ends here
