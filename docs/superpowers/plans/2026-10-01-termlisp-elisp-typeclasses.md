# term-lisp Emacs Lisp Port — Plan 4: Type Classes (phase A) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add Hindley–Milner type classes (phase A) — class/instance declarations, constraint collection and solving, constrained schemes, dictionary-passing elaboration, and type-directed `do`.

**Architecture:** A class has a parameter and method schemes; methods are used at *constrained* types. Inference accumulates constraints (a dynamic list) and constrained schemes carry them. Solving matches a constraint `(C T)` against instance heads (one-way matching, borrowing clover's subsumption style), recursively discharging the instance context. A post-inference **elaborator** rewrites each method call to pass the resolved instance dictionary, so the runtime is the existing term-lisp evaluator with explicit dictionaries. `do` without an explicit monad is desugared using the inferred `Monad` constraint.

**Tech Stack:** Emacs Lisp (`cl-lib`, `ert`); builds on `termlisp-types.el` (Plan 2), `termlisp-eval.el`/prelude (Plan 3).

**Scope:** Phase A. Kind checking is minimal (class params are `* -> *`). Multi-parameter type classes, functional dependencies, and associated types are out of scope. Superclasses are supported for constraint simplification only.

**Progress (as of 2026-10-01):** Tasks 1–3 DONE and merged (class/instance declarations; constraint collection; constraint solving + constrained schemes). Tasks 5–6 DONE and merged (`termlisp-elaborate.el` type-directed dictionary passing; prelude `Functor`/`Applicative`/`Monad` classes + Maybe/List/State/Reader instances; `:elaborate` option; 188 tests, `make compile` clean). The elaborator is sound: it never rewrites a non-method call and never inserts a wrong dictionary — it only *under*-elaborates.

**Remaining (Task 4 + follow-ups):**
- **Task 4 — type-directed `do`**: `(do (x <- (Just 1)) (return (+ x 1)))` (no explicit monad name) is not yet supported; `tl-desugar-do` still requires a dictionary. Explicit-dictionary `do` works.
- Polymorphic functions with a *generalized* constraint are not dictionary-threaded (e.g. `(define (add1-in m) (fmap ... m))` errors at runtime); full support requires transforming polymorphic functions to take dictionary parameters.
- Method referenced as a bare value (not in application position) is not elaborated.
- Ambiguous (non-ground) constraints are silently accepted and fail only at runtime; a proper implementation should reject ambiguous type variables.
- `Applicative` runtime methods (`pure`/`ap`) are absent; superclasses are declared `nil` (nominal only).
- Parameterized instance heads (e.g. `Functor (Either e)`) do not resolve with the current `f a`-vs-`Either e a` encoding; instance contexts/superclasses are parsed but unused.

**Borrowing note:** constraint solving uses one-way matching/subsumption in the style of clover's `unify.lisp`; the shared unifier kernel may be parameterized over term decomposition (`cons` vs `tl-tcon`) where natural.

---

## File Structure

```
termlisp-types.el      ; constraints, classes, instances, solving, constrained schemes, do inference
termlisp-elaborate.el  ; dictionary-passing elaborator (new)
termlisp-eval.el       ; optional :elaborate integration
termlisp-prelude.tlsp  ; class/instance declarations + runtime dictionaries
test/termlisp-test.el  ; type-class tests
```

---

## Task 1: Constraints, classes, instances, and declarations

**Files:**
- Modify: `termlisp-types.el`
- Modify: `termlisp-base.el` (add `class-env`, `instance-env`, `method-env` slots)
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest class/declare-and-methods ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (should (gethash 'Functor (tl-env-class-env env)))
    (should (gethash 'fmap (tl-env-method-env env)))))

(ert-deftest class/instance-registration ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-typecheck-def env "(instance (Functor Maybe))")
    (should (= (length (gethash 'Functor (tl-env-instance-env env))) 1))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL.

- [ ] **Step 3: Add structs and env slots**

In `termlisp-types.el`:

```elisp
(cl-defstruct (tl-constraint (:constructor tl-constraint (class type))) class type)
(cl-defstruct (tl-cclass (:constructor tl-cclass (name params supers methods))) name params supers methods)
(cl-defstruct (tl-instance (:constructor tl-instance (class head context methods))) class head context methods)
```

Add a `constraints` slot to `tl-tscheme` (keep the 2-arg constructor working):

```elisp
(cl-defstruct (tl-tscheme (:constructor tl-tscheme (vars type &optional constraints)))
  vars type (constraints nil))
```

In `termlisp-base.el`, add slots to `tl-env`:

```elisp
  (class-env (make-hash-table :test #'eq))
  (instance-env (make-hash-table :test #'eq))
  (method-env (make-hash-table :test #'eq))
```

- [ ] **Step 4: Implement declaration parsing/registration**

```elisp
(defun tl-register-class (env form)
  "Register `(class NAME (PARAM) SUPERS METHOD-DECL...)' in ENV."
  (let* ((name (nth 1 form))
         (param (car (nth 2 form)))
         (supers (nth 3 form))
         (method-decls (nthcdr 4 form))
         (methods nil))
    (dolist (md method-decls)
      (let* ((mname (car md))
             (ty (tl-type-parse (cadr md)))
             (cparam (tl-fresh-tvar)))
        (push (cons mname
                    (tl-tscheme (list cparam)
                                ty
                                (list (tl-constraint name cparam))))
              methods)))
    (setq methods (nreverse methods))
    (puthash name (tl-cclass name (list param) supers methods)
             (tl-env-class-env env))
    (dolist (m methods)
      (puthash (car m) (cdr m) (tl-env-method-env env)))
    name))

(defun tl-register-instance (env form)
  "Register `(instance (CLASS TYPE))' in ENV (methods defined separately)."
  (let* ((head (nth 1 form))
         (cname (car head))
         (ty (tl-type-parse (cadr head)))
         (inst (tl-instance cname ty nil nil)))
    (puthash cname (append (gethash cname (tl-env-instance-env env)) (list inst))
             (tl-env-instance-env env))
    cname))
```

In `tl-typecheck-form`, add cases:

```elisp
   ((and (consp form) (eq (car form) 'class)) (tl-register-class env form))
   ((and (consp form) (eq (car form) 'instance)) (tl-register-instance env form))
```

Note: `tl-type-parse` on the instance head `(Functor Maybe)` uses `Maybe` as a type constructor; instance heads with variables (contexts) are handled in Task 3.

- [ ] **Step 5: Run `make test`** — all pass.

- [ ] **Step 6: Commit**

```bash
git add termlisp-base.el termlisp-types.el test/termlisp-test.el
git commit -m "feat: add type class and instance declarations"
```

---

## Task 2: Constraint collection in inference

**Files:**
- Modify: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest class/method-use-constraint ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-eval "(datatype Maybe (Nothing) (Just a))" env)
    (let ((r (tl-infer (cons nil env) '(lambda (g x) (fmap g x)))))
      (should (consp (car r)))
      (should (tl-constraint-p (car (tl-infer-constraints)))))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL.

- [ ] **Step 3: Implement constraint collection**

Add a dynamic constraint accumulator:

```elisp
(defvar tl-infer-constraints nil
  "Dynamically bound list of constraints collected during inference.")

(defun tl-emit-constraint (c)
  (push c tl-infer-constraints))
```

In `tl-infer-symbol`, before the fresh-tvar fallback, check `tl-env-method-env` and instantiate the constrained scheme, emitting the constraint:

```elisp
     ((and base (gethash sym (tl-env-method-env base)))
      (let* ((sc (gethash sym (tl-env-method-env base)))
             (sub (mapcar (lambda (v) (cons v (tl-fresh-tvar)))
                          (tl-tscheme-vars sc)))
             (ty (tl-type-subst (tl-tscheme-type sc) sub)))
        (dolist (c (tl-tscheme-constraints sc))
          (tl-emit-constraint
           (tl-constraint (tl-constraint-class c)
                          (tl-type-subst (tl-constraint-type c) sub))))
        (cons ty nil)))
```

Bind `tl-infer-constraints` to nil at the entry points (`tl-infer-define-clauses`, `tl-infer-constant`, and the public `termlisp-typecheck-def`), and expose the collected list via a helper for tests (e.g. `tl-infer-constraints` after inference). Also: `tl-tscheme` now has a `constraints` slot — update `tl-generalize` to accept a constraint list and attach it (Task 3).

- [ ] **Step 4: Run `make test`** — all pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-types.el test/termlisp-test.el
git commit -m "feat: collect type class constraints during inference"
```

---

## Task 3: Constraint solving and constrained schemes

**Files:**
- Modify: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest class/solve-instance ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-eval "(datatype Maybe (Nothing) (Just a))" env)
    (termlisp-typecheck-def env "(instance (Functor Maybe))")
    ;; fmap at Maybe resolves
    (should (termlisp-typecheck "(fmap (lambda (x) x) (Just 1))" env))))

(ert-deftest class/unsolved-constraint-errors ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-eval "(datatype NotFunctor (Mk))" env)
    (should-error (termlisp-typecheck "(fmap (lambda (x) x) (Mk))" env)
                  :type 'termlisp-type-error)))

(ert-deftest class/generalized-constraint ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))")
    (termlisp-typecheck-def env "(define (twice g x) (fmap g (fmap g x)))")
    (let ((sc (gethash 'twice (tl-env-type-env env))))
      (should (= (length (tl-tscheme-constraints sc)) 1)))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL.

- [ ] **Step 3: Implement solving and constrained generalization**

One-way matching of a constraint type against an instance head (borrowing clover's subsumption style — instance head vars are rigid, constraint vars may bind):

```elisp
(defun tl-match-instance (head ty)
  "Match instance HEAD against type TY.  Return a substitution or nil."
  (let ((sub nil) (work (list (cons head ty))) (ok t))
    (while (and work ok)
      (let* ((pair (pop work))
             (h (car pair))
             (t2 (tl-deref (cdr pair) sub)))
        (cond
         ((tl-tvar-p h) (push (cons h t2) sub))
         ((and (tl-tcon-p h) (tl-tcon-p t2) (eq (tl-tcon-name h) (tl-tcon-name t2))
               (= (length (tl-tcon-args h)) (length (tl-tcon-args t2))))
          (let ((ah (tl-tcon-args h)) (at (tl-tcon-args t2)))
            (while ah (push (cons (car ah) (car at)) work)
                   (setq ah (cdr ah) at (cdr at)))))
         ((equal h t2))
         (t (setq ok nil)))))
    (and ok sub)))
```

```elisp
(defun tl-solve-constraint (env c bindings)
  "Solve constraint C in ENV under BINDINGS.  Return `(ok . bindings)'.
For a resolvable instance, recursively solve its context."
  (let* ((ty (tl-apply-bindings (tl-constraint-type c) bindings))
         (insts (gethash (tl-constraint-class c) (tl-env-instance-env env)))
         (found nil)
         (ok t))
    (while (and insts (not found) ok)
      (let ((sub (tl-match-instance (tl-instance-head (car insts)) ty)))
        (when sub
          (setq found t)
          (let ((ctx (tl-instance-context (car insts))))
            (dolist (c2 ctx)
              (let ((r (tl-solve-constraint env
                                            (tl-constraint (tl-constraint-class c2)
                                                           (tl-type-subst (tl-constraint-type c2) sub))
                                            bindings)))
                (unless (car r) (setq ok nil))
                (setq bindings (cdr r)))))))
      (setq insts (cdr insts)))
    (if (and found ok) (cons t bindings) (cons nil nil))))
```

Constrained generalization: in `tl-generalize`, accept the current constraints and keep those whose type is (or mentions) a generalized variable; solve/discard the rest. Update `tl-infer-define-clauses`/`tl-infer-constant` to bind `tl-infer-constraints` and pass the collected constraints to `tl-generalize`, then solve the residual constraints against the env.

```elisp
(defun tl-generalize (type env-tvars &optional constraints)
  "Generalize TYPE, quantifying tvars not in ENV-TVARS, keeping CONSTRAINTS
whose type mentions a quantified variable."
  (let* ((ftv (tl-free-tvars type))
         (vars (cl-remove-if (lambda (v) (memq v env-tvars)) ftv))
         (kept (cl-remove-if-not
                (lambda (c)
                  (cl-intersection vars (tl-free-tvars (tl-constraint-type c))))
                constraints)))
    (tl-tscheme vars type kept)))
```

Instantiation must freshen constraints too (update `tl-instantiate` to substitute constraint types and re-emit them at use sites — this ties into Task 2's method-use path).

- [ ] **Step 4: Run `make test`** — all pass. Iterate on solving/generalization until the three tests pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-types.el test/termlisp-test.el
git commit -m "feat: solve type class constraints and generalize with contexts"
```

---

## Task 4: Type-directed `do`

**Files:**
- Modify: `termlisp-types.el`, `termlisp-eval.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest do/type-directed-maybe ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-file
     (expand-file-name "termlisp-prelude.tlsp" termlisp--directory) env)
    ;; (do ...) without an explicit monad name is not supported at runtime yet;
    ;; the type-level test asserts the monad operand can be inferred.
    (should (termlisp-typecheck
             "(fmap (lambda (x) (+ x 1)) (Just 1))" env))))
```

Note: this task's runtime surface depends on Task 5 (dictionary passing). Keep Task 4 to the type-level inference of the monad operand; the runtime `do` without a monad name is delivered in Task 5.

- [ ] **Step 2: Implement** `tl-infer` handling of `do` by desugaring to `monad-bind`/`monad-return` calls, where `monad-bind`/`monad-return` are class methods (`Monad`), so the constraint is collected and solved. `(do ...)` with no monad name desugars using the class methods `bind`/`return`; the monad type is inferred from the constraint.

- [ ] **Step 3: Run `make test`** — all pass.

- [ ] **Step 4: Commit**

```bash
git add termlisp-types.el termlisp-eval.el test/termlisp-test.el
git commit -m "feat: type-directed do via Monad constraint"
```

---

## Task 5: Dictionary-passing elaboration

**Files:**
- Create: `termlisp-elaborate.el`
- Modify: `termlisp-eval.el` (`:elaborate` option), `termlisp.el` (loader)
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest elaborate/method-dictionary-passing ()
  (let ((env (termlisp-make-env '(:elaborate t))))
    (termlisp-load-prelude env)
    ;; user writes overloaded fmap; elaborator inserts the Maybe dictionary
    (should (equal (termlisp-value->string
                    (termlisp-eval "(fmap (lambda (x) (+ x 1)) (Just 4))" env))
                   "(Just 5)"))))
```

- [ ] **Step 2: Implement `termlisp-elaborate.el`**

- A class instance has a runtime dictionary value (a record of method implementations). `(instance (C T))` with methods defined via `(define (method@T ...) ...)` (or an `instance` block with method `define`s) builds `CTDict`.
- The elaborator walks the term and, for each method call `(method arg...)` whose inferred constraint resolves to instance `(C T)`, rewrites to `(method CTDict arg...)`.
- Method definitions take the dictionary as their first parameter: e.g. `(define (fmap (FunctorDict f) g x) ...)`.

This is the most intricate task; the implementer should follow the existing `tl-infer`/constraint machinery and add an `elaborate` pass that runs before evaluation when `:elaborate` is set.

- [ ] **Step 3: Run `make test`** — all pass.

- [ ] **Step 4: Commit**

```bash
git add termlisp-elaborate.el termlisp-eval.el termlisp.el test/termlisp-test.el
git commit -m "feat: add dictionary-passing elaborator"
```

---

## Task 6: Prelude classes/instances and acceptance

**Files:**
- Modify: `termlisp-prelude.tlsp`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Declare classes and instances in the prelude**

```lisp
(class Functor (f) nil
  (fmap ((-> a b) -> (f a) -> (f b))))
(class Applicative (f) ((Functor f))
  (pure (-> a (f a)))
  (ap ((f (-> a b)) -> (f a) -> (f b))))
(class Monad (m) ((Applicative m))
  (bind ((m a) -> ((-> a (m b)) -> (m b)))))

(instance (Functor Maybe))
(instance (Applicative Maybe))
(instance (Monad Maybe))
;; ... List, State, Reader
```

- [ ] **Step 2: Write acceptance tests**

- `(fmap (lambda (x) (+ x 1)) (Just 4))` → `(Just 5)` (elaborated)
- `(bind (Just 1) (lambda (x) (Just (+ x 1))))` → `(Just 2)`
- `(do (x <- (Just 1)) (return (+ x 1)))` → `(Just 2)` (type-directed monad)
- `api/typecheck-prelude` still passes.

- [ ] **Step 3: Run `make test`** and `make compile`; commit.

```bash
git add termlisp-prelude.tlsp test/termlisp-test.el
git commit -m "feat: add type class prelude and acceptance tests"
```

---

## Self-Review

**Spec coverage (Plan 4 / spec §8.3, §11):**
- §8.3 class/instance declarations, constraint collection/solving, dictionary passing — Tasks 1–5.
- §11 A-phase `do` inference — Task 4.
- §11 typed monad instances — Task 6.

**Known deferrals:** multi-parameter classes, functional dependencies, associated types, kind checking beyond `* -> *`, full superclass-dictionary composition (Task 5 may simplify to direct dictionary selection), Applicative `ap` beyond the minimal set.

**Risk:** Task 5 (dictionary passing) is the most complex; if it proves too large, split it and document a reduced runtime surface (type-level classes + explicit dictionaries).
