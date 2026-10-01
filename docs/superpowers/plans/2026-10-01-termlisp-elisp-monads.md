# term-lisp Emacs Lisp Port — Plan 3: Monads and `do` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add language-level monads (explicit dictionaries, phase B) with `do` notation, plus a cats-backed Reader monad in the implementation layer.

**Architecture:** A monad instance is an ordinary term-lisp value: a `MonadDict` record holding `bind`/`return`/`fmap` functions. Generic `monad-bind`/`monad-return`/`monad-fmap` pattern-match the dictionary. `do` is a special form in the evaluator that desugars to `monad-bind`/`monad-return` calls. Instances for Maybe, List, State, and Reader are defined in the prelude (State/Reader use closures + pattern-matching helpers). The library's elisp API additionally exposes a cats-based Reader monad (`termlisp-data-reader.el`).

**Tech Stack:** Emacs Lisp (`cl-lib`, `ert`); vendored `emacs-cats` for the implementation-layer Reader.

**Scope:** Phase B (explicit monad names). Type-class inference of the monad operand (phase A) is Plan 4. Refactoring the evaluator itself onto cats is deferred (documented). `Monoid` instances deferred.

**Reference:** cats' Functor/Applicative/Monad interfaces (`vendor/cats`).

---

## File Structure

```
termlisp-data-reader.el ; cats-based Reader monad (elisp API)
termlisp-eval.el        ; `do` special form desugaring
termlisp-prelude.tlsp   ; MonadDict datatype, generic ops, Maybe/List/State/Reader instances
test/termlisp-test.el   ; monad tests
```

---

## Task 1: cats-based Reader monad (implementation layer)

**Files:**
- Create: `termlisp-data-reader.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(require 'termlisp-data-reader)

(ert-deftest reader/pure-and-run ()
  (let ((m (cats-pure (tl-data-reader) 42)))
    (should (= (tl-run-reader m :env) 42))))

(ert-deftest reader/ask ()
  (should (eq (tl-run-reader (tl-reader-ask) :env) :env)))

(ert-deftest reader/fmap ()
  (let ((m (cats-fmap (lambda (x) (1+ x)) (cats-pure (tl-data-reader) 41))))
    (should (= (tl-run-reader m :env) 42))))

(ert-deftest reader/bind ()
  (let ((m (cats-bind (tl-reader-ask)
                      (lambda (r) (cats-pure (tl-data-reader) (list r r))))))
    (should (equal (tl-run-reader m :cfg) '(:cfg :cfg)))))

(ert-deftest reader/local ()
  (let ((m (tl-reader-local (lambda (_) :inner) (tl-reader-ask))))
    (should (eq (tl-run-reader m :outer) :inner))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL (`tl-data-reader` void / cats not loaded).

- [ ] **Step 3: Implement `termlisp-data-reader.el`**

```elisp
;;; termlisp-data-reader.el --- Reader monad -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A cats-style Reader monad: a computation `env -> a'.

;;; Code:

(require 'cl-lib)
(require 'eieio)
(require 'cats-data-monad)
(require 'cats-data-applicative)
(require 'cats-data-functor)

(defclass tl-data-reader ()
  ((run :initarg :run :accessor tl-data-reader-run))
  :documentation "Reader monad: RUN is a function of the environment.")

(defun tl-reader-pure (v)
  "Return a Reader that ignores the environment and yields V."
  (tl-data-reader :run (lambda (_env) v)))

(defun tl-reader-ask ()
  "Return a Reader that yields the environment."
  (tl-data-reader :run #'identity))

(defun tl-reader-local (f m)
  "Run M under the environment transformed by F."
  (tl-data-reader :run (lambda (env) (funcall (tl-data-reader-run m) (funcall f env)))))

(defun tl-run-reader (m env)
  "Run Reader M with ENV."
  (funcall (tl-data-reader-run m) env))

(cl-defmethod cats-pure ((_this tl-data-reader) v)
  (tl-reader-pure v))

(cl-defmethod cats-fmap (f (m tl-data-reader))
  (tl-data-reader :run (lambda (env) (funcall f (tl-run-reader m env)))))

(cl-defmethod cats-apply ((mf tl-data-reader) (mx tl-data-reader))
  (tl-data-reader :run (lambda (env)
                         (funcall (tl-run-reader mf env)
                                  (tl-run-reader mx env)))))

(cl-defmethod cats-bind ((m tl-data-reader) f)
  (tl-data-reader :run (lambda (env)
                         (tl-run-reader (funcall f (tl-run-reader m env)) env))))

(provide 'termlisp-data-reader)
;;; termlisp-data-reader.el ends here
```

- [ ] **Step 4: Run `make test`** — all pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-data-reader.el test/termlisp-test.el
git commit -m "feat: add cats-based Reader monad (implementation layer)"
```

---

## Task 2: Monad dictionaries and generic operations

**Files:**
- Modify: `termlisp-prelude.tlsp` (add `MonadDict` datatype + generic ops + Maybe/List instances)
- Modify: `termlisp-monad.el` (create: `_monad`-level elisp helpers if needed)
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest monad/maybe-return ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(monad-return MaybeDict 5)" env))
                   "(Just 5)"))))

(ert-deftest monad/maybe-bind-just ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (Just 3) (lambda (x) (Just (+ x 1))))" env))
                   "(Just 4)"))))

(ert-deftest monad/maybe-bind-nothing ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(monad-bind MaybeDict Nothing (lambda (x) (Just x)))" env)
                'Nothing))))

(ert-deftest monad/list-return-and-bind ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(monad-return ListDict 1)" env))
                   "(Cons 1 Nil)"))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (Cons 1 (Cons 2 Nil)) (lambda (x) (Cons (+ x 10) Nil)))" env))
                   "(Cons 11 (Cons 12 Nil))"))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL (`monad-return` unbound).

- [ ] **Step 3: Add to `termlisp-prelude.tlsp`**

```lisp
;; Monads (phase B: explicit dictionaries)

(datatype MonadDict (MonadDict bind return fmap))
(datatype Maybe (Nothing) (Just a))
(datatype List (Nil) (Cons a List))

(define (monad-return (MonadDict bind return fmap) v) (return v))
(define (monad-bind (MonadDict bind return fmap) m k) (bind m k))
(define (monad-fmap (MonadDict bind return fmap) f m) (fmap f m))

;; Maybe instance
(define (maybe-return v) (Just v))
(define (maybe-bind Nothing k) Nothing)
(define (maybe-bind (Just v) k) (k v))
(define (maybe-fmap f Nothing) Nothing)
(define (maybe-fmap f (Just v)) (Just (f v)))
(define MaybeDict (MonadDict maybe-bind maybe-return maybe-fmap))

;; List instance
(define (list-return v) (Cons v Nil))
(define (list-append Nil ys) ys)
(define (list-append (Cons x xs) ys) (Cons x (list-append xs ys)))
(define (list-bind Nil k) Nil)
(define (list-bind (Cons x xs) k) (list-append (k x) (list-bind xs k)))
(define (list-fmap f Nil) Nil)
(define (list-fmap f (Cons x xs)) (Cons (f x) (list-fmap f xs)))
(define ListDict (MonadDict list-bind list-return list-fmap))
```

- [ ] **Step 4: Run `make test`** — all pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-prelude.tlsp test/termlisp-test.el
git commit -m "feat: add monad dictionaries and Maybe/List instances"
```

---

## Task 3: `do` special form

**Files:**
- Modify: `termlisp-eval.el` (`tl-eval-top` handles `do`)
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest do/maybe ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do MaybeDict (x <- (Just 1)) (y <- (Just 2)) (return (+ x y)))" env))
                   "(Just 3)"))
    (should (eq (termlisp-eval
                 "(do MaybeDict (x <- (Just 1)) (y <- Nothing) (return (+ x y)))" env)
                'Nothing))))

(ert-deftest do/list ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(do ListDict (x <- (Cons 1 (Cons 2 Nil))) (return (+ x 10)))" env))
                   "(Cons 11 (Cons 12 Nil))"))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL (evaluates `do` as an open constructor).

- [ ] **Step 3: Implement `do` desugaring in `termlisp-eval.el`**

Add a desugarer and handle it in `tl-eval-top`:

```elisp
(defun tl-desugar-do (form)
  "Desugar `(do DICT STMT...)' into nested monad-bind/monad-return calls.
Each STMT is `(NAME <- EXPR)' or a bare monadic expression; the block must
end with `(return EXPR)'."
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
                        (list 'lambda '(_) acc)))))
    acc))
```

In `tl-eval-top`, add before the fallback:

```elisp
   ((and (consp form) (eq (car form) 'do))
    (tl-run (tl-desugar-do form) nil))
```

- [ ] **Step 4: Run `make test`** — all pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-eval.el test/termlisp-test.el
git commit -m "feat: add do-notation special form"
```

---

## Task 4: State and Reader language instances

**Files:**
- Modify: `termlisp-prelude.tlsp`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest monad/state ()
  (let ((env (termlisp-load-prelude)))
    ;; state: s -> (Pair a s) ; run with 0, increment, return the old value
    (should (equal (termlisp-value->string
                    (termlisp-eval
                     "((run-state
                        (do StateDict
                          (n <- (state-get))
                          (state-put (+ n 1))
                          (return n)))
                       0)"
                     env))
                   "(Pair 0 1)"))))

(ert-deftest monad/reader ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval
                 "((run-reader (do ReaderDict (r <- (reader-ask)) (return r))) cfg)"
                 env)
                'cfg))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL.

- [ ] **Step 3: Add State/Reader instances to `termlisp-prelude.tlsp`**

```lisp
;; State instance: a computation is a function s -> (Pair a s)
(define (state-return v) (lambda (s) (Pair v s)))
(define (state-bind-step (Pair a s2) k) ((k a) s2))
(define (state-bind m k) (lambda (s) (state-bind-step (m s) k)))
(define (state-fmap f m) (lambda (s) (state-fmap-step (m s) f)))
(define (state-fmap-step (Pair a s2) f) (Pair (f a) s2))
(define StateDict (MonadDict state-bind state-return state-fmap))

(define (state-get) (lambda (s) (Pair s s)))
(define (state-put v) (lambda (s) (Pair Unit v)))
(define run-state (lambda (m) m))

;; Reader instance: a computation is a function r -> a
(define (reader-return v) (lambda (r) v))
(define (reader-bind m k) (lambda (r) ((k (m r)) r)))
(define (reader-fmap f m) (lambda (r) (f (m r))))
(define ReaderDict (MonadDict reader-bind reader-return reader-fmap))
(define (reader-ask) (lambda (r) r))
(define (run-reader m) m)
```

(Add `(datatype Unit (Unit))` if `Unit` is used.)

- [ ] **Step 4: Run `make test`** — all pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-prelude.tlsp test/termlisp-test.el
git commit -m "feat: add State and Reader monad instances"
```

---

## Task 5: Monad laws

**Files:**
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the law tests**

For each instance, test left identity `bind (return a) f = f a`, right identity `bind m return = m`, and associativity. Compare via `termlisp-value->string` where values are not `eq`-comparable.

```elisp
(ert-deftest monad-laws/maybe ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (monad-return MaybeDict 5) (lambda (x) (Just (+ x 1))))" env))
                   (termlisp-value->string (termlisp-eval "(Just 6)" env))))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind MaybeDict (Just 5) (lambda (x) (monad-return MaybeDict x)))" env))
                   "(Just 5)"))))

(ert-deftest monad-laws/list ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(monad-bind ListDict (monad-return ListDict 5) (lambda (x) (Cons x Nil)))" env))
                   "(Cons 5 Nil)"))))
```

- [ ] **Step 2: Run `make test`** — all pass.

- [ ] **Step 3: Commit**

```bash
git add test/termlisp-test.el
git commit -m "test: add monad law tests"
```

---

## Self-Review

**Spec coverage (Plan 3 / spec §7, §11):**
- §11.1 implementation layer: cats-based Reader (`termlisp-data-reader.el`) — Task 1. Evaluator-on-cats refactor deferred (documented).
- §11.2 language layer: monad dictionaries, `do`, `return`/`bind`, instances Maybe/List/State/Reader — Tasks 2–4. Laws — Task 5.
- B-phase explicit monad name — Tasks 3–4.

**Known deferrals:** phase-A type-class inference of the monad operand (Plan 4); `Monoid` instances; evaluator-on-cats refactor; `do` for the `Reader`/`State` type-level (untyped phase B).

- `MonadDict` does not yet carry `apply`/`pure` (Applicative) — deferred to Plan 4.
- The spec surface `(do Maybe ...)` / `return` / `>>=` maps in phase B to `(do MaybeDict ...)` / `monad-return` / `monad-bind`; Plan 4's elaborator will provide the sugar.

**Type/name consistency:** `MonadDict` (bind/return/fmap), `monad-bind`/`monad-return`/`monad-fmap`, instance dictionaries `MaybeDict`/`ListDict`/`StateDict`/`ReaderDict`.
