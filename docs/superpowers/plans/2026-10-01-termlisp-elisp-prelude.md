# term-lisp Emacs Lisp Port — Plan 5: Full Prelude and Acceptance Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the term-lisp prelude (list library, assertions, higher-order helpers) and add end-to-end acceptance tests and examples that exercise the whole system (evaluator, types, monads, type classes).

**Architecture:** Additions are ordinary term-lisp definitions in `termlisp-prelude.tlsp` (plus a few elisp builtins if needed). Acceptance tests load the prelude and evaluate programs. No new core machinery is expected.

**Tech Stack:** Emacs Lisp (`ert`), term-lisp `.tlsp`.

**Scope:** Prelude completeness + acceptance. Multi-parameter type classes, full dictionary threading through polymorphic functions, and the JS implementation's removal are out of scope (the JS sources remain for reference).

---

## File Structure

```
termlisp-prelude.tlsp   ; list library, assertions, helpers
termlisp-builtins.el    ; any new primitives (e.g. `print`-free string ops) if needed
examples/*.tlsp         ; example programs
test/termlisp-test.el   ; prelude + acceptance tests
README.md               ; note the elisp port
```

---

## Task 1: List library

**Files:** modify `termlisp-prelude.tlsp`; test `test/termlisp-test.el`.

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest prelude/list-head-tail ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(head (Cons A (Cons B Nil)))" env) 'A))
    (should (equal (termlisp-value->string (termlisp-eval "(tail (Cons A (Cons B Nil)))" env))
                   "(Cons B Nil)"))))

(ert-deftest prelude/list-length-append ()
  (let ((env (termlisp-load-prelude)))
    (should (= (termlisp-eval "(length (Cons A (Cons B (Cons C Nil))))" env) 3))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(append (Cons A Nil) (Cons B (Cons C Nil)))" env))
                   "(Cons A (Cons B (Cons C Nil)))"))))

(ert-deftest prelude/list-map-filter-foldr ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(map-list (lambda (x) (+ x 1)) (Cons 1 (Cons 2 Nil)))" env))
                   "(Cons 2 (Cons 3 Nil))"))
    (should (equal (termlisp-value->string
                    (termlisp-eval "(filter (lambda (x) (eq x 1)) (Cons 1 (Cons 2 Nil)))" env))
                   "(Cons 1 Nil)"))
    (should (= (termlisp-eval "(foldr (lambda (x acc) (+ x acc)) 0 (Cons 1 (Cons 2 (Cons 3 Nil))))" env)
               6))))
```

- [ ] **Step 2: Implement in the prelude** (names chosen to avoid clashing with the existing higher-order `map`):

```lisp
(define (head (Cons x xs)) x)
(define (tail (Cons x xs)) xs)
(define (length Nil) 0)
(define (length (Cons x xs)) (+ 1 (length xs)))
(define (append Nil ys) ys)
(define (append (Cons x xs) ys) (Cons x (append xs ys)))
(define (map-list f Nil) Nil)
(define (map-list f (Cons x xs)) (Cons (f x) (map-list f xs)))
(define (filter f Nil) Nil)
(define (filter f (Cons x xs)) (if (f x) (Cons x (filter f xs)) (filter f xs)))
(define (foldr f z Nil) z)
(define (foldr f z (Cons x xs)) (f x (foldr f z xs)))
```

Note: `map-list` is used because the prelude already defines a higher-order `map` (apply a function to one argument). If you prefer to unify, rename the existing `map` and update its tests — but keep all existing tests green.

- [ ] **Step 3: Run `make test`**; `make compile`. Iterate until green.
- [ ] **Step 4: Commit** `feat: add list library to prelude`.

---

## Task 2: Assertions and parity with the original prelude

**Files:** modify `termlisp-prelude.tlsp`; test `test/termlisp-test.el`.

- [ ] **Step 1: Tests**

```elisp
(ert-deftest prelude/assert-equal ()
  (let ((env (termlisp-load-prelude)))
    (should (termlisp-eval "(assertEqual (Cons 1 Nil) (Cons 1 Nil))" env))))

(ert-deftest prelude/boolean-law ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(and (not (and True False)) (or True False))" env) 'True))))
```

- [ ] **Step 2: Implement**

```lisp
(define (assertEqual a b) (if (eq a b) True (error "not equal")))
```

(`error` may not exist as a builtin; if so, define `assertEqual` to return `True`/`False` instead, and adjust the test accordingly. Do not add side-effecting IO.)

- [ ] **Step 3: Run `make test`; commit** `feat: add assertions to prelude`.

---

## Task 3: Examples

**Files:** `examples/*.tlsp`; test `test/termlisp-test.el`.

- [ ] **Step 1: Add example programs**

- `examples/lists.tlsp`: define a list, `map-list`/`filter`/`foldr` over it.
- `examples/classes.tlsp`: use `fmap`/`bind`/`do` over Maybe/List.
- `examples/nat.tlsp` (existing): keep.
- `examples/bool.tlsp` (existing): keep.

- [ ] **Step 2: Acceptance tests** load the prelude and evaluate each example, asserting the result. Add `acceptance/examples-all`.

- [ ] **Step 3: Run `make test`; commit** `test: add examples and acceptance`.

---

## Task 4: README and cleanup

**Files:** `README.md`.

- [ ] **Step 1:** Add a short section documenting the Emacs Lisp port: how to load (`(require 'termlisp)`), the API (`termlisp-eval`, `termlisp-typecheck`, `termlisp-load-prelude`, `:type-check`/`:elaborate` options), and that the JS implementation is superseded.
- [ ] **Step 2: Commit** `docs: document the elisp port in README`.

---

## Self-Review

**Spec coverage:** §12 API (already implemented) — documented in README; §13 acceptance — Tasks 3/4; prelude parity — Tasks 1/2.

**Deferrals:** full polymorphic dictionary threading; multi-parameter classes; removing the JS sources.
