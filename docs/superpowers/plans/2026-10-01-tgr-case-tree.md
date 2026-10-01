# Plan 7.5: TGR case-tree matcher (Idris-style) Implementation Plan

> Small tasks; each independently testable. Design: `docs/superpowers/specs/2026-10-01-tgr-case-tree-design.md`.

**Goal:** Replace the ad-hoc `(:rest)`/`(:splice)`/function-template rule matching with a proper `Pat` AST and Idris-style clause→decision-tree compilation.

**Repos:** `/home/iris/termlisp` (`termlisp-graph.el`, new `termlisp-case.el`; `dev` has tests, `main` implementation, sync as before). Then `/home/iris/lisp` (`setup.el`).

---

## Task 1: Pattern AST

**Files:** create `termlisp-case.el`; modify `termlisp.el`; test.

- `tl-pat-parse (sexp)` → compiled pattern:
  - `(pvar NAME)`, `(pwild)`, `(plit VALUE)`, `(pcon HEAD PAT...)`,
    `(pas NAME PAT)`, `(pnil)`, `(plist PAT...)`.
- Tests: parse shapes; a `(plist ...)` expands to cons/nil `pcon`s.

## Task 2: Single-clause structural match

**Files:** `termlisp-case.el`; test.

- `tl-pat-match (pat node bindings)` → `(ok . bindings)`; supports pvar/pwild/plit/pcon/pas/pnil; lists via pcon cons/nil.
- Tests: var, wildcard, literal, constructor, as-pattern, nested list.

## Task 3: Clause compilation (decision tree)

**Files:** `termlisp-case.el`; test.

- `tl-case-compile (clauses)` → tree: `tl-ct-case (column alts)`, `tl-ct-leaf (clause-idx)`, `tl-ct-fail`; alts `tl-ct-con (head arity tree)`, `tl-ct-const (value tree)`, `tl-ct-default tree`.
- Column-wise (0=head, 1..=args), partition by con/const at leftmost non-variable column, default group; mirror `CaseBuilder`.
- Tests: two clauses discriminated by head; by a constructor arg; default catch-all; first-match order.

## Task 4: Case match + templates

**Files:** `termlisp-case.el`; test.

- `tl-case-match (tree node bindings)` → bindings or nil.
- Template instantiation from bindings, including list bindings (splice).
- Tests: nested dispatch; list-binding template builds a `:seq`.

## Task 5: Integrate into the TGR

**Files:** `termlisp-graph.el`, `termlisp-case.el`; test.

- `tl-grule` gains a clause list; `tl-graph-apply` compiles the rule set for a symbol and matches via the case tree. Remove `(:rest)`/`(:splice)`/function-template from matching.
- Keep phases/priority, in-place update, fuel, opaque `quote`/`function`.
- Migrate the existing TGR tests; `make test` passes.

## Task 6: Port setup

**Files:** `/home/iris/lisp/setup.el`; test.

- Rewrite `setup-rules` as clauses; variadic keywords via `plist` over args.
- Remove `setup--chunk-template`/`setup--chunk-guard`/function templates; keep dotted-pair handling only if still required (justify).
- `make test` (105+) passes; config macroexpand check 240/0.

## Verify (each task)

`make test` + `make compile` clean; commit per task.
