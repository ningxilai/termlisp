# term-lisp Emacs Lisp Port — Plan 6: Graph Rewriter Core (TGR) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend term-lisp into a term-graph-rewriting (TGR) engine — shared nodes, update-in-place, rule sets with phase/priority control, and strict reduction to normal form — in the spirit of Clean/Dactl/OBJ3 (style only, not a full implementation).

**Architecture:** A term is a mutable graph of `tl-node`s (head + children + state + memo); children are shared node references (structural sharing via hash-consing on build). A rule (`tl-grule`) has a phase, a priority, a pattern, a template, and an optional guard. Reduction is strict: within each phase, apply the highest-priority matching rule to the leftmost-outermost redex, rewriting the node **in place** (memo), until no rule applies; then advance to the next phase. Phases only move forward, which guarantees termination alongside a progress check (a rewrite must change the node). The engine reuses term-lisp's `tl-match`/`tl-unify`/`tl-decompose` where possible.

**Tech Stack:** Emacs Lisp (`cl-lib`, `ert`); builds on the existing term-lisp modules.

**Scope:** TGR core only. The setup DSL (order-sorted signature, primitives, derived rules) is a follow-up plan built on this core. Non-injective/AC matching, concurrency (Dact), and Knuth-Bendix completion are out of scope.

---

## File Structure

```
termlisp-graph.el      ; nodes, graphs, rules, reduction, public interface
termlisp.el            ; add termlisp-graph to the loader
test/termlisp-test.el  ; TGR tests
```

---

## Task 1: Nodes, graphs, and building with sharing

**Files:** create `termlisp-graph.el`; modify `termlisp.el`; test `test/termlisp-test.el`.

- [ ] **Step 1: Failing tests**

```elisp
(require 'termlisp-graph)

(ert-deftest graph/build-atom ()
  (let* ((g (tl-graph-build 'foo))
         (n (tl-graph-root g)))
    (should (tl-node-p n))
    (should (eq (tl-node-head n) 'foo))
    (should (null (tl-node-children n)))))

(ert-deftest graph/build-application ()
  (let* ((g (tl-graph-build '(f a b)))
         (n (tl-graph-root g)))
    (should (eq (tl-node-head n) 'f))
    (should (= (length (tl-node-children n)) 2))
    (should (eq (tl-node-head (car (tl-node-children n))) 'a))))

(ert-deftest graph/sharing ()
  "Structurally identical subterms share one node."
  (let* ((g (tl-graph-build '(pair (f x) (f x))))
         (kids (tl-node-children (tl-graph-root g))))
    (should (eq (car kids) (cadr kids)))))

(ert-deftest graph/node-state ()
  (let ((n (tl-make-node 'f nil)))
    (should (eq (tl-node-state n) :idle))))
```

- [ ] **Step 2: Run `make test`** — expect FAIL.

- [ ] **Step 3: Implement `termlisp-graph.el`**

```elisp
;;; termlisp-graph.el --- Term graph rewriting core -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A term is a graph of mutable nodes (head + children + state + memo).
;; Children are shared node references (hash-consing on build).  Rules
;; rewrite nodes in place; reduction is strict and phase/priority ordered.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(cl-defstruct (tl-node (:constructor tl-make-node (head &optional children)))
  "A term graph node.
HEAD is a symbol/atom operator (or a literal value for leaves).
CHILDREN is a list of child `tl-node's (shared).
STATE is a Dactl-style control marker (:idle, :active, :done).
MEMO is the node's rewritten replacement, or nil."
  head children (state :idle) memo)

(cl-defstruct (tl-graph (:constructor tl-make-graph (root table)))
  "A term graph: ROOT node plus a sharing TABLE (sexp-key -> node)."
  root table)

(defun tl-graph-build (sexp)
  "Build a term graph from SEXP, sharing structurally identical subterms."
  (let ((table (make-hash-table :test #'equal)))
    (cl-labels ((build (x)
                  (let ((cell (gethash x table)))
                    (if cell cell
                      (let ((node (if (consp x)
                                      (tl-make-node (car x) (mapcar #'build (cdr x)))
                                    (tl-make-node x nil))))
                        (puthash x node table)
                        node)))))
      (tl-make-graph (build sexp) table))))

(provide 'termlisp-graph)
;;; termlisp-graph.el ends here
```

Add `termlisp-graph` to the loader in `termlisp.el` (hard require).

- [ ] **Step 4: Run `make test`; `make compile`.** Commit `feat: add TGR nodes, graphs, and shared build`.

---

## Task 2: Rules and in-place rewriting

**Files:** modify `termlisp-graph.el`; test `test/termlisp-test.el`.

- [ ] **Step 1: Failing tests**

```elisp
(ert-deftest graph/rule-rewrite-in-place ()
  (let* ((g (tl-graph-build '(global "C-c f" foo)))
         (r (tl-make-grule 'g :normalize 0 '(global ?key ?cmd)
                           '(bind (quote current-global-map) ?key ?cmd))))
    (tl-graph-rewrite graph r)
    ...))
```

(Exact API settled during implementation; the rule rewrites the root node's head/children to the template.)

- [ ] **Step 2: Implement rule matching/instantiation**

- `tl-grule` = name/phase/priority/pattern/template/guard.
- `tl-graph-match (pattern node)` → bindings alist or nil (reuse `tl-match` if the pattern is in term-lisp pattern syntax; otherwise a small matcher over `tl-node`).
- `tl-graph-instantiate (template bindings graph)` → a node (reusing existing nodes for bound variables, preserving sharing).
- `tl-graph-apply (graph rule node)` → rewrite NODE in place (set head/children/memo), returning t on progress.

- [ ] **Step 3: Run `make test`.** Commit `feat: add TGR rules and in-place rewriting`.

---

## Task 3: Phased, priority-ordered, strict reduction

**Files:** modify `termlisp-graph.el`; test `test/termlisp-test.el`.

- [ ] **Step 1: Failing tests**

```elisp
(ert-deftest graph/phase-order ()
  ;; a rule in a later phase must not fire before an earlier-phase rule
  ...)

(ert-deftest graph/priority ()
  ;; lower priority number fires first
  ...)

(ert-deftest graph/normal-form ()
  ;; no rule applies -> normal-form predicate is true
  ...)

(ert-deftest graph/no-progress-error ()
  ;; a rule whose output equals its input signals an error
  ...)

(ert-deftest graph/strict-normalization ()
  ;; all redexes (including under the root) are reduced
  ...)
```

- [ ] **Step 2: Implement**

- `tl-graph-rewrite (graph rules)` — for each phase in `tl-graph-phases` order, repeatedly find the leftmost-outermost redex whose rule phase matches and has the highest priority (lowest number), apply it; stop the phase when no rule applies; advance.
- `tl-graph-normal-form-p (graph rules)`.
- Progress check: a rewrite that does not change the node signals `termlisp-eval-error` ("Non-progressing rewrite").
- Phase list: `(:surface :normalize :desugar :context :control :load :action :backend)`.

- [ ] **Step 3: Run `make test`; `make compile`.** Commit `feat: add phased strict TGR reduction`.

---

## Task 4: Public interface and integration

**Files:** modify `termlisp-graph.el`; test `test/termlisp-test.el`.

- [ ] **Step 1:** `tl-graph-rewrite-sexp (sexp rules)` → normal-form sexp (build graph, rewrite, render back). Add a `tl-node->sexp` renderer.
- [ ] **Step 2:** Reuse `tl-match`/`tl-unify` for non-linear patterns and guards; add tests for a guard and a non-linear pattern.
- [ ] **Step 3:** Run `make test`; commit `feat: add TGR public interface and matching integration`.

---

## Self-Review

**Coverage:** TGR representation + sharing (Task 1), rules + in-place rewrite (Task 2), phase/priority strict reduction + termination (Task 3), interface (Task 4). Setup DSL is a follow-up.

**Deferrals:** concurrency (Dact), AC/associative-commutative matching, Knuth-Bendix completion (clover-style), graph visualization.

**Termination argument:** rules are phase-ordered (only forward) and each rewrite must make progress; combined with a bounded rule set this gives termination on setup-shaped inputs.
