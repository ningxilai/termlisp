# TODO

Work archive for the post-Stage-2 round.  Every node starts unchecked; a node is
ticked only when its listed acceptance criteria hold on a committed tree with all
four gates green (`make compile` 0 warnings, `make test`, checkdoc multiset zero
new, `parsecheck.sh` OK).  Status values: `[ ]` not started, `[~]` in progress,
`[x]` done.

## 表一：上轮报告缺陷

- [x] **P0-1 递归 `define` + `:type-check t` bare env 崩溃** — `excessive-lisp-nesting`
  via `tl-kind-infer` self-reference (kinds.el:499).  The bare `(Succ n)'
  spelling parses the field name as a type parameter, so the clause asks
  for the pattern variable's type to be `Nat' of itself; `:occurs-check'
  nil admits that equirecursive knot by design, and kind inference was
  the one walk without a cycle guard.  Fixed coinductively: an
  application node carries a provisional kind variable in its KIND slot
  while its own kind is being inferred, re-entry reads the assumption
  back, and the assumption is unified with the walked kind -- a cycle
  that would need two kinds at once is still a kind error.  Shape
  dispatch extracted to `tl-kind-infer--node'.
  - [x] Repro pinned as a failing-first test
    (`tl-checked-recursion-on-a-bare-environment' in aldor-test.el).
  - [x] Fix lands; repro matrix all four cells green (bare/checked,
    bare/unchecked, prelude/checked, prelude/unchecked), plus the
    self-application cycle, no nesting crash.
  - [x] Full suite green (463/463), compile 0 warnings, checkdoc 0 new,
    parsecheck OK.
- [x] **P1-2 `termlisp-typecheck-def` docstring lies** — types.el:2181 said
  "Return ENV." but the last form was `(tl-run-post-batch)', so the return
  value belonged to the coverage hook.  Decided truth: the driver really
  returns ENV (which makes `termlisp-typecheck''s own "Return ENV" promise
  true as well), with a comment saying why the value cannot be the hook's
  leftovers.  Swept every "Return" promise in types.el: the one other
  "Return ENV" (`tl-typecheck-ir') is true -- `dolist''s third argument --
  and no same-shaped lies remain.
  - [x] Regression test pins the return value even when the post-batch
    hook returns something else (`tl-ch-batch-driver-returns-the-env-it-checked-into').
- [ ] **P2-3 Undocumented accessors** — types.el:76, :79, :106-109, :1002.  Add
  docstrings; consider `--` internal naming where they are not API.
- [ ] **P1-4 `termlisp-ir-types` layering** — only the umbrella `termlisp.el`
  requires it; requiring submodules directly misses builtin-type registrations
  (`seq` unknown → `tl-canonical-key` crashes).  Add the require to the real
  consumer module (not the umbrella), or document the umbrella-only contract.
  - [ ] `(require 'termlisp-load)` alone loads prelude successfully.
- [ ] **P3-5 `tl-dpo-normalize` production-dead** — decided by F2 below: if kind
  normalization adopts it, it gains a production caller; otherwise document it as
  the entry point for callers needing the reduction graph.  Closed by F5.

## 表二：System Fω 推进（F2 即 `tl-dpo-last-gluing` 的消费者）

- [ ] **F1 kind 保持性检查器** — kind mirror of `tl-preserve-check`: freeze open
  type variables of type-level rules as kind metavariables, normalize both sides
  at the kind level, compare; refuse when kinds do not match.
  - [ ] kind-oracle over the type-level rule set: preserved / violated /
    cannot-check buckets.
  - [ ] Tests pin at least one violating rule as a refusal.
- [ ] **F2 类型层 `rewrite`/`reduce` 落地，门控于 F1 + 局部性** — the
  `tl-dpo-last-gluing` consumer: kind-level normalization runs through
  `tl-dpo-normalize` and `tl-dpo--step-gluing`; the checker reads
  `tl-dpo-last-gluing` and refuses on any non-nil verdict (dangling / cross-rule
  escape), because a kind cannot be re-generalized the way a value can.
  - [ ] Non-nil gluing type-level rule rejected with `termlisp-type-error`.
  - [ ] Nil gluing passes unchanged.
- [ ] **F3 prelude 获得类型层规则** — e.g. `Vec` arithmetic, type-level `+`,
  every rule through the F1+F2 gate.
  - [ ] Every prelude type-level rule lands in its oracle bucket.
- [ ] **F4 Fω 表达力测试** — higher-kinded polymorphism (`Functor` at `* -> *`),
  type-level lambda application, kind inference on open terms, NBE equality
  under type binders; end-to-end Fω samples with higher-kinded instances.
- [ ] **F5 文档与门收口** — README Fω section; kind-oracle joins the standing
  gates; P3-5 closes here.

## Notes

- P0-1 (the recursion crash) was scheduled before F1 because kind-preservation
  verification of type-level rules meets the same self-reference unfolding; it
  is fixed, so F1 inherits the cycle guard for free.
- Standing gates unchanged: 0 byte-compile warnings, checkdoc multiset zero new
  vs `7ff25f7`, parsecheck OK, full ert suite green.  `make compile` starts with
  `rm -f *.elc`.
