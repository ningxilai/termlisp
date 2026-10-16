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
- [x] **P2-3 Undocumented accessors** — types.el:76, :79, :106-109, :1002.
  Docstrings added: `tl-tcon-name'/`tl-tcon-args' (dereference first, leaf
  yields no arguments), `tl-tarrow'/`tl-tint'/`tl-tstring'/`tl-tbool', and
  `tl-tenv-locals' (the locals half of the inference-time pair).  All five
  are cross-file API -- kept their names rather than `--' internal ones.  A
  mechanical sweep of every defun in types.el for a missing docstring is now
  clean (the one apparent holdout was `tl-type-parse*', which has one).
- [x] **P1-4 `termlisp-ir-types` layering** — only the umbrella `termlisp.el`
  required it, so requiring submodules directly missed builtin-type
  registrations (`seq` unknown → `Unknown symbol: seq`).  The real consumer is
  `termlisp-eval`: its `:type-check` path reads `tl-builtin-types` and
  `termlisp-load-prelude` walks the prelude through it, and it already required
  the runtime table's home (`termlisp-builtins`) while the type table lagged
  behind.  Added `(require 'termlisp-ir-types)` there with a comment saying why
  the edge lives in this layer (load/repl inherit it; the dependency closure is
  acyclic), and documented in `tl-builtin-types`'s docstring where the bundled
  schemes arrive and what a host requiring `termlisp-types` alone keeps.
  - [x] `(require 'termlisp-load)` alone loads prelude successfully — pinned by
    a fresh-image subprocess test (`tl-load-standalone-typechecks-the-prelude`),
    red before the require landed (dies of `Unknown symbol: seq`), green after.
- [ ] **P3-5 `tl-dpo-normalize` production-dead** — decided by F2 below: if kind
  normalization adopts it, it gains a production caller; otherwise document it as
  the entry point for callers needing the reduction graph.  Closed by F5.

## 表二：System Fω 推进（F2 即 `tl-dpo-last-gluing` 的消费者）

- [x] **F1 kind 保持性检查器** — kind mirror of `tl-preserve-check`: freeze open
  type variables of type-level rules as kind metavariables, normalize both sides
  at the kind level, compare; refuse when kinds do not match.
  - [x] kind-oracle over the type-level rule set: preserved / violated /
    cannot-check buckets.
  - [x] Tests pin at least one violating rule as a refusal.

  `tl-kind-preserve-check` (termlisp-kinds.el) takes the same three verdicts,
  the same clause loop, and the same unread guard as the value checker, but
  reads both sides of a rule as types: one dynamic `tl-type-parse-vars`
  binding spans both parses, so each variable of the rule is one node whose
  kind slot the left side fills and the right side reads — that is the
  freeze.  Graph sides write their variables `$name', which a type parser
  would take for constructor leaves, so the `$' is dropped on the way in.
  The two sides fail differently and the verdicts say so: an unknown head
  takes a fresh kind variable where value inference refuses a name, so a
  reduct that fails to kind proves a clash between the two sides and is
  `violated', while a pattern that fails to kind is `cannot-check'.  The
  whnf-aware `tl-kind-unify' carries the final comparison, and its clash —
  or the reduct's kind error — is the reason string on a refusal.

  The oracle pins one finding about the prelude.  The value checker cannot
  decide the class-method family at all, no scheme covering a dict-taking
  pattern, while the kind side can see them and refuses all twelve: the
  pattern lifts a method out of its dictionary, and the dictionary
  constructor has already said what came out is a value (its fields are
  types, so the lifted kind asks for `univ' of their types), which no
  application can consume — the reduct `(add a b)' does not kind.  Both
  refusal paths are pinned directly as well: a reduct at another kind
  (`(List $a) -> Zero') and a reduct that mistakes a type for a value
  (`(List $a) -> (Cons $a $a)').  Type-level `rewrite' is not gated here;
  F2 hangs the gate on this checker.
- [x] **F2 类型层 `rewrite`/`reduce` 落地，门控于 F1 + 局部性** — the
  `tl-dpo-last-gluing` consumer: kind-level normalization runs through
  `tl-dpo-normalize` and `tl-dpo--step-gluing`; the checker reads
  `tl-dpo-last-gluing` and refuses on any non-nil verdict (dangling / cross-rule
  escape), because a kind cannot be re-generalized the way a value can.
  - [x] Non-nil gluing type-level rule rejected with `termlisp-type-error`.
  - [x] Nil gluing passes unchanged.

  The gate hangs in `tl-rewrite-desugar`, after the value verdict.  Every
  clause that reaches it is already readable by the type layer
  (`tl-nbe--make-rule` refuses the ones that are not), which means every
  admitted rewrite can be unfolded inside a type — so F1's
  `tl-kind-preserve-check` is asked of every `rewrite`, not only of some
  marked type-level subset, and an ordinary value clause passes it the
  same way the oracle's family does not.  Then the locality trial: the
  rule's own pattern (the target as written, a term for a clause the type
  layer can read) is built into a graph and normalized with this one rule
  under `tl-dpo-normalize`, which runs every cut through
  `tl-dpo--step-gluing` and writes the first non-local verdict to
  `tl-dpo-last-gluing`.  A redex at the root has no holder outside the
  match, so refusals come from the walk finding what a root cut alone
  cannot: `identification` (a pattern whose two positions would reach one
  host node) and `dangling` (the reduct rewriting itself again under a
  holder it does not own).  Both are records at the value level —
  `tl-reduce-term` still only records, and the slot it documents now also
  carries the trial's verdict, nil included — and refusals here.  A walk
  that runs out of `tl-rewrite--trial-fuel` is the rule not settling at
  its own redex, refused with that wording.  All three refusals are
  `termlisp-type-error` raised before the clause list is touched.
  P3-5's question — whether kind-level normalization adopts
  `tl-dpo-normalize` as a production caller — is answered yes here;
  closing the checkbox stays with F5.  Pinned by four tests in
  `rewrite-form-test` (kinds, identification, dangling, and the nil slot
  after an accepted rewrite); suite 474/474.
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
