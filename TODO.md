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
- [x] **P3-5 `tl-dpo-normalize` production-dead** — decided by F2 below: if kind
  normalization adopts it, it gains a production caller; otherwise document it as
  the entry point for callers needing the reduction graph.  Closed by F5.

  Closed as adopted, so the fallback — a side-entry documentation page for a
  dead function — never applies.  `tl-dpo-normalize` carries three production
  callers and the standing suite exercises all three.  The type-level normal form
  `tl-nbe-nf` unfolds through it, which is the reduction behind definitional
  equality `tl-nbe-equal`; `tl-reduce-term` reads its value-level unfolding off
  the same entry; and the locality trial `tl-rewrite--locality` — a kind-level
  question, the one F2 named — runs each rule's own pattern through it.  None is
  a test-only shim: the first is the type checker's normal form, so a rewrite the
  gate accepts is reduced through `tl-dpo-normalize` on every later type
  comparison.  The kind oracle, in F1's node, buckets the same rule set
  this normalization carries.

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
  after an accepted rewrite); suite 474/474.  The identification pin is
  reversed by F6 below, which withdraws that condition from the gate.
- [x] **F3 prelude 获得类型层规则** — e.g. `Vec` arithmetic, type-level `+`,
  every rule through the F1+F2 gate.
  - [x] Every prelude type-level rule lands in its oracle bucket.

  The prelude gains `vappend`, whose codomain's index is the type-level
  `plus` of its two argument indices.  Both clauses reduce inside the
  signature at definition time — `(plus Zero m)` to `m`, `(plus (Succ n) m)`
  to `(Succ (plus n m))` — and both are readable by the type layer, so the
  rule joins the rule set as an ordinary member.  It lands `preserved` in
  both oracles, and both oracle tests now also assert it by name: a rule
  whose clauses stopped being type-readable would leave `tl-nbe--rules`
  entirely, which every count they already pin would pass over silently.
  Four cases in `curry-howard-test` pin it end to end — appending, an
  annotation accepted at a `Zero` head and at a `Succ` head (the two
  reductions), and a codomain that claims the first index while the second
  is one past its head's, refused with the signature's own wording.

  The gate's locality half ran over the prelude's own rules: every clause
  rebuilt as the term it spells, tried through `tl-rewrite--locality`, nil
  everywhere but one rule.  `and` and `or` were written as a truth table
  whose pattern repeated a constructor, and a repeat is identification —
  two positions reaching one host node; both are reformulated to decide
  one position in the pattern and pass the other through, the same table
  without a repeat, which the truth tables `prelude-test` already pins
  answer unchanged.  `trans` cannot be written that way: both `Refl`
  patterns are load-bearing, each collapsing one equation of the
  signature's `x y z` chain so that the body `Refl` proves `(Eq a x z)`.
  It is recorded instead under its reason in `rewrite-form-test--folded`,
  and the trial pins the exemption both ways — a folded rule must still
  come back flagged, and the clause count must reach past the rule count
  so that a rule which stopped being type-readable cannot slip out of the
  trial either.  A user rewrite that repeats a subterm it does not need
  is refused as before.  F6 below withdraws the identification condition
  itself, so the reformulated `and` and `or` stay only because they are
  the smaller table, the exemption list is deleted, and a
  repeated-subterm rewrite is admitted rather than refused.

  `vappend` also found the value checker without its evaluator: the batch
  driver and the evaluator both bind `tl-nbe-reduce-env` around the
  comparisons they make, and `tl-preserve-check` did not, so its
  structural comparison called the rule violated for returning exactly
  the index its signature computes — a verdict that depended on who was
  asking.  The check now binds it while typing both sides, the same
  reduction every checked program runs under, and says so in its
  docstring.  Pinned by the prelude locality trial, the two oracle
  presence assertions and four `vappend` cases; suite 479/479.
- [x] **F4 Fω 表达力测试** — higher-kinded polymorphism (`Functor` at `* -> *`),
  type-level lambda application, kind inference on open terms, NBE equality
  under type binders; end-to-end Fω samples with higher-kinded instances.

  The round opened on a spelling: `->` written as a kind had never worked.
  `tl-kind-parse` walked the operator itself among the operands, so
  `(-> * *)` parsed as an arrow whose first domain was a universe named
  `->`, and `(f : (-> * *))` — datatype parameter or class parameter
  alike — was refused at its first use while `(karr * *)` went through.
  With the operator skipped, a parameter ranges over type constructors:
  `(datatype (Box (f : (-> * *)) a) (MkBox (f a)))` admits
  `(Box Maybe Int)` and refuses `(Box Int Int)` naming the argument, and
  a class parameter may now carry `(NAME : KIND)`, measured at each
  instance's own declaration — the `Int` instance refused, the `Maybe`
  instance resolving through its dictionary to its answer.  A parameter
  written any other way is a named error instead of being read as two
  extra parameters.

  A lambda in application position now parses to the same node a
  standalone lambda does, so `((lambda (n) (Succ n)) Zero)` reaches the
  checker as a term it can reduce rather than as a raw sexp, and
  `tl-nbe--whnf` consults a node head only for beta — a fallback that
  returned that head instead of the application had leaked bare heads
  into every result it could not reduce.  Rigidity learned the same
  lesson from the other side: a Pi binder's variable refuses to be
  bound but no longer refuses to be looked at first, so
  `(plus Zero n)` reduces to the binder's own `n` and the two
  `(n : Nat) -> Vec Nat …` types are one with an environment in reach
  and two without, structural checking unchanged in between.

  Open terms take the kind their head says — `(Succ n)` is a `Nat` —
  and a head nothing registered leaves a kind variable each use decides,
  which is what lets a clause be kinded before anything has named its
  arguments.  Thirteen cases pin the round, ten in `curry-howard-test`
  and three in `prelude-test`: the `Box` datatype both ways, an applied
  type-level lambda unifying and computing an index inside a signature,
  its kind meeting the arrow spelling, class instances both ways with
  the bare parameter spelling refused, and binder equality with and
  without an environment.  Suite 492/492, 0 byte-compile warnings,
  checkdoc 366 = 366 with an empty normalized diff against `a2f138d`,
  parsecheck OK (37 files).
- [x] **F5 文档与门收口** — README Fω section; kind-oracle joins the standing
  gates; P3-5 closes here.

  The README gains a `System Fω` section documenting what F1–F4 built: an
  arrow-kind parameter, a type-level `lambda` and its application, and the
  kind-level gate every type-level rule passes before it is written.  Writing it
  found a documentation defect that had stood since the Kinds section was first
  written.  That section claimed arrows are spelled `K1 -> K2` and showed
  `(datatype (T (a : * -> *)) ...)`, but a kind is read as `(-> K1 K2)` — `->` in
  head position, right-associative — and `* -> *` reads as `(* -> *)`, which
  `tl-kind-parse` has always refused as `Bad kind`.  Only the prefix spelling was
  ever real: F4 had already made `(-> * *)` parse correctly, and the README's
  infix example was simply never true.  The Kinds section is corrected to
  `(-> K1 K2)` / `(karr K1 K2)` and the Fω section is written against the
  spellings the tests pin — `Box`'s annotated parameter, the
  `(lambda (a) (Vec a Zero))` of kind `(* -> *)`, and the computed index
  `(Vec Int ((lambda (n) (Succ n)) Zero))`.

  The kind oracle joins the standing gates: the prelude bucketing test is
  named in the Notes alongside compile/test/checkdoc/parsecheck,
  `tl-kind-preserve-oracle-buckets-the-prelude-rules`, and it already
  asserts every prelude rule lands in exactly one bucket — `preserved`,
  `violated`, or `cannot-check` — with the `violated` family pinned by name
  and count and `vappend`'s presence asked directly, so a rule that stopped
  being type-readable cannot slip out of the count.  P3-5 closes
  as adopted: `tl-dpo-normalize` is not production-dead, carrying `tl-nbe-nf`,
  `tl-reduce-term`, and the locality trial as callers, so it needs no side-entry
  page.

  The `trans` exemption is left as it stands and its rationale is not weakened
  here.  The locality trial reports `identification` for `trans` because its
  pattern spells `Refl` at two positions that hash-cons to one node — the same
  shape as the user rewrite `(f (MkG a) (MkG a)) -> (MkG a)` that F2 deliberately
  pins as refused.  No structural criterion separates the two: both share a node
  outside the interface, both leave a reduct that is a copy rather than the shared
  node itself, and neither dangles in the isolated trial graph.  So truly clearing
  the exemption would mean accepting the F2-pinned refusal too, which is a change
  to a safety property the suite pins, not a documentation-round tidy-up.  It stays
  a name-based carve-out, recorded in `rewrite-form-test--folded`, and any move to
  make it structural belongs in its own round with that trade-off stated.  F6 below
  takes that round.  Suite 492/492, 0 byte-compile warnings, checkdoc 0 new,
  parsecheck OK.

- [x] **F6 局部性判决收口** — the locality condition becomes containment alone:
  `identification` leaves `tl-dpo-gluing`, the `trans` exemption is deleted, and
  F2's pin of `(f (MkG a) (MkG a)) -> (MkG a)` as refused is reversed into an
  admission.
  - [x] Every prelude clause returns nil from the trial, with no exemption list
    to carry.
  - [x] The dangling and kinds refusals are untouched.

  F5 left the `trans` exemption a name-based carve-out and said the structural
  move belongs in its own round with the trade-off stated; this is that round,
  taken with sign-off on the trade-off.  The two cases were never separable —
  `trans` and the user rewrite `(f (MkG a) (MkG a)) -> (MkG a)` share a node
  outside the interface, both leave a reduct that is a copy rather than the
  shared node, and neither dangles in the isolated trial graph — so the choice
  was refusing both or admitting both, and it is admission, because
  identification was never a locality question.  The step is SPO:
  `tl-spo-apply` cuts the matched image and glues the template, so a step is
  local exactly when nothing outside the match observes the cut, which is the
  dangling condition and only that.  Two positions reaching one host node is a
  failure of the DPO pushout complement — it would have to cut one coincident
  image and keep the other — and SPO has no complement to fail; it folds the
  positions, and a fold wholly inside the redex cannot be seen from outside.
  A fold whose node is held outside leaks, which is the dangling case still
  asked.

  The condition had to leave `tl-dpo-gluing` rather than be filtered by the
  trial: `tl-dpo-normalize` records the first non-nil verdict the walk takes,
  so a walk finding identification at one step and dangling at a later one
  would have named the first and hidden the second behind it.  `dangling` alone
  is what the slot can ever hold now.

  The match's `positions` slot existed only to answer the removed condition,
  so it goes with it — both matchers keep the image, and the repeat
  special-case in each `one` simplifies to `take` then `bind`, which `take`'s
  memq guard already made right on a repeat.  What the value level records is
  unchanged in kind: `tl-reduce-term` never refused, and it simply never sees
  identification in the slot; nothing read it there.

  The suite says so in both directions.  `trans` passes with nil and
  `rewrite-form-test--folded` is deleted: the prelude trial
  `tl-rewrite-locality-trials-the-prelude-rules` now demands nil for every
  prelude clause with no exceptions to carry.  The F2 pin flips:
  `(rewrite (f (MkG a) (MkG a)) (MkG a))` is admitted, pinned by
  `tl-rewrite-form-admits-a-pattern-that-repeats-a-subterm`, and that
  reversal of a safety property F2 recorded as deliberate is exactly the
  trade-off F5 named.  What was never in question stays pinned:
  `(rewrite (f (Succ x)) (Succ (f (Succ x))))` still refuses dangling, the
  kinds refusal is untouched, and the gluing unit test that used to report
  `identification` for `(f a a)` now asserts nil on the same graph.  The
  prelude's `and`/`or` comment, which claimed the trial reports a repeated
  constructor, is corrected with it.  F2's node above describes the
  two-verdict gate as built; this node is its correction.  Suite 492/492, 0
  byte-compile warnings, checkdoc 0 new, parsecheck OK.

## Notes

- P0-1 (the recursion crash) was scheduled before F1 because kind-preservation
  verification of type-level rules meets the same self-reference unfolding; it
  is fixed, so F1 inherits the cycle guard for free.
- Standing gates: 0 byte-compile warnings, checkdoc multiset zero new vs the base
  regenerated from HEAD, parsecheck OK, full ert suite green, and the kind oracle
  `tl-kind-preserve-oracle-buckets-the-prelude-rules` (every prelude type-level
  rule bucketed `preserved` / `violated` / `cannot-check`, the `violated` family
  pinned by name and count).  `make compile` starts with `rm -f *.elc`.
