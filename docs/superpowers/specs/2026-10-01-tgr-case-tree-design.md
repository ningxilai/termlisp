# TGR: Idris-style clause compilation to case trees

Date: 2026-10-01
Status: proposed

## Motivation

The graph rewriter's rule matching currently uses an ad-hoc pattern language
(`$var`, `(:rest $xs)`, `(:splice $xs)`) plus *function templates* to cope with
variadic keywords. This is not elegant: variadic/repeatable matching is bolted
on, and quoted-data opacity is a special case.

Idris2 (`/home/iris/.pack/clones/Idris2`, `src/Core/Case/CaseTree.idr`,
`src/Core/Case/CaseBuilder.idr`) shows the canonical solution: multi-argument,
multi-clause pattern matching is **compiled to a decision tree**.

## Idris's model (reference)

- `Pat`: `PAs`, `PCon name tag arity subpats`, `PTyCon`, `PConst c`,
  `PArrow`, `PDelay`, `PLoc`, `PUnmatchable`. A proper pattern AST, not markers.
- `CaseTree`: A-normal form; only variables are scrutinised.
  - `Case idx isVar scTy alts` — dispatch on the variable at column `idx`.
  - `STerm clauseId term` — right-hand side.
  - `Unmatched msg` / `Impossible`.
- `CaseAlt`: `ConCase name tag args tree`, `DelayCase`, `ConstCase c tree`,
  `DefaultCase tree`.
- `CaseBuilder`: `NamedPats` = patterns still to process, in column order;
  `partition` splits clauses by the constructor/constant in the current column;
  `Group`/`checkGroupMatch` build the alternatives; recursion yields the tree.
  This is Wadler/Augustsson "compiling pattern matching to good decision trees".

Key ideas worth adopting:
1. Patterns are a **data type** (`Pat`), with a catch-all (`DefaultCase`) and
   as-patterns (`PAs`) — no ad-hoc `:rest`/`:splice`.
2. Matching is **column-wise**: a set of clauses over `(head arg1 ... argN)` is
   compiled once into a decision tree; each node scrutinises one position.
3. A rule *set* (all clauses for a symbol) is compiled together, so overlaps and
   defaults are handled uniformly and first-match semantics are explicit.
4. Variadic/repeatable forms are handled by **structural patterns over the
   argument list** (cons/nil patterns) — a list is just data, matched by the
   same machinery, not by a special "rest" marker.

## Proposed design for the TGR

### Pattern AST

```
Pat ::= (pvar NAME)                 ; bind a subterm
      | (pwild)                     ; match anything, bind nothing
      | (plit VALUE)                ; literal equality
      | (pcon HEAD PAT...)          ; constructor / application with arity
      | (pas NAME PAT)              ; bind the whole while matching PAT
      | (plist PAT...)              ; proper-list pattern (cons/nil sugar)
      | (pnil)                      ; empty list
```

`(pcon HEAD PAT...)` matches a node whose head is `HEAD` and whose children
match `PAT...`; a nullary `(pcon HEAD)` matches the atom `HEAD`. Lists are
`(pcon cons (pvar h) (pvar t))` / `(pnil)`; `(plist p1 p2 ...)` is sugar.

### Clause and rule set

A **clause** is `(PATTERN . TEMPLATE)` where `PATTERN` matches the whole term
`(head args...)` and `TEMPLATE` is a sexp built from `(pvar)` bindings (plus a
`splice` for lists, which is just the template counterpart of a list binding).

A symbol's rules are a **list of clauses** (first match wins). A single
`tl-grule` becomes a symbol with one clause; variadic keywords become a symbol
with clauses whose patterns use `plist`.

### Compilation

`tl-case-compile (clauses)` → a `tl-case-tree`:

- `tl-ct-case (column alts)` — scrutinise position `column` (0 = head, 1.. = args).
- `tl-ct-leaf (clause-index bindings)` — a matched RHS.
- `tl-ct-fail` — no clause matches (used for non-exhaustive symbols).

Alternatives:
- `tl-ct-con (head arity subtree)` — the value at the column is `(head a1..aN)`.
- `tl-ct-const (value subtree)` — a literal atom.
- `tl-ct-default subtree` — variable/wildcard column.

Compilation mirrors `CaseBuilder`: for the leftmost column that is not all
variables, partition clauses by the constructor/const at that column, keeping a
`default` group for variable/wildcard patterns; recurse. `PAs` bind at the leaf.

### Matching

`tl-case-match (tree node bindings)` walks the tree: at a `case` node, force the
column's subterm (already WHNF in the graph), dispatch on its head/arity/const,
recurse; at a leaf, instantiate the template with the accumulated bindings
(including list bindings for variadic clauses).

### Opacity

`quote`/`function` subterms remain opaque (a `tl-graph-opaque-heads` property of
the *constructor table*, not a rewrite special case): the case matcher simply
never descends into them, and templates never rebuild them.

## Migration

- Replace `(:rest)`/`(:splice)`/function-templates in `tl-grule` with the clause
  list + case tree.
- Port `setup-rules` to clauses: fixed keywords become single clauses; repeatable
  keywords (e.g. `:hooks H1 F1 H2 F2 ...`, `:commands (C...)`) become clauses
  using `plist` over the argument list, with a template that maps over the bound
  list (the template language needs a `map`/`splice` over a list binding).
- Keep the current public `tl-graph-rewrite-sexp` interface; the case tree is an
  internal compilation of the rule set.

## Non-goals

Full dependent pattern matching (Idris's `PTyCon`, `PDelay`, coverage checking),
and the elaborator's unification. We only adopt the clause→case-tree *compilation*
and the `Pat` AST.
