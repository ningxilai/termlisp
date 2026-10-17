# TODO

Work archive for the post-Stage-2 round.  Every node starts unchecked; a node is
ticked only when its listed acceptance criteria hold on a committed tree with the
standing gates green (`make compile` 0 warnings, `make test`, checkdoc multiset zero
new, `parsecheck.sh` OK, every library file byte-compiling clean on its own).
Status values: `[ ]` not started, `[~]` in progress, `[x]` done.

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

- [x] **P2-6 `.tls' 首行 magic string 写的是 `emacs-lisp`** — `termlisp--magic-string'
  named the mode a `.tls' file opens in `emacs-lisp', which is how the file is
  read rather than what it is written in.  It now says `mode: scheme', the bundled
  `termlisp-prelude.tls''s first line says the same, and `termlisp-load''s
  commentary follows.  The prelude had to move with the constant:
  `termlisp--ensure-magic-string' *inserts* when the head does not match, so a
  constant that moved alone would have rewritten the installed copy of the
  prelude in place on its first load.  `load' ignores the file-local part either
  way, so the line chooses the buffer's mode and nothing else.
  - [x] Two tests pin the pair: `tl-magic-string-opens-a-tls-file-in-scheme-mode'
    (red before -- the string said `emacs-lisp'), and
    `tl-prelude-ships-the-current-magic-string' (red on either half moving alone).

- [x] **P2-7 `Not registering prefix ":"' printed on every build** — the line is
  Emacs's `loaddefs-generate--make-prefixes' declining to register a
  one-character prefix and naming the definition it dropped; elpaca runs that
  generator over this package whenever it builds it, so every build printed it.  A
  prefix exists to fetch a file whose definitions are not loaded yet, and
  `termlisp-load.el' already told the reader in its commentary that these names
  must be required before they are met -- so the file now says the same to the
  generator, through a file-local `autoload-compute-prefixes: nil' after the
  `ends here' line, documented beside the WARNING it belongs to.  The warning went
  with the prefixes it was about; the other 25 registrations are untouched.
  - [x] `loaddefs-generate' over this tree prints no prefix warning.

- [x] **P1-8 Native compilation found nine warnings the standing gate could not
  see** — native compilation byte-compiles one file per fresh process, where only
  that file's own `require's are loaded; `make compile' compiles all 27 in one
  image, in which `termlisp-load' has already required `termlisp-eval' -- and eval
  has required `termlisp-kinds' -- before `termlisp-nbe' and `termlisp-types' are
  reached.  Compiled alone, types.el did not know `tl-karr', `tl-kind-freshen',
  `tl-kind-whnf', `tl-kind-unify' or `tl-kind->string', nor the variable
  `tl-kind-star', and nbe.el did not know the two `tl-clause' accessors; the
  ninth was `tl-type-lenient', read in `tl-infer-application' 174 lines before its
  own `defvar'.  `declare-function' now names kinds' five beside the eval ones
  already declared there, `tl-kind-star' is declared beside them, and nbe declares
  the two accessors -- kinds and eval both require these files back, so a `require'
  was never available, and the `fboundp' guards at every call, which are what
  keeps a host that loaded `termlisp-types' alone from calling into a kind module
  it never loaded, stay exactly as they were.  The free variable was ordering
  inside one file, so the two oracle flags moved up beside `tl-infer-constraints'
  with the other inference flags.
  - [x] `tl-types-and-nbe-compile-alone-without-warnings' compiles both files in
    fresh Emacsen of their own, in a staging directory of symlinks so no `.elc'
    reaches the source tree; red before the declarations (the nine warnings are
    what the report carried), green after.
  - [x] All 27 library files byte-compile clean when each is compiled alone;
    suite 495/495, `make compile` clean with 27 .elc, checkdoc 366 = 366 with an
    empty normalized diff against `3500d66`, parsecheck OK (37 files).

- [x] **P1-9 `termlisp-repl' typed `(' and got `(('** — electric-pair asks the
  syntax table what the partner of a character is, through `matching-paren',
  which reads the match that `modify-syntax-entry' records as a descriptor's
  second character -- and the REPL's table gave the paren characters classes
  only.  With no recorded partner the answer for `(' was nil, and the fallback
  at the end of `electric-pair-syntax-info' pairs a character with itself, so a
  session with `electric-pair-mode' on inserted a second open paren after the
  one typed.  That mode is global -- it is toggled on from `prog-mode-hook' and
  off again from the lisp hooks by the config that runs termlisp -- while
  `termlisp-repl-mode' derives from `comint-mode', then `fundamental-mode', and
  runs neither hook, so the buffer inherited whichever state the session had
  last set.  Closers never showed it: electric-pair steps over a closer that
  already stands next to point instead of pairing, which is why only the left
  side was reported.  The descriptors now carry their partners the way
  `lisp-mode''s spell `()" and `")("', so `matching-paren' answers for all six
  characters the table treats as parens.
  - [x] Two tests pin it: `tl-repl-syntax-table-names-each-paren-s-partner'
    covers every character of the table, and
    `tl-repl-electric-pair-closes-the-paren-it-just-opened' types one `(' at a
    real REPL prompt — red before (the buffer ended `(('), green after (`()').

- [x] **P1-10 `termlisp-repl' held its own copy of the interpreter driver** —
  `termlisp-repl--eval-string' re-did `termlisp-eval''s whole batch wiring
  (the four `tl-infer-forward-*' bindings, the evaluation loop,
  `tl-forward--link') and then added on top the three lines a front end needs
  -- `tl-run-post-batch', the drop of a queue a failure left behind, and the
  rendered answer -- because `termlisp-eval' returns a raw value and leaves
  the coverage queue to whoever drove it; `tl-test--coverage' carried a
  second copy of those same three lines for that same reason.  The shape
  Geiser draws and IELM already draws is one evaluation API with a front end
  that only formats, so the bookkeeping now lives in one place:
  `termlisp--eval-forms' holds the batch wiring that `termlisp-eval' and the
  new `termlisp-eval-submission' both call, and the submission driver is
  what a front end drives -- STRING parsed as one unit, every form
  evaluated, forward names linked, the coverage check run once the
  submission succeeded, a queue a failure left behind dropped rather than
  reported at the next one, and the answer printed.  The reader gained the
  front end's only other question, `termlisp-read-complete-p', which used to
  be `termlisp-repl--complete-p' reaching into the reader's private
  `termlisp--skip-trivia' from the repl file.  `termlisp-repl.el' now holds
  no interpreter wiring at all -- `termlisp-repl--send' calls the API and
  `termlisp-repl-return' calls the reader -- and `tl-test--coverage' drives
  that same API, so the REPL, the test harness and any future front end
  share one driver.
  - [x] The two coverage tests now drive `termlisp-eval-submission' with an
    explicit environment instead of `let'-binding `termlisp-repl--env', and
    still pin what the prompt shows
    (`tl-ch-cov-repl-reports-per-submission',
    `tl-ch-cov-repl-drops-a-failed-submission').
  - [x] Two new pins: `tl-read-complete-p-says-when-input-may-be-sent'
    (unfinished / finished / comment-only / lone closer) and
    `tl-eval-submission-with-no-forms-returns-nil' — red before (both
    functions did not exist), green after.
  - [x] README documents both functions in the API list, its
    `tl-run-post-batch' caller line now names the three functions that
    actually call it (`termlisp-eval-submission', `termlisp-load',
    `termlisp-typecheck-def' — the line had said `tl-typecheck-def', which
    names no function), and the REPL section says which side of that API the
    buffer sits on.
  - [x] Suite 499/499, `make compile` 0 warnings with 27 .elc, isolated
    per-file compile clean, checkdoc 366 = 366 with an empty normalized diff
    against `0efdeb8', parsecheck OK (37 files), `loaddefs-generate' prints
    no prefix warning (25 registrations).

- [x] **P1-11 The reader guarded `read-eval', which never existed** —
  `termlisp-parse' and `termlisp-read-complete-p' both carried
  `(when (boundp 'read-eval) ...)' with a comment claiming the variable
  "was removed in Emacs 32 ... on older Emacsen it defaults to t", and the
  commentary and two README passages repeated the story -- but there has
  never been a `read-eval' variable in Emacs: `git log -S' over
  `src/lread.c' finds the string in zero revisions, NEWS never mentions
  it, and the only substring hits in all of Emacs are edebug's
  `edebug-install-read-eval-functions', which advises `load-read-function'
  and `eval-defun' and shares nothing with a reader switch.  `#.' never
  needed one either: the dispatch on the character after the hash has no
  `.' case, so `#.' has been invalid read syntax all along -- Emacs 32
  signals `invalid-read-syntax', and the string `"#."' is absent from
  lread.c's history too.  The guard was therefore dead on every version it
  claimed to protect: it could not have fired once, and the trust boundary
  it purported to hold is held by the grammar itself.  The guard and its
  comment are gone from both functions, the commentary now says read-time
  evaluation needs no switch (and no longer lists `#1=' labels among the
  things the reader accepts, the contradiction the README had been
  documenting in a parenthetical -- that parenthetical is gone too, with
  the contradiction fixed at the source), and the README's trust-boundary
  paragraph and reporting checklist are rewritten against what the reader
  actually does.  The rest of the sweep is clean: every other `boundp' /
  `fboundp' guard in the tree tests for something real, and the
  `read-circle' half of the trust boundary is true as written (nil rejects
  finite and circular `#1=' labels alike, verified).
  - [x] `tl-reader-cannot-evaluate-at-read-time' pins the boundary the old
    comment claimed to hold: `termlisp-parse' rejects `#.' with a parse
    error and `termlisp-read-complete-p' sends it to evaluation like any
    other read error.  Green before and after, as the defect was a false
    comment and dead code, which no behavior test could see; the red was
    in `git log', not in ERT.
  - [x] Suite 500/500, `make compile` 0 warnings with 27 .elc, isolated
    per-file compile clean, checkdoc 366 = 366 with an empty normalized diff
    against `72defcc', parsecheck OK (37 files), `loaddefs-generate' prints
    no prefix warning (25 registrations).

- [x] **P1-12 Eight operators typechecked, then rendered back as
  themselves** — `quo', `mod', `cl-gcd', `^', `zero?', `even?',
  `odd?' and `neq' each carried a type scheme in `termlisp-ir-types'
  and no runtime: under `:type-check', `(quo 7 2)' passed the checker
  and then answered `(quo 7 2)' -- a stuck form, arithmetic that
  fails by being silent.  The schemes came from the emit path, which
  compiles these names to elisp (`truncate', `mod', `cl-gcd',
  `zerop', `expt', `neq' inlined as `(not (equal a b))'); plain
  term-lisp evaluation never had the other half.  Each now has a
  runtime in `termlisp-builtins' spelled the way `tl-emit' inlines
  it, so the two paths cannot drift, and `quo'/`mod' divide by zero
  the way `/' has always reported it.  Three more names existed
  nowhere -- `floor', `ceiling', `round' -- kept as primitives for
  parity, not impossibility: the emitter's fallback already lands on
  elisp's own of these names, so the interpreter binds the same
  functions, exact at the float/bignum boundary and at the
  half-to-even rule `round' inherits.  An impossibility claim would
  have been wrong twice over -- `quo' had just opened the door,
  `(quo x 1)' truncating a float to an integer, and over it a floor
  is one sign-adjustment while a half-to-even round is a
  reconstruction; both were compared against the primitives on an
  18-float battery (positive and negative whole, half and fractional
  values, signed zero, ten-digit scale), every one equal, and the
  floor spelling is pinned in the suite beside the two `(quo x 1)'
  facts it rests on.
  With them and the eight, the prelude gains the Arithmetic section
  the baseline library was missing: `abs', `signum', `min', `max',
  `positive?', `negative?', `square', `sum', `product',
  `gcd'/`lcm' over `cl-gcd', and the partner both division families
  needed -- `quo' pairs with `rem', cutting toward zero, `mod' with
  `div', which did not exist at all, flooring.  The section pins its
  own claim at the value level: each pair rebuilds -7 from b = 2, so
  the difference between cutting and flooring is observable rather
  than asserted.
  The bar was `~/aldor--.hs' -- the Haskell sketch of an Aldor
  interpreter's AST -- with the prelude as its base library, and the
  transcription tests separate the two halves honestly: the six
  mutually recursive trees (`FB', `DefTable', `DTE', `Expr', `Value',
  `Type', in the .hs file's own order, the `DefTable' constructor
  keeping its datatype's name, `QName = [String]' as `(List String)'),
  the `BuiltInOp' closure field carrying `(-> (List Value) Value)',
  the nested match back out and the forward-referencing defines were
  already there -- symbolic capability needed no round; the
  interpreter's arithmetic did, and `value-quo' over `IntegerVal' is
  where the two halves meet.  `factorial 20' and `(^ 2 100)' pin the
  arbitrary-width Integer an interpreter's `IntegerVal' must have.
  `factorial' ended up a primitive because the suite insisted: the
  locality trial over the prelude's clauses
  (`tl-rewrite-locality-trials-the-prelude-rules') refuses an
  accumulator loop over Integers -- a pattern with only variable
  positions matches its own recursive call under the `if' that guards
  it, and the cut reaching outside the redex is dangling.  Every
  recursive clause the prelude did ship escapes the trial the same
  way, its recursive call violating the constructor its own pattern
  demands; with the loop in elisp at the mathematical base (0! = 1),
  the prelude still carries no exceptions.
  - [x] Deliberately untouched: `ListFirst', `ListRest', `ListEmpty'
    and `tl-output-char', `tl-output-<<', `tl-format' also typecheck
    without runtimes, but they are emit-pipeline internals -- the
    first three always inlined before evaluation, the last three
    elisp functions the emitted program calls -- and a runtime behind
    them would promise source an entry surface that is not its own.
  - [x] Red/green: 44 of the 48 new pins fail at the round's parent
    `f7549e1' with the tests kept; the four that pass are the purely
    symbolic transcriptions, which is the capability that already
    existed.  All 48 green with the round applied.
  - [x] Suite 548/548, `make compile` 0 warnings with 27 .elc, isolated
    per-file compile clean, checkdoc 366 = 366 with an empty normalized
    diff against `f7549e1', parsecheck OK (37 files), `loaddefs-generate'
    prints no prefix warning (25 registrations).
- [x] **P1-13 The `cats` dependency went with its module, and the bigfloat
  became a first-class tower member** -- two chores the calc plan owed.
  On the dependency: `termlisp-data-reader.el' had zero callers and zero
  tests, was the only consumer of `cats', and -- by requiring it at load
  -- made `(require 'termlisp)' fail on any machine without it, so the
  module was deleted outright and `cats' left `Package-Requires';
  termlisp now names only Emacs itself and still loads Calc lazily
  (proven: `featurep' is nil after load and after a native fast-path
  add, and only the first tower operation pulls Calc in).  The
  Makefile's `CATS_DIR' block and the comment above it are now stale,
  and stay: the no-touch rule on the Makefile outranks cosmetics.
  On the tower: Emacs 32's Calc is bigfloat-only -- an elisp float is
  not a Calc number (`math-float 0.5' dies of `listp') -- so `Float'
  lands as Calc's `(float MANT EXPT)' beside `frac' and `cplx', and
  every entry point runs inside `tl-calc-pure', one macro pinning all
  five session variables (chatter off, radians, exact preferred,
  symbolic off, precision) so a tower operation is a function of its
  arguments alone.  The first draft of that macro was wrong in a way
  only the suite could tell: it re-read the precision from a *sibling*
  binding of the same `let' (`(let ((p ...)) ... (or p ...))'), and
  Emacs `let' binds in parallel, so every init form saw the unbound
  gensym -- all tower paths died of a void variable the moment they ran
  and the byte compiler warned `reference to free variable' at each
  call site; the override now lives in `calc-internal-prec''s own init,
  where the name reads the enclosing dynamic value.  A second quiet
  lie: `infinitep', which Emacs 32 does not have, now `= 1.0e+INF'.
  `tl-bigfloat (x prec)' takes an integer, double, fraction or
  bigfloat at a chosen precision: doubles enter exactly through their
  finite decimal expansion (`%.1769e' prints it; 0.1 at 25 digits is
  `0.1000000000000000055511151'), fractions divide at prec, and
  normalisation strips trailing zeros so equal values are `equal'
  whatever precision built them.  The bigfloat owns its printed form
  (`tl-bigfloat->string', exact, leading zero included) through a
  printer hook both renderers consult -- whose first spelling was
  Common Lisp's `cond' `=>' clause, which elisp's `cond' does not
  have, so the renderer died on a void `=>' exactly when a printer
  matched; it is a `let'-hoisted cond now.  The order is `tl-num-less?'
  (`tl-num-less-p'): native `<' when both sides are native, else both
  sides to exact fractions, because Calc's own mixed comparison calls
  equal values unequal (`math-equal' of 0.1 and 1/10 is nil on Emacs
  32) -- so 1/3 is placed exactly between its two neighbouring
  12-digit bigfloats, and the same double at precisions 5 and 25
  compares as the two decimals it then is.  Complex numbers signal:
  the tower has no order for them.  `<'/`>' are deliberately untouched
  -- Aldor's `<` belongs to OrderedSet, not to every numeric type, so
  the prelude's `min'/`positive?' stay native-number operations and
  the tower order is its own builtin.  `tl-fraction' hardened to
  integer operands, `tl-complex' converts double parts through the
  bridge, and the dead `math-big-p' branch went (not fbound on Emacs
  32).  Every empirical claim in the docstrings was re-measured after
  this round's output-corruption episode rather than carried over.
  - [x] Red/green: the 14 new pins (5 elisp-level in aldor-test.el, 9
    source-level under `:type-check t' in prelude-test.el) all fail at
    this round's parent `b08a732' with the tests kept -- the source
    pins through the checker's unknown-symbol path, the elisp pins
    through void function -- and all 14 are green with the round
    applied, with the 548 old tests green on both sides.
  - [x] Suite 562/562, `make compile` 0 warnings (26 .elc for 26 .el,
    the deleted module accounted for), checkdoc 179 = 179 with an
    empty normalized diff against `b08a732' (test/ included, the
    deleted file's 4 messages excluded from the base), parsecheck OK
    (36 files, was 37), `loaddefs-generate' prints no prefix warning
    (24 registrations; the sole diff against the base loaddefs is the
    deleted file's prefix entry).

- [x] **P1-14 The category tower landed: `Monoid`, `Foldable`,
  `Traversable` and `lift-a2`** -- cats pulled locally
  (`~/.config/emacs/elpaca/sources/emacs-cats`) and its protocol
  surface compared face by face before writing anything.  The design,
  each piece pinned by a probe first: `Monoid' is dictionaries only --
  `mempty' is a value in the record rather than a function, so its
  three verbs take the dictionary explicitly and work in phase B, and
  `string-append' is redefined through `string-join' under a signature
  (elisp owns the bare name).  `Foldable' is a class: its `foldr'
  scheme applies only the class parameter itself, which is what the
  parse wall in `tl-type-head' lets through, and `to-list', `length'
  and `fold-map' are three-line derivations over it; the old List-only
  `length'/`foldr' are gone, so default-mode callers pass
  `FoldableListDict' or switch `:elaborate' on (the two old pins got
  the option, their renders unchanged).  `Traversable' is dictionaries
  only -- a method scheme may not apply a free scheme variable in
  argument position, where it parses as a rigid constructor and the
  call site then refuses every dictionary -- with `traverse'/`mapm'
  accessors and `sequence-a'/`sequence' on top; `maybe-traverse' goes
  through the `lift' field so its pure appears at one type in both
  clauses (the helper-split alternative died on the
  monomorphic-across-clauses wall for bare parameters).  `lift-a2'
  joins the `Applicative' class under an infix `(a -> b -> c)' scheme
  with a third dictionary field, and every lift implementation
  uncurries the binary function itself: a partially applied
  multi-parameter lambda silently filled its missing arguments with nil
  at runtime (the S0 family, fixed in P1-15), and `fmap' feeds one
  element at a time --
  traverse passes plain binary lambdas across the field boundary and
  the implementation does the wrapping.  `asks' and `local' arrive in
  the raw `reader-fmap' style the reader's transparent function type
  lives in.
  - [x] What cats ships that this round did not take, and why:
    `cats-find' -- a convenience over `to-list' whose early exit a
    strict `foldr' cannot express, and a First-style monoid was one
    abstraction too far for this round; the ziplist datatype and its
    applicative -- data, not protocol, nothing in the engine blocks
    it; the Maybe extraction helpers `cats-just'/`cats-maybe'; the
    State runners `eval-state'/`exec-state'/`run-state'/
    `state-modify' -- a state is a plain function here, run by
    applying and read by taking the `Pair'; `cats-seq' -- `do' and
    `bind' say the same thing, and the prelude's `seq' builtin is
    strict sequencing, a different animal; elisp-vector instances --
    termlisp has no vector type to stand for one.  `cats-partial'
    cannot be ported honestly at all: partial application is the
    runtime wall above, which is also why cats composes its own
    `lift-a2' through `cats-partial' while the prelude uncurries
    instead.  Either gets no instances on either side -- cats ships
    none either, and the compound constructor cannot stand in
    class-parameter position here.
  - [x] **New finding: the whole-file inference and the submission
    inference diverge.**  The same `state-lift-a2' body, submitted
    alone, infers the sound threading; loaded as part of the prelude
    file it comes out with `mx' unconstrained and the result `s -> ?'
    carrying no `Pair'.  The value preserve oracle caught it on the
    spot ("Cannot apply state-ap to mx") -- the round's only genuine
    `violated' verdict -- and an explicit signature pins what the body
    implements (verdict `preserved', scheme sound on both paths).  The
    batch-generalization divergence itself is left to the engine.
  - [x] Two pre-existing walls confirmed while probing, recorded not
    fixed: an applied type variable cannot unify with an arrow, so the
    elided-dictionary `lift-a2' call cannot take State/Reader
    arguments (their values are functions) -- the implementation-level
    pins call `state-lift-a2'/`reader-lift-a2' directly; and a
    successful elaboration zonks a dictionary value's stored type, so
    the stock `monad-return MaybeDict' refuses its second type in the
    same env -- probes and tests stay on the fresh-env-per-evaluation
    model the suite already uses.
  - [x] Oracle pins moved with the prelude and nothing was pinned
    away: kind-violated 12 -> 30 in three shapes the reasons report
    verbatim (a pattern variable declared a value and applied; a
    constructor application where a proper type is required -- both
    `Cons'-folding rules; the lift implementations' uncurrying lambda,
    which has function kind), value-cannot 8 -> 13 (the dict-taking
    patterns plus the two `Foldable'-constrained derived verbs), and
    the docstrings rewritten to describe exactly the families the
    checkers report.  `length' is the one asymmetry the new text
    names: the kind side reads its reduct as a type that kinds.
  - [x] Red/green: with the tests kept and only the prelude reverted
    to `7a84068', 45 of the 49 selector-matched tower and oracle tests
    fail; the three that pass are wall-pins whose rejection is
    unchanged behaviour (`foldr'/`length' refusing a non-container,
    `(length Nil)' answering 0 on the old implementation too).
  - [x] Gates: suite 608/608 (46 new pins, two old pins switched to
    `:elaborate t'), `make compile' 0 warnings and every library file
    clean in isolation, checkdoc identical normalized multiset against
    a fresh `7a84068' worktree, parsecheck OK, `loaddefs-generate'
    prints no prefix warning.

- [x] **P1-15 The runtime now matches the curried arrows: an
  under-applied function is a value, and `Ziplist' joins the
  applicative family** -- the S0 family, named in the engine rather
  than worked around in the prelude.  `tl-bind-params' walked the
  parameter list binding as it went, so a multi-parameter lambda
  applied to fewer arguments filled the gaps with thunks over nil --
  `((lambda (x y) (Cons x y)) 1)' answered `(Cons 1 nil)' while the
  checker, which types the lambda as a right-nested arrow, had
  accepted the program -- and surplus arguments were dropped the same
  way in reverse, while a named function refused a short call
  outright (`No matching clause') because `tl-match-seq' matches at
  exact arity.  The fix is currying end to end: a `tl-partial'
  machine value records the callee and the argument thunks supplied
  so far -- thunks, so each argument keeps the environment it was
  written in -- and the next application appends to them and
  continues where the call stopped, a partial of a partial flattening
  by construction.  The application core (`tl-apply-thunks' over
  `tl-apply-clauses') answers `(BODY ENV SURPLUS)': a closure binds
  its parameters to the leading thunks and hands the rest back, the
  call sites push an `apply' continuation frame, and when the body's
  value arrives the frame applies it to the surplus -- which is how a
  nested `(lambda (x) (lambda (y) ...))' applied flat consumes its
  trailing arguments instead of dropping them, and how a zero-arity
  clause applied to anything still runs and gets its result applied.
  Clause arity counts the parameters less any trailing `:list' rest
  pattern, which still absorbs the whole supply; the pending
  threshold is the smallest arity among the clauses and the surplus
  split the largest, so a mixed-arity clause set dispatches the way
  the exact matcher always did.  A class-method call missing its
  elaborated dictionary -- `(fmap f x)' in phase B -- now waits for
  it as a pending application instead of failing clause selection,
  uniform with everything else, and `:type-check t' still names the
  real error.  `Ziplist' takes the cats omission P1-14 recorded: a
  list wrapper whose `pure' delivers one element and whose `ap' pairs
  element-wise, truncating at the shortest side -- the eager ziplist
  keeps the identity law only on one-element ziplists, cats itself
  accepting the deviation, and termlisp has no infinite lists to
  stand in -- with Functor, Applicative and Foldable instances as
  cats gives the type, and no Traversable because cats has none.
  - [x] The lift implementations keep their one-call wrappers and
    only the comment that justified them changes: the S0 workaround
    was retired, but a fixed-arity builtin has no curried form --
    `(+ 1)' refuses with `+ expects 2 arguments, got 1' rather than
    answering a pending application -- so `(+ x y)' in one call is
    what makes `lift-a2 +' work at all (pinned through the ziplist
    lift), while defined functions and constructors answer a pending
    application like everything else (`(cons 1)' and
    `(string-append "a")' are `#<partial>').
  - [x] `ziplist-lift-a2' carries the family's wrapper and a
    signature, the second after `state-lift-a2': loaded whole-file
    its inferred scheme lost the element threading -- five
    quantifiers with `mx' and the result detached from `f', probed
    against `maybe-lift-a2' which infers the sound three -- exactly
    the divergence the state lift documents, and the value oracle
    caught it (`Cannot apply ziplist-ap to mx') before the signature
    pinned the threading the body implements.
  - [x] Oracles moved with the prelude and nothing pinned away:
    kind-violated 30 -> 33, the three new reducts falling into the
    families the docstrings already describe (`ziplist-ap-step'
    applies the `f' its `(Cons f fs)' pattern bound,
    `ziplist-lift-a2' joins the uncurrying wrappers, `ziplist-pure'
    folds with `Ziplist' where the reading wants a `*');
    preserve-cannot unchanged at 13; preserve-violated 0.
  - [x] Tests: 29 new pins -- 19 application, 9 ziplist, the
    dictionary-waiting pin -- every rendering probed, none
    hand-computed; `tl-test-sub' joins test-support for the
    define-then-call shape the single-form macros cannot express.
  - [x] Red/green: with the tests kept and the engine, machine and
    prelude reverted to `2d38cdc', 24 of the 29 round-matched pins
    fail; the five that pass are behaviour-unchanged pins (exact and
    zero-argument lambda application, the two `:list'-clause pins
    whose rest binding still absorbs the supply, and
    `((adder1 1) 2)', whose inner call was already exact).
  - [x] Gates: suite 637/637, `make compile' 0 warnings and every
    library file clean in isolation, checkdoc normalized multiset
    against a fresh `2d38cdc' worktree identical but for one fewer
    warning (the old `tl-apply-step' docstring never named
    CALLER-ENV; the rewrite does), parsecheck OK,
    `loaddefs-generate' prints no prefix warning (24 registrations).

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
  pinned by name and count).  `make compile` starts with `rm -f *.elc`.  Two
  checks P1-8 added to these, because one batch image cannot see what a fresh
  process sees: every library file byte-compiles clean when it is compiled alone
  (`emacs -Q --batch -L . -f batch-byte-compile FILE`, one file per process, no
  output) -- that is the condition native compilation meets -- and
  `loaddefs-generate` over the tree prints no prefix warning.
