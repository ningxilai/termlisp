> Disclaimer: This project is at an early stage, many things may not work.

# term-lisp

<!--toc:start-->
- [term-lisp](#term-lisp)
  - [Design charter](#design-charter)
    - [One term representation](#one-term-representation)
    - [What that buys the language](#what-that-buys-the-language)
    - [What it costs](#what-it-costs)
    - [How far elisp can carry it](#how-far-elisp-can-carry-it)
  - [Syntax](#syntax)
    - [Literals and the reader](#literals-and-the-reader)
    - [Top-level forms](#top-level-forms)
    - [Patterns](#patterns)
    - [Types](#types)
    - [Kinds](#kinds)
    - [Options](#options)
  - [Using the library](#using-the-library)
  - [Debugging](#debugging)
    - [The REPL](#the-repl)
    - [The error model](#the-error-model)
    - [What the messages look like](#what-the-messages-look-like)
    - [Diagnostic knobs](#diagnostic-knobs)
    - [Holes](#holes)
    - [Inspecting values and types](#inspecting-values-and-types)
    - [A working order](#a-working-order)
    - [Writing a minimal repro](#writing-a-minimal-repro)
  - [Extending termlisp from Emacs Lisp](#extending-termlisp-from-emacs-lisp)
    - [A builtin and its type](#a-builtin-and-its-type)
    - [Rewrite rules](#rewrite-rules)
    - [Hooking reduction](#hooking-reduction)
    - [The environment](#the-environment)
    - [Batch hooks](#batch-hooks)
  - [Metaprogramming](#metaprogramming)
    - [Reading, building, evaluating](#reading-building-evaluating)
    - [Emitting Emacs Lisp](#emitting-emacs-lisp)
    - [The Aldor front end](#the-aldor-front-end)
    - [I/O](#io)
  - [Reporting bugs](#reporting-bugs)
  - [Project layout](#project-layout)
    - [Branches](#branches)
    - [Dependencies](#dependencies)
  - [Development](#development)
  - [Scope](#scope)
  - [License](#license)
<!--toc:end-->

term-lisp is a language for *term* *lis*t *p*rocessing with first-class
pattern matching, lazy evaluation, tail-call optimization, static types,
type classes, and monads. It is implemented in Emacs Lisp as an embedded
library — no external runtime, no build step, and one optional dependency.

It is also an experiment: how much of a real language can be built on top
of elisp, and where does elisp stop being able to carry it?

## Design charter

### One term representation

The whole design rests on a single decision, recorded in
`DECISION-unified-term-graph.md`: **everything that is a term is a
`tl-node`, and there is no second representation anywhere.** Terms, types
and kinds all live in one graph.

That decision is forced before it is chosen. A type must be allowed to
contain terms — `Vec a n` indexes by a term `n`, `(n : Nat) -> Vec a n -> a`
binds one, `Vec a (n + m)` contains one that must still reduce. So every
term that can appear in a type needs a representation already picked, and
picking anything else means writing traversal, substitution, alpha
equivalence and reduction twice, once for terms and once for types.

`tl-node` is built for both jobs at once. It carries two disjoint groups of
slots (`termlisp-graph.el`):

| purpose | slots |
|---|---|
| unification (union-find) | `var` `bind` `rank` `kind` |
| reduction (rewriting / NbE) | `state` `memo` |

One struct serves two subsystems, so the unifier and the normaliser share
the graph instead of translating between two copies of it. The reducer was
already written on nodes before the decision was made, so taking it cost no
second implementation.

The structural invariant that follows is worth knowing when reading the
code: a type constructor's head has exactly one spelling, so head lookups
always go through `tl-gnode--head` rather than reading the slot directly.

### What that buys the language

Because unification and reduction share the graph, a signature's `plus n m`
can unfold *while its type is being compared with another*. That single
property is what makes indexed families work at all:

```lisp
(datatype (Vec a n)
  (VNil : (Vec a Zero))
  (VCons a (Vec a n) : (Vec a (Succ n))))
```

`Vec : * -> Nat -> *`, and `Vec Int String` is rejected at the declaration
rather than left as a case somebody forgot to rule out. The same idea
carries into the propositional layer as `(datatype (Eq a) (Refl : (Eq a)))`.

### What it costs

Two things, both accepted rather than solved:

- The type layer needs its own evaluator running over nodes. There is no
  cheap path from "the typechecker wants to compare two types" back to a
  term-level result.
- NbE performance on elisp has never been benchmarked. Normalisation is
  exact, and exactness is not free.

### How far elisp can carry it

The boundary the project is probing, concretely:

- Hindley–Milner inference, dictionary-passing type classes, kind inference
  with dependent kinds, and exhaustiveness checking — all in elisp.
- An explicit CEK machine with memoized thunks, so forcing a
  variable-bound thunk and function application are both tail steps. Deep
  tail recursion does not grow the Emacs stack.
- Unification by union-find over the same nodes the evaluator rewrites.
- An Aldor front end compiling down to elisp, with self tail calls turned
  into loops.
- About 12,000 lines of elisp, byte-compiling clean on Emacs 27.1 and
  later, with a single optional dependency.

## Syntax

### Literals and the reader

Top-level forms are ordinary S-expressions read with the **Emacs Lisp
reader**, so elisp literal syntax carries over: integers, floats, strings,
character literals such as `?a` and `?\n`, and symbols. Comments run from
`;` to end of line.

The reader accepts the full elisp reader grammar — vectors, records, `#1=`
labels and so on. It is intended for **trusted** term-lisp source, not
arbitrary untrusted input. Circular `#1=` structures are rejected by
binding `read-circle` to nil, and read-time evaluation is disabled on
Emacsen where `read-eval` is bound.

One consequence is worth stating plainly: `?0` is a character literal, not
a symbol. You cannot write a type variable called `?N`, and the test suite
renames such variables for exactly that reason.

### Top-level forms

The evaluator dispatches top-level forms in `tl-eval-top`
(`termlisp-eval.el:511`):

| form | meaning |
|---|---|
| `(define x VALUE)` | define a value |
| `(define (f PATTERN...) BODY...)` | define a function as a list of patterns and a body |
| `(datatype open NAME (Ctor TYPE...) ...)` | declare a datatype |
| `(datatype (NAME PARAM...) (Ctor TYPE...) ...)` | declare a parameterised datatype |
| `(datatype-extension NAME (Ctor TYPE...) ...)` | add constructors to an open datatype |
| `(: name TYPE)` | declare a signature for the next `define` |
| `(do ...)` | desugared to `bind`/`return` before anything else runs |
| anything else | evaluated as an expression |

`class` and `instance` are handled one layer up, in `tl-elaborate-form`
(`termlisp-elaborate.el:186-187`), and so are constrained `define`s. They
are the forms that need `:elaborate` on.

A definition is *a list of patterns plus a body*, not a lambda applied to
patterns. There is no separate `match` form:

```lisp
(datatype Bool (True) (False))
(define (if (True) a b) a)
(define (if (False) a b) b)
```

A datatype may declare `open`, in which case constructors can be added
later and pattern matches are never considered exhaustive — a failed match
is a runtime error:

```lisp
(datatype open Expr (Lit Int))
(datatype-extension Expr (Add Expr Expr))
```

A constructor may declare its own result type after `:`, which is how the
indices above become part of the type rather than something the caller
keeps straight. Ordinary datatypes are untouched by any of this:
`(datatype Maybe (Nothing) (Just a))` still infers `Just : ∀a. a -> Maybe a`.

### Patterns

`tl-pattern-parse` (`termlisp-pattern.el:55`) turns a surface pattern into
a compiled one:

| surface | compiled | meaning |
|---|---|---|
| `_` | `(wild)` | match anything, bind nothing |
| `x` | `(var . x)` | bind `x` |
| `(:literal EXPR)` | `(lit EXPR)` | compare with the value of `EXPR` |
| `(:dot EXPR)` | `(dot EXPR)` | same value test, and say what it means |
| `(Ctor P...)` | `(con ...)` | destructure a constructor |
| `(:list NAME)` | `(rest . NAME)` | bind the remaining sequence elements |
| `(:lambda NAME)` | `(lam . NAME)` | bind a function value |
| `(guard PAT EXPR)` | | `PAT` must match *and* `EXPR` must be `True` |
| `(or P...)` / `(and P...)` | | alternatives, or conjunction |

A bare symbol is a variable — unless it names a nullary constructor in
constructor position, in which case it is that constructor. Repeating a
variable inside one pattern is a *constraint*, not a shadow: both
occurrences must bind equal values.

```lisp
(define (car (Pair a b)) a)          ; destructuring
(define (is-zero (:literal 0)) True) ; value matching
(define (list (:list rest)) rest)    ; remaining arguments
(define (map a (:lambda fun)) (fun a)) ; passing a function
```

**Dot patterns** are the Idris2-style form, and they exist for the type
checker rather than for the evaluator. `lit` and `dot` run the identical
value check — evaluate the expression in the definition's scope and
compare it with the value on offer — but a literal is a constant the
checker *cannot enumerate*, whereas a dot is the programmer telling the
checker what stands at a position a constructor pattern could not name:

```lisp
(define (f (:dot (plus n m))) ...)  ; only when the argument is already
                                    ; `plus n m' reduced
(define (g (:dot k))) ...)          ; only when the argument is the value
                                    ; of `k' -- a bare `k' would bind it
```

The compiled tag is `dot`, but the surface spelling carries the colon,
like `:literal`, `:list` and `:lambda`. Writing `(dot (plus n m))` makes
`dot` a constructor name and fails with `Unknown constructor in pattern:
dot`.

At the value level it constrains nothing a literal would not. What it buys
is at the type level: `tl-clause--pattern-term` hands the checker the term
itself, so the codomain can reduce under it the way it reduces under a
constructor. Without the dot there is no way to say "assume this position
is that term" — the alternative is to bind it and hope.

### Types

Arrow types may be written infix or prefix; the parser splits on every `->`
in the type, so `(-> Int Bool)` and `(Int -> Bool)` are the same type, and
both are curried.

```lisp
(: not-void (Void -> Void))
(define (not-void v) v)            ; ¬⊥
```

Type application is `(List Int)` or `(Vec a n)`. Literals are legal in type
position — `Vec a 3` indexes by a number — as are type-level `lambda` and
an explicit `Pi`.

Type classes use dictionary passing:

```lisp
(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))
(instance (Functor Maybe) FunctorMaybeDict)
;; (fmap (lambda (x) (+ x 1)) (Just 4)) => (Just 5)
```

Types are propositions and programs are proofs, so the prelude carries the
constructive connectives:

| Proposition   | Type                              |
|---------------|-----------------------------------|
| truth `⊤`     | `Unit`                            |
| falsehood `⊥` | `Void` — declares no constructors |
| conjunction   | `(Pair a b)`                      |
| disjunction   | `(Either a b)` — `Left`, `Right`  |
| implication   | `a -> b`                          |
| negation `¬a` | `a -> Void`                       |

`absurd : ∀a. Void -> a` is `⊥`-elimination. It can never run, because
`Void` has no constructors; reaching it at all means `:type-check` was off,
and it signals rather than answering a value.

### Kinds

Kinds are nodes too (`termlisp-kinds.el`), so kind unification reuses the
graph unifier. `*` is the kind of proper types and arrows are written
`->`. Two kinds go past that:

- `univ(T)` is the kind of the *values* of `T`. `Zero : Nat` because it is
  a `Nat`, and the universe leaf is what says which datatype a value came
  from. This is the level shift `DataKinds` needs and a plain `*` cannot say.
- `Π(x : k1).  k2` binds a parameter so that `k2` may mention it: `(x : (univ a))`
  states that `x` comes out of `a`, which is the dependency `Eq` needs and
  three independent kind variables cannot say.

A datatype parameter's kind is written in the declaration's own scope:

```lisp
(datatype (Eq (a : *) (x : (univ a)) (y : (univ a))) (Refl : (Eq a x x)))
```

So `Int : *`, `List : * -> *`, `Vec : * -> Nat -> *`, `Fin : Nat -> *`, and
`Eq : Π(a : *).  univ(a) -> univ(a) -> *`. A lifted constructor's argument
kind is `univ` of its field's type: `Succ : Nat -> Nat` as before, but
`VCons : univ(a) -> univ((Vec a n)) -> Vec`.

That is what makes `Vec Int String` a kind error at the declaration instead
of a case somebody forgot to rule out.

```lisp
(: v (Vec Int String))            ; rejected: Kind error
(: v (Vec Int (Succ Zero)))
(define v (VCons 1 VNil))         ; => (VCons 1 VNil)

(define (vhd (VCons x xs)) x)     ; the index unifies with the scrutinee
(vhd (VCons 7 VNil))              ; => 7
(vhd VNil)                        ; rejected: its index is Zero
```

### Options

`termlisp-make-env` takes a plist merged over `termlisp-default-options`
(`termlisp-base.el:40`):

| option | default | effect |
|---|---|---|
| `:type-check` | `nil` | typecheck each top-level form before evaluating it (`datatype` forms are exempt) |
| `:elaborate` | `nil` | type-directed elaboration; inserts class dictionaries and handles `class`/`instance` |
| `:coverage` | unset | check exhaustiveness after a batch of definitions |
| `:occurs-check` | `nil` | occurs check during elaboration |
| `:fuel` | `100000` | evaluator fuel; exhaustion signals `fuel exhausted` |
| `:phase` | `B` | which rewrite-rule phase to apply |

`:type-check` and `:elaborate` are the two that change behaviour for
ordinary programs. `:elaborate` subsumes typechecking — when it is on, it
runs instead of the plain checker.

Numeric literals are inferred `Int` regardless of their runtime
representation, so `sin`/`cos`/`tan`/`exp`/`log`/`sqrt` are typed
`Int -> Int`. The exact numeric tower (`tl-fraction`, `tl-complex`,
`tl-num-*`) is polymorphic underneath.

Variadic `list` has no fixed arity to express as a curried arrow, so it is
expanded to nested `Cons` applications in both the evaluator and the type
checker — the same trick Coalton uses for `make`/`make-list`. It therefore
acquires a type at each call site, and `Cons` enforces homogeneity:

```lisp
(list 1 2 3)         ; (List Int)
(list 1 True)        ; Cannot apply Cons to (Cons True Nil)
```

## Using the library

```elisp
(require 'termlisp)
```

API:

- `termlisp-make-env` — create an environment from a plist (see Options).
- `termlisp-parse` / `termlisp-parse-file` — read a string / file into a
  list of S-expressions.
- `termlisp-eval` / `termlisp-eval-file` / `termlisp-eval-form` — parse and
  evaluate a string / file / already-read form.
- `termlisp-typecheck` / `termlisp-typecheck-file` — typecheck without
  evaluating; returns the environment and signals on error.
- `termlisp-load` / `termlisp-load-prelude` — load a `.tls` file / the
  bundled prelude into an environment.
- `termlisp-value->string` — render a value.
- Builtins — the primitive functions term-lisp code can call: `eq`, `+`, `-`,
  `*`, `/`, `<`, `<=`, `>`, `>=`, `sin`, `cos`, `tan`, `exp`, `log`, `sqrt`,
  `absurd`, `seq`, `first`, `rest`, `empty?`, `list`, `format`, `print`,
  `read-line`, `stdin`, `string-join`, `string->list`, `list->string`.

The prelude defines the booleans, pairs, `Either`/`Void`, lists, `Nat`,
`Vec`, `Fin`, `Eq`, monads and type classes, together with the operators
`=`, `xor`, `null?`, `map`, `foldl`, `reverse` and `sort`.

Example:

```elisp
(let ((env (termlisp-load-prelude (termlisp-make-env '(:elaborate t)))))
  (termlisp-value->string
   (termlisp-eval "(fmap (lambda (x) (+ x 1)) (Just 4))" env)))
;; => "(Just 5)"
```

## Debugging

### The REPL

`M-x termlisp-repl` opens a comint buffer with a `λ>` prompt. Input is
evaluated in the running Emacs, so definitions made at the prompt stay for
the rest of the session. The environment starts from
`termlisp-repl-options` (`:type-check` on by default) and, unless
`termlisp-repl-load-prelude` is nil, the prelude is loaded into it.

- `RET` sends the input when it reads as a sequence of complete top-level
  forms; an unfinished form moves to the next line and is indented, so a
  form can be typed across several lines without an escape character.
- `C-j` inserts a newline without evaluating.
- `C-c C-t` toggles `:type-check` for the current environment.
- `C-c C-k` discards every definition and loads a fresh environment.
- `M-p`, `M-n`, `M-r` and `C-c C-o` are comint's usual history and
  clear-buffer bindings.
- An input of `exit` (or `quit`) closes the REPL.

Errors are printed in the buffer as `error: ...` and the REPL keeps
running, so the session survives a bad form. Four defcustoms shape it:
`termlisp-repl-buffer-name`, `termlisp-repl-prompt`,
`termlisp-repl-options` and `termlisp-repl-load-prelude`.

### The error model

Every error the package signals is documented as deriving from
`termlisp-error`, so a caller can catch the whole family with one
`condition-case`, or just the phase it cares about:

```
error
 └─ termlisp-error                     base
     ├─ termlisp-parse-error           termlisp-reader
     ├─ termlisp-type-error            termlisp-types, termlisp-kinds,
     │                                 termlisp-ir-types, termlisp-exhaust,
     │                                 termlisp-io, termlisp-builtins
     ├─ termlisp-eval-error            termlisp-eval, termlisp-numeric,
     │                                 termlisp-graph
     ├─ termlisp-abn-error             termlisp-abn
     ├─ termlisp-aldor-error           termlisp-aldor
     └─ termlisp-emit-error            termlisp-emit
```

There is one exception, and it is the one you will hit first:
`termlisp-hole` is defined with no parent, so it derives from `error`
directly and **a `(termlisp-error …)` handler will not catch it**. Catch
it separately:

```elisp
(condition-case err
    (termlisp-eval "(+ 1 True)" env)
  (termlisp-error (message "%s" (cadr err)))
  (termlisp-hole  (message "unsolved goals: %S" (cadr err))))
```

Errors are signalled with a one-element list holding the message, so the
message of a caught condition is its `cadr`. Anything that carries
structured data puts it in the remaining list elements — a hole carries
its goal lines there.

### What the messages look like

Every message below was produced by running the form in the third column
— either live, or by the test suite that asserts it. They are the whole
debugging surface, so it is worth knowing what they look like before one
appears.

| phase | message | what you typed |
|---|---|---|
| types | `Cannot apply + to True` | `(+ 1 True)` |
| types | `Cannot apply Cons to (Cons True Nil)` | `(list 1 True)` |
| types | `Cannot apply vhd to VNil` | `(define (vhd (VCons x xs)) x)` then `(vhd VNil)` |
| types | `Cannot apply absurd` | `(absurd 1)` |
| types | `Unknown symbol: nosuch` | `(nosuch 1)` |
| types | `Unknown constructor in pattern: Nope` | `(define (f (Nope x)) x)` |
| types | `Guard expression is not Bool` | `(define (f (guard x 1)) x)` |
| types | `Clause of f does not match its signature` | `(: f (Nat -> Nat))` then `(define (f x) True)` |
| types | `Definition of g does not match its signature` | `(: g (Either Int String))` then `(define (g) (Just 1))` |
| types | `inconsistent type` | two clauses of one function returning different types |
| types | `Malformed arrow type: (-> Int)` | an arrow with nothing to its right |
| types | `is not a proper type` | `(: r (Eq Int))` — `Eq` wants three arguments |
| kinds | `Kind error: Vec argument 2 is a * where a Nat is required` | `(: v (Vec Int String))` |
| kinds | `Bad kind: ...` | a malformed kind annotation |
| eval | `fuel exhausted` | a looping rewrite, or `:fuel` set too low |
| eval | `Cannot extend non-open datatype Bool` | `(datatype-extension Bool (Meh))` |
| eval | `Division by zero` | `(/ 1 0)` |
| eval | `do block must end with (return e)` | a `do` whose last step is not `(return …)` |
| eval | `<<loop>> detected while forcing a thunk` | a thunk that forces itself |
| builtins | `+ expects 2 arguments, got 3` | wrong arity on a primitive |

Some messages carry more than one line. A signature mismatch prints the
two types it could not reconcile:

```
Clause of f does not match its signature
  the signature says: (-> Nat Nat)
  this clause gives:  (-> Nat Bool)
```

Coverage messages name the case that is missing, which is the useful
part — `no case for VNil`, `no case for (Cons _ Nil)`,
`no case for (PProgram (DGlobal _) _)` — alongside `clause 3 is
unreachable` and `coverage undecidable here`. If the coverage checker
runs out of budget it says so rather than lying: `Coverage: fuel
exhausted after 10 steps`, with the budget in `tl-exh-fuel`.

Kind *rendering* uses the same spellings as the source: `univ(a)`,
`Π(a : *).  univ(a) -> univ(a) -> *`, `(k1 -> k2)`.

### Diagnostic knobs

- `:type-check` / `:elaborate` — turn the checker on. Most wrong programs
  fail here rather than at runtime, and this is the first thing to reach for.
- `:coverage` — checks exhaustiveness *after* a batch of definitions,
  because a function's clauses may be spread over several `define` forms.
  The bundled `if` is written that way, and checking after each clause
  would report a half-written function as incomplete.
- `:fuel` (default `100000`) — bounds evaluation. Exhaustion is
  `fuel exhausted`, which usually means a rewrite rule loops rather than
  that the number is too small.
- `tl-exh-fuel` (default `8192`) — the same backstop for the coverage
  checker. It is a global, not an option.
- `tl-coverage-announcements` — the queue of definitions waiting to be
  checked. `termlisp-load-prelude` binds it to nil, so the bundled library's
  deliberate partial functions are never reported.

There is no stepper or trace for the evaluator or the rewriter. The
diagnostics are the type checker, the coverage checker, and fuel.

### Holes

`_` in expression position is a hole, and it is the most useful debugging
tool the language has. A hole types as a fresh variable, but the context
still constrains it, so asking for the goal tells you what the compiler
already decided:

```lisp
(+ 1 _)      ; leaves a hole the context has decided is a number
```

What comes back is exactly that decision:

```
Unsolved goal: ("hole 1 : Int")
```

A form left with holes is not something to run: there is no value to
produce. Instead the goals are reported — which is what the REPL is for —
and a batch caller sees the same thing as a `termlisp-hole` condition
carrying one display line per hole.

### Inspecting values and types

- `termlisp-value->string` renders a runtime value, forcing thunks.
- `termlisp-typecheck` returns the environment, so after a successful call
  the inferred scheme is in `tl-env-type-env`.
- `tl-type-to-datum` turns a type node into a plain datum you can `equal`
  against. Its `?N` variable numbering follows traversal order, which is an
  implementation detail; the test suite renames them to `%1`, `%2`, … in
  first-appearance order before asserting, which is the stable spelling.

Note that the two printers disagree, deliberately. The same list renders
as `(Cons Zero (Cons (Succ Zero) Nil))` from `termlisp-value->string` and
as `[Zero,(Succ Zero)]` from `(format "~a" …)` — the first is elisp-shaped
and shows the runtime representation, the second is Aldor-shaped and
shows the language's own view of a list.

### A working order

Given a program that does not do what you want:

1. Turn `:type-check` on if it is off. A surprising share of "wrong answer"
   reports are ill-typed programs that were allowed to run.
2. Turn `:coverage` on if the program pattern-matches. An unaccounted case
   is named explicitly, e.g. `no case for PEnd`.
3. Put a `_` where you are unsure and read the goal.
4. If it typechecks and still misbehaves, check whether a rewrite loops —
   `fuel exhausted` or `<<loop>> detected` are the signatures of that.
5. Re-run the same form in a fresh environment (`C-c C-k` in the REPL). A
   definition leaking in from an earlier experiment is a common cause.

### Writing a minimal repro

The test suite's own macros are the shortest path to one, and they show the
shape a report should take (`test/test-support.el`):

```elisp
(tl-test-eval tl-some-name "(fmap (lambda (x) (+ x 1)) (Just 4))" "(Just 5)"
              '(:elaborate t))
(tl-test-reject tl-other-name "(list 1 True)" "Cannot apply"
                '(:type-check t :elaborate t))
(tl-test-covers tl-third-name "(define (f (Zero)) True)" '(:coverage t))
```

Each runs in a **fresh** prelude environment built from the given options,
so nothing leaks between cases. That isolation is exactly what makes a
minimal repro minimal: if you can name the option plist and the form, you
have a report.

## Extending termlisp from Emacs Lisp

### A builtin and its type

Adding a primitive takes two registrations, and they have to agree.

```elisp
(tl-register-builtin '+
  (lambda (args) (tl-check-numbers args '+) (+ (nth 0 args) (nth 1 args))))
```

`tl-register-builtin (name fn)` puts `fn` in `tl-builtins`. `fn` receives
the argument list with every argument already forced to weak head normal
form by the driver. Raise `termlisp-type-error` for bad input, using one of
the helpers — `tl-check-one-arg`, `tl-check-one-number`, `tl-check-numbers`:

```elisp
(tl-check-numbers args '+)
;; "+ expects 2 arguments, got 3"
;; "+ expects numbers, got True"
```

The type is a separate registration, and without it the typechecker knows
nothing about the builtin:

```elisp
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type
   'eq (tl-tscheme (list a) (tl-tarrow a (tl-tarrow a (tl-tbool))))))
```

`tl-register-builtin-type (name scheme)` puts `scheme` in
`tl-builtin-types`. Two steps is deliberate: the runtime table and the type
table are read by different layers, and keeping them separate lets a host
override one without the other.

### Rewrite rules

Two constructors, both building a `tl-grule`:

```elisp
(tl-make-grule NAME PHASE PRIORITY PATTERN TEMPLATE &optional GUARD CLAUSES)
(tl-make-crule NAME PHASE PRIORITY CLAUSES &optional GUARD)
```

- A **pattern/template** rule matches `PATTERN` and rebuilds the node from
  `TEMPLATE`.
- A **clause-based** rule takes `CLAUSES` as `(PATTERN . TEMPLATE)` pairs,
  whose patterns come from `tl-pat-parse` in `termlisp-case`. The clauses
  are compiled into a decision tree once and dispatched through it, so
  variadic rules can be written with list patterns and `(prest NAME)`.

`PHASE` selects which rules apply — `tl-graph--rules-for` filters by phase
— and `PRIORITY` orders those that do, ascending. An optional `GUARD`
further constrains a rule.

### Hooking reduction

`tl-graph-whnf` (`termlisp-graph.el:60`) is a `defvar` holding a function
of one node returning its weak head normal form, or nil. A host that
reduces *while it matches* binds it. The type layer cannot tell that
`plus Zero n` is a `Succ` without reducing it first, so a clause guard or a
literal comparison cannot decide without the host's normaliser:

```elisp
(let ((tl-graph-whnf (lambda (arg) (tl-nbe-whnf arg nbe))))
  ...)
```

That binding is exactly how `termlisp-nbe.el` plugs its normaliser into
`termlisp-case` and into the rewriter.

### The environment

`tl-env` is a plain struct whose slots a caller can read and write:

| slot | holds |
|---|---|
| `functions`, `clauses` | defined functions and their clause lists |
| `datatypes`, `constructors` | datatype declarations and their constructors |
| `type-env`, `sig-env`, `kind-env` | inferred schemes, declared signatures, kinds |
| `class-env`, `instance-env`, `method-env` | type classes and their dictionaries |
| `globals` | global bindings |
| `options` | the option plist |
| `current` | a linked environment, if any |

`tl-env-option (env key &optional default)` is the accessor to use rather
than reading the plist directly.

### Batch hooks

Coverage runs later than typechecking, and does not want the typechecker to
depend on it. Two globals bridge the gap:

- `tl-coverage-announcements` — each `(ENV NAME TYPE)` pushed as a `define`
  finishes typechecking.
- `tl-post-batch-hook` — called once with the accumulated list; this is
  where the coverage layer is reached.
- `tl-run-post-batch` — runs the hook over the queue and clears it, so an
  error in the hook cannot leave a stale definition queued for the next
  batch.

## Metaprogramming

### Reading, building, evaluating

The public API is enough to write a termlisp front end of your own. The
full loop — generate source from elisp, parse it, walk it, evaluate it,
inspect the result:

```elisp
(require 'termlisp)

(defun my/tl-inc-n (name n)
  "Return termlisp source defining NAME as N nested increments of x."
  (let ((body 'x))
    (dotimes (_ n) (setq body (list '+ body 1)))
    (format "(define (%s x) %s)" name body)))

(let* ((env (termlisp-load-prelude (termlisp-make-env '(:type-check t))))
       ;; 1. Generate source.  This is ordinary elisp string building.
       (src (mapconcat (lambda (n) (my/tl-inc-n (format "inc%d" n) n))
                       '(1 2 3) " "))
       ;; 2. Parse.  `forms' is a list of ordinary elisp data, so walk,
       ;;    rewrite, or build it with any tool you like.
       (forms (termlisp-parse src)))
  ;; 3. Evaluate each form in order; `termlisp-eval-form' takes one
  ;;    already-read form, so the driver is yours.
  (dolist (f forms) (termlisp-eval-form f env))
  ;; 4. Evaluate an application that was never written as source.
  (termlisp-value->string (termlisp-eval-form '(inc3 0) env)))
;; => "3"
```

`termlisp-parse` returns plain S-expressions, so source generation needs
nothing special — `format` is usually enough, and `list`/`cons` work when
you would rather build the forms than the text. Note that
`termlisp-eval-form` handles exactly one form: it does not walk the list
for you, which is what makes it usable as a building block. The `.tls`
prelude is loaded this way.

`tl-graph-build (sexp)` builds a term graph directly from an S-expression,
sharing structurally identical subterms. Heads listed in
`tl-graph-opaque-heads` (currently `quote` and `function`) become a single
opaque leaf holding the whole subterm, so deep quoted data is neither
traversed nor rebuilt.

### Emitting Emacs Lisp

`tl-emit-program (forms)` compiles termlisp top-level forms to a list of
Emacs Lisp forms. The output is standalone: functions become `defun`s,
values `defconst`s, `if` becomes the elisp special form (both branches
lazy, matching Aldor's conditional), and constructor applications become
tagged lists with booleans mapped to `t`/`nil`.

Supported includes single-clause defines, lambdas, `if`, `and`/`or`/`not`,
arithmetic and comparison, constructor applications and nullary
constructor references, the list operations `first`/`rest`/`empty?`
inlined to `car`/`cdr`-style accesses, records and unions (which become
plain vectors), arrays (vectors), and the statement forms produced by loop
lowering — `Seq`→`progn`, `Let`→`let*`, `While`→`while`, `Catch`, `Break`
and `Iterate` throwing to the fixed tags `tl-loop-break` and
`tl-loop-next`.

Self tail calls are optimized: a `defun` whose body calls itself in tail
position is rewritten as a loop that rebinds its parameters from an
argument vector, so tail recursion runs in constant stack.

One limit, stated plainly because it will bite: **multi-clause pattern
dispatch is not yet emitted.** A `define` with several pattern clauses
does not compile through this path.

### The Aldor front end

The pipeline is

```
.as --aldor -Fabn--> .abn --tl-abn-read-file--> ABN tree
    --tl-aldor-lower--> termlisp IR --tl-emit-program--> Lisp forms
```

The one-call entry point is the autoloaded

```elisp
(tl-aldor-compile-file AS-FILE :output FILE :byte-compile t)
```

which returns the generated Emacs Lisp source string, writes it to
`:output`, and optionally byte-compiles it. It shells out to the real
Aldor compiler, so it needs `aldor` on `PATH` (or `tl-aldor-program`) plus
a FriCAS algebra directory; `tl-aldor-available-p` reports whether both are
present, and the Aldor tests skip when they are not.

### I/O

I/O is a State action over the world: the state is threaded through a
computation of the shape `s -> (a . s)`. A `TextReader` is a *box* holding
the remaining input, and `read!` pops one character off the front and
commits the rest. Characters are character codes (integers) and `eof` is
`-1`.

The prelude exposes `io-world`, `io-print`, `io-read-line` and `run-io`.
Readers and writers are the same box type, so the erasing
`f::TextReader` / `f::TextWriter` coercions are the identity.

```lisp
(do (x <- (Just 1))
    (y <- (Just 2))
    (return (+ x y)))       ; => (Just 3)
```

## Reporting bugs

Report at <https://github.com/ningxilai/termlisp/issues>. There is no
issue template yet, so the report has to carry its own context. The
fastest one to write, and the fastest one to reproduce, is a form plus its
option plist:

1. **The smallest form that still fails**, as a single string. If it needs
   the prelude, say so; if it does not, prefer the version that does not.
2. **The option plist you used**, spelled out — `'(:type-check t)` versus
   `'(:elaborate t)` versus bare defaults produce genuinely different
   failures, and this is the single most commonly missing detail.
3. **The verbatim error message**, in full, including the
   `the signature says:` / `this clause gives:` lines if present. Message
   text is the diagnostic; paraphrasing it loses the part that matters.
4. **`C-h v emacs-version`**, since the floor is Emacs 27.1 and the reader
   behaves differently on Emacsen where `read-eval` is bound.
5. **Whether `cats` is installed**, for anything touching
   `termlisp-data-reader.el`.

The macros in `test/test-support.el` — `tl-test-eval`, `tl-test-reject`,
`tl-test-covers` — are the shortest encoding of items 1 and 2. If your
report can be written as one of those, it is already a regression test.

For the Aldor front end, additionally say whether `tl-aldor-available-p`
returns non-nil and what `tl-aldor-program` is set to; that pipeline fails
in ways that look like language bugs and are not.

## Project layout

```
termlisp.el             ; entry point, public API, loader
termlisp-base.el        ; errors, options, environment struct
termlisp-reader.el      ; S-expression reader
termlisp-machine.el     ; runtime objects (thunks, closures, functions)
termlisp-pattern.el     ; pattern parsing and matching
termlisp-builtins.el    ; primitive functions
termlisp-numeric.el     ; exact Fraction/Complex arithmetic over Calc
termlisp-types.el       ; HM inference over the term graph
termlisp-kinds.el       ; kind inference
termlisp-free-vars.el   ; free type variables of a type graph
termlisp-ir-types.el    ; HM typing for the lowering IR
termlisp-resolve.el     ; unification-driven overload resolution
termlisp-elaborate.el   ; dictionary-passing elaborator
termlisp-exhaust.el     ; coverage / exhaustiveness checking
termlisp-eval.el        ; lazy TCO evaluator, `do', top-level forms
termlisp-load.el        ; load .tls files as elisp
termlisp-graph.el       ; term-graph rewriting core
termlisp-graph-unify.el ; graph unification (union-find)
termlisp-graph-types.el ; graph <-> surface bridges (dev branch only)
termlisp-case.el        ; compiled-pattern dispatch
termlisp-nbe.el         ; normalization by evaluation
termlisp-abn.el         ; Aldor ABN reader
termlisp-aldor.el       ; Aldor -> termlisp lowering
termlisp-emit.el        ; termlisp IR -> Emacs Lisp
termlisp-data-reader.el ; cats-based Reader monad
termlisp-io.el          ; State-monad I/O runtime
termlisp-repl.el        ; interactive REPL, `M-x termlisp-repl'
termlisp-prelude.tls    ; the standard prelude
```

### Branches

- `main` — the library only; no tests, no test-only support.
- `dev` — `main` plus the ERT test suite (`test/aldor-test.el`) and the
  graph <-> surface bridges it exercises (`termlisp-graph-types.el`).

### Dependencies

The only external dependency is
[cats](https://github.com/Fuco1/emacs-cats), used by the optional Reader
monad (`termlisp-data-reader.el`). It is declared in `termlisp.el`'s
`Package-Requires` and installed like any package; with elpaca:

```elisp
(elpaca cats)
(elpaca (termlisp :host github :repo "ningxilai/termlisp" :files (:defaults "*.tls")))
```

The core language loads fine without it; only the Reader monad is skipped.

## Development

On `main`:

```
make compile   ; byte-compile
make clean     ; remove .elc files
```

The ERT suite lives on `dev` (`make test` there runs it; 418 tests).
`cats` is expected on the load path; the Makefile defaults to the elpaca
sources directory and honours `CATS_DIR`, e.g.
`make test CATS_DIR=$HOME/src/emacs-cats`.

## Scope

Two things this project has decided not to do. They are recorded here
because they are decisions rather than gaps, and because no other file in
the repository says them.

**Stage 4 is out of scope.** Quantitative type theory — a multiplicity on
every binder plus a separate linearity pass — along with universe levels,
totality checking and general proof search would amount to rewriting the
type layer, and on elisp the NbE performance it leans on has never been
established. QTT is in any case orthogonal to the Curry–Howard reading this
project is about: adding linearity moves it no closer, while costing the
whole type layer.

**`subst` and `rewrite` stay out of the core.** Both already hold as
inference rules over `Eq`, `Refl`, `sym` and `trans`, so they need no
universe, no new code and no library function — promoting them to
primitives would buy nothing the checker does not already do.

## License

GPL-3.0-or-later. See `LICENSE`.
