> Disclaimer: This project is at an early stage, many things may not work.

# term-lisp

term-lisp is a language for *term* *lis*t *p*rocessing with first-class pattern
matching, lazy evaluation, tail-call optimization, static types, type classes,
and monads. It is implemented in Emacs Lisp as an embedded library.

## Overview

### Term rewriting

Right from when Church and Turing defined it, the concept of computation has
been two-fold: it can be presented either as the process of mutating the values
of some state (Turing Machine) or by transforming terms using a predefined set
of equations (Lambda Calculus). term-lisp leans heavily in the second direction.
Its functions are *rules* that describe how to replace a given term with
another one.

### Data types and open terms

Data types are declared explicitly, and a term that is not a defined function is
just a constructor. For example:

```lisp
(datatype Bool (True) (False))
(define (if (True) a b) a)
(define (if (False) a b) b)
```

`True` and `False` are nullary constructors. Data types may also be declared
`open`, in which case constructors can be added later and pattern matches are
never considered exhaustive (a failed match is a runtime error):

```lisp
(datatype open Expr (Lit Int))
(datatype-extension Expr (Add Expr Expr))
```

### First-class pattern matching

Definitions are lists of patterns and a body. Patterns include variables,
wildcards (`_`), constructor destructuring, literal values, rest arguments, and
functions:

```lisp
(define (car (Pair a b)) a)      ; destructuring
(define (is-zero (:literal 0)) True) ; value matching
(define (list (:list rest)) rest)    ; remaining arguments
(define (map a (:lambda fun)) (fun a)) ; passing a function
```

### Lazy evaluation and TCO

Arguments are memoized thunks (call-by-need), so unused arguments are never
evaluated. Function application and forcing a variable-bound thunk are tail
steps in an explicit CEK machine, so deep tail recursion does not grow the
Emacs stack.

### Static types and type classes

A Hindley–Milner type checker infers types (opt-in via `:type-check`).
Every builtin carries a type scheme, so ill-typed calls are rejected before
they reach the evaluator:

```lisp
(+ 1 True)              ; Cannot apply + to True
(cos True)               ; Cannot apply cos to True
(string->list 42)        ; Cannot apply string->list to 42
(sin (sin 1))            ; ok — the transcendental numerics compose
```

Numeric literals are inferred `Int` regardless of their runtime
representation, so `sin`/`cos`/`tan`/`exp`/`log`/`sqrt` are typed
`Int -> Int` (as `/` already was).  The exact numeric tower
(`tl-fraction`, `tl-complex`, `tl-num-*`) is polymorphic.

Variadic `list` has no fixed arity to express as a curried arrow, so it is
expanded to nested `Cons` applications in both the evaluator and the type
checker — the same trick Coalton uses for `make`/`make-list`.  It therefore
acquires a type at each call site, and `Cons` enforces that the elements are
homogeneous:

```lisp
(list 1 2 3)         ; (List Int)
(list 1 True)        ; Cannot apply Cons to (Cons True Nil)
```

Type classes with dictionary passing are supported (opt-in via `:elaborate`):

```lisp
(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))
(instance (Functor Maybe) FunctorMaybeDict)
;; (fmap (lambda (x) (+ x 1)) (Just 4)) => (Just 5)
```

### Propositional types

Types are propositions and programs are proofs, so the prelude carries the
constructive connectives.  The Curry–Howard reading holds outright for
intuitionistic propositional logic:

| Proposition | Type |
|---|---|
| truth `⊤` | `Unit` |
| falsehood `⊥` | `Void` — declares no constructors |
| conjunction | `(Pair a b)` |
| disjunction | `(Either a b)` — `Left`, `Right` |
| implication | `a -> b` |
| negation `¬a` | `a -> Void` |

```lisp
(define (and-implies-or (Pair a b)) (Left a))   ; A ∧ B → A ∨ B
(: not-void (Void -> Void))
(define (not-void v) v)                          ; ¬⊥
```

`absurd : ∀a. Void -> a` is `⊥`-elimination.  It can never run, because
`Void` has no constructors; reaching it at all means `:type-check` was off,
and it signals rather than answering a value.

### Monads and `do`

```lisp
(do (x <- (Just 1))
    (y <- (Just 2))
    (return (+ x y)))       ; => (Just 3)
```

## Using the library

```elisp
(require 'termlisp)
```

API:

- `termlisp-make-env` — create an environment, with plist options:
  - `:type-check` — typecheck each top-level form before evaluating it.
  - `:elaborate` — type-directed elaboration (inserts class-method dictionaries).
- `termlisp-eval` / `termlisp-eval-file` — parse and evaluate a string / file.
- `termlisp-parse` — parse a string into a list of S-expressions.
- `termlisp-typecheck` / `termlisp-typecheck-file` — typecheck a string / file.
- `termlisp-load-prelude` — load `termlisp-prelude.tls` into an environment.
  The prelude defines the booleans, pairs, `Either`/`Void`, lists, monads
  and type classes, together with the hlisp operators `=`, `xor`, `null?`,
  `foldl`, `reverse` and `sort`.  I/O is a State action over the world:
  `io-world`, `io-print`, `io-read-line` and `run-io`.
- `termlisp-value->string` — render a value.
- Builtins — the primitive functions term-lisp code can call: `eq`, `+`, `-`,
  `*`, `/`, `<`, `<=`, `>`, `>=`, `sin`, `cos`, `tan`, `exp`, `log`, `sqrt`,
  `list`, `seq`, `first`, `rest`, `empty?`, `absurd`, `stdin`, `read-line`,
  `print`, `format`, `string-join`, `string->list`, `list->string`.

Example:

```elisp
(let ((env (termlisp-load-prelude (termlisp-make-env '(:elaborate t)))))
  (termlisp-value->string
   (termlisp-eval "(fmap (lambda (x) (+ x 1)) (Just 4))" env)))
;; => "(Just 5)"
```

## The REPL

`M-x termlisp-repl` opens a comint buffer with a `λ>` prompt. Input is
evaluated in the running Emacs, so definitions made at the prompt stay for the
rest of the session. The environment starts from `termlisp-repl-options`
(`:type-check` on by default) and, unless `termlisp-repl-load-prelude` is nil,
the prelude is loaded into it.

- `RET` sends the input when it reads as a sequence of complete top-level
  forms; an unfinished form moves to the next line and is indented, so a form
  can be typed across several lines without an escape character.
- `C-j` inserts a newline without evaluating.
- `M-p`, `M-n`, `M-r` browse the input history; `C-c C-o` removes output.
- `C-c C-k` discards every definition and loads a fresh environment.
- `C-c C-t` toggles `:type-check` for the current environment.
- An input of `exit` (or `quit`) closes the REPL.

Errors are reported in the buffer (`error: ...`) and the REPL keeps running.

## Project layout

```
termlisp.el            ; entry point, public API, loader
termlisp-base.el       ; errors, options, environment struct
termlisp-reader.el     ; S-expression reader
termlisp-graph.el      ; term-graph rewriting core
termlisp-graph-unify.el; graph unification (union-find)
termlisp-types.el      ; HM inference over the term graph
termlisp-free-vars.el  ; free type variables of a type graph
termlisp-kinds.el      ; kind inference
termlisp-ir-types.el   ; HM typing for the lowering IR
termlisp-resolve.el    ; unification-driven overload resolution
termlisp-elaborate.el  ; dictionary-passing elaborator
termlisp-machine.el    ; runtime objects (thunks, closures, functions)
termlisp-pattern.el    ; pattern parsing and matching
termlisp-builtins.el   ; primitive functions
termlisp-numeric.el    ; exact Fraction/Complex arithmetic over Calc
termlisp-eval.el       ; lazy TCO evaluator, `do`, top-level forms
termlisp-load.el       ; load .tls files as elisp
termlisp-repl.el      ; interactive REPL, `M-x termlisp-repl'
termlisp-data-reader.el; cats-based Reader monad
termlisp-io.el         ; State-monad I/O runtime
termlisp-abn.el        ; Aldor ABN reader
termlisp-aldor.el      ; Aldor -> termlisp lowering
termlisp-emit.el       ; termlisp IR -> Emacs Lisp
termlisp-prelude.tls   ; the standard prelude
```

### Branches

- `main` — the library only (this branch); no tests, no test-only support.
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

The ERT suite lives on `dev` (`make test` there runs it).  `cats` is
expected on the load path; the Makefile defaults to the elpaca sources
directory and honours `CATS_DIR`, e.g.
`make test CATS_DIR=$HOME/src/emacs-cats`.

## License

GPL-3.0-or-later. See `LICENSE`.
