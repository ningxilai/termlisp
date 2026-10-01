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
Type classes with dictionary passing are supported (opt-in via `:elaborate`):

```lisp
(class Functor (f) nil (fmap ((-> a b) -> (f a) -> (f b))))
(instance (Functor Maybe) FunctorMaybeDict)
;; (fmap (lambda (x) (+ x 1)) (Just 4)) => (Just 5)
```

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
- `termlisp-load-prelude` — load `termlisp-prelude.tlsp` into an environment.
- `termlisp-value->string` — render a value.

Example:

```elisp
(let ((env (termlisp-load-prelude (termlisp-make-env '(:elaborate t)))))
  (termlisp-value->string
   (termlisp-eval "(fmap (lambda (x) (+ x 1)) (Just 4))" env)))
;; => "(Just 5)"
```

## Project layout

```
termlisp.el            ; entry point, public API, loader
termlisp-base.el       ; errors, options, environment struct
termlisp-reader.el     ; S-expression reader
termlisp-unify.el      ; unification kernel (generic structural core)
termlisp-types.el      ; HM inference, type classes, constraints
termlisp-elaborate.el  ; dictionary-passing elaborator
termlisp-machine.el    ; runtime objects (thunks, closures, functions)
termlisp-pattern.el    ; pattern parsing and matching
termlisp-builtins.el   ; primitive functions
termlisp-eval.el       ; lazy TCO evaluator, `do`, top-level forms
termlisp-data-reader.el; cats-based Reader monad
termlisp-prelude.tlsp  ; the standard prelude
examples/              ; example programs
test/                  ; ERT test suite
vendor/cats/           ; vendored emacs-cats (GPLv3)
```

## Development

```
make test      ; run the ERT suite
make compile   ; byte-compile
make clean     ; remove .elc files
```

## License

GPL-3.0-or-later. See `LICENSE`. `vendor/cats` is GPLv3.
