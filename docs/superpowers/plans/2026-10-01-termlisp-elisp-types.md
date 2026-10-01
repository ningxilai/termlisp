# term-lisp Emacs Lisp Port — Plan 2: HM Type System (phase B) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a Hindley–Milner static type checker (phase B: no type classes) to the term-lisp elisp port, integrated as an independent pass over S-expression terms.

**Architecture:** Types are `tl-tvar` (reusing the unification kernel's `tl-lvar`) and `tl-tcon` (named constructor applied to args). A dedicated structural type unifier shares `tl-deref`/`tl-occurs` with the term kernel and uses alist substitutions with "no-change-loser" failure semantics (inspired by ACL2's `one-way-unify1-term-alist`). Inference is Algorithm W/J with generalization by "tvars not free in the environment" (no level counters) and a **value restriction**. Datatype declarations register constructor type schemes; `(: name TYPE)` registers user signatures. The checker is opt-in via `termlisp-typecheck` and the `:type-check` eval option; it does not change runtime semantics.

**Tech Stack:** Emacs Lisp (`cl-lib`, `ert`); reuses `termlisp-base`, `termlisp-unify`, `termlisp-reader`, `termlisp-eval`.

**Reference:** ACL2 `rewrite.lisp` `one-way-unify1-term-alist` (alist substitution, no-change-loser).

**Scope:** Phase B only. Type classes (Functor/Monad/etc.), dictionary passing, and monadic `do` are Plan 4. peg-based type parsing is deferred (hand-written parser here).

---

## File Structure

```
termlisp-types.el     ; type representation, parser, unifier, substitution, inference
termlisp.el           ; termlisp-typecheck implemented; :type-check wiring
termlisp-base.el      ; add type-env slot to tl-env
termlisp-eval.el      ; register constructor types on datatype; optional type-check
test/termlisp-test.el ; type tests
```

---

## Task 1: Type representation and type unifier

**Files:**
- Modify: `termlisp-unify.el` (add optional `level` slot to `tl-lvar`)
- Create: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(require 'termlisp-types)

(ert-deftest type/representation ()
  (should (tl-type-p (tl-fresh-tvar)))
  (should (tl-type-p (tl-tint)))
  (should (equal (tl-tcon-name (tl-tint)) 'Int))
  (should (equal (tl-tcon-args (tl-tint)) nil)))

(ert-deftest type/unify-atoms ()
  (should (car (tl-unify-types (tl-tint) (tl-tint) nil)))
  (should (null (car (tl-unify-types (tl-tint) (tl-tstring) nil)))))

(ert-deftest type/unify-variable ()
  (let* ((a (tl-fresh-tvar))
         (r (tl-unify-types a (tl-tint) nil)))
    (should (car r))
    (should (equal (tl-deref a (cdr r)) (tl-tint)))))

(ert-deftest type/unify-application ()
  (let* ((a (tl-fresh-tvar))
         (r (tl-unify-types (tl-tcon 'List (list a)) (tl-tcon 'List (list (tl-tint))) nil)))
    (should (car r))
    (should (equal (tl-deref a (cdr r)) (tl-tint)))))

(ert-deftest type/unify-occurs ()
  (let* ((a (tl-fresh-tvar))
         (r (tl-unify-types a (tl-tcon 'List (list a)) nil)))
    (should (null (car r)))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-type-p`.

- [ ] **Step 3: Add the `level` slot to `tl-lvar`**

In `termlisp-unify.el` change the struct constructor to accept an optional level:

```elisp
(cl-defstruct (tl-lvar (:constructor tl-make-lvar (id &optional level))) id (level 0))
```

Existing callers `(tl-make-lvar 'x)` still work (level defaults to 0).

- [ ] **Step 4: Implement `termlisp-types.el` (representation + unifier)**

```elisp
;;; termlisp-types.el --- HM type inference -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Types are either a type variable (a `tl-lvar') or a type constructor
;; application `tl-tcon'.  Substitutions are alists tvar -> type.  The type
;; unifier shares `tl-deref'/`tl-occurs' with the term kernel and, like ACL2's
;; one-way unifier, leaves bindings unchanged on failure.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-unify)

(cl-defstruct (tl-tcon (:constructor tl-tcon (name args))) name args)
(cl-defstruct (tl-tscheme (:constructor tl-tscheme (vars type))) vars type)

(defun tl-tvar-p (x) (tl-lvar-p x))
(defun tl-type-p (x) (or (tl-tvar-p x) (tl-tcon-p x)))

(defun tl-fresh-tvar (&optional level)
  "Return a fresh type variable."
  (tl-make-lvar (gensym "t") (or level 0)))

(defun tl-tarrow (a b) (tl-tcon '-> (list a b)))
(defun tl-tint () (tl-tcon 'Int nil))
(defun tl-tstring () (tl-tcon 'String nil))
(defun tl-tbool () (tl-tcon 'Bool nil))

(defun tl-tfun-args (ty)
  "If TY is `(-> a b)', return (a b), else nil."
  (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
    (tl-tcon-args ty)))

(defun tl-unify-types (a b bindings)
  "Unify types A and B under BINDINGS.  Return `(ok . bindings)'.
On failure returns `(nil . nil)' (no-change-loser)."
  (let ((pending (list (cons a b))) (ok t))
    (while (and pending ok)
      (let* ((pair (pop pending))
             (x (tl-deref (car pair) bindings))
             (y (tl-deref (cdr pair) bindings)))
        (cond
         ((eq x y))
         ((tl-tvar-p x)
          (if (tl-occurs x y bindings) (setq ok nil)
            (setq bindings (cons (cons x y) bindings))))
         ((tl-tvar-p y)
          (if (tl-occurs y x bindings) (setq ok nil)
            (setq bindings (cons (cons y x) bindings))))
         ((and (tl-tcon-p x) (tl-tcon-p y))
          (if (and (eq (tl-tcon-name x) (tl-tcon-name y))
                   (= (length (tl-tcon-args x)) (length (tl-tcon-args y))))
              (let ((ax (tl-tcon-args x)) (ay (tl-tcon-args y)))
                (while ax
                  (push (cons (car ax) (car ay)) pending)
                  (setq ax (cdr ax) ay (cdr ay))))
            (setq ok nil)))
         (t (setq ok nil)))))
    (if ok (cons t bindings) (cons nil nil))))

(provide 'termlisp-types)
;;; termlisp-types.el ends here
```

- [ ] **Step 5: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add termlisp-unify.el termlisp-types.el test/termlisp-test.el
git commit -m "feat: add type representation and type unifier"
```

---

## Task 2: Type expression parser and schemes

**Files:**
- Modify: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest type/parse-atom ()
  (should (equal (tl-type-parse 'Int) (tl-tint)))
  (should (equal (tl-tcon-name (tl-type-parse 'Int)) 'Int)))

(ert-deftest type/parse-arrow ()
  (let ((ty (tl-type-parse '(a -> a))))
    (should (tl-tcon-p ty))
    (should (eq (tl-tcon-name ty) '->))
    (let ((args (tl-tcon-args ty)))
      (should (eq (nth 0 args) (nth 1 args))))))

(ert-deftest type/parse-arrow-right-assoc ()
  ;; (a -> b -> c) parses as (a -> (b -> c))
  (let* ((ty (tl-type-parse '(a -> b -> c)))
         (args (tl-tcon-args ty)))
    (should (tl-tcon-p (nth 1 args)))
    (should (eq (tl-tcon-name (nth 1 args)) '->))))

(ert-deftest type/parse-application ()
  (let* ((ty (tl-type-parse '(List a)))
         (args (tl-tcon-args ty)))
    (should (eq (tl-tcon-name ty) 'List))
    (should (tl-tvar-p (nth 0 args)))))

(ert-deftest type/parse-scheme ()
  (let ((sc (tl-type-parse-scheme '(a -> a))))
    (should (tl-tscheme-p sc))
    (should (= (length (tl-tscheme-vars sc)) 1))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-type-parse`.

- [ ] **Step 3: Implement the parser**

Add to `termlisp-types.el` before `(provide ...)`:

```elisp
(defun tl-type-var-symbol-p (sym)
  "Return non-nil if SYM is a type variable (lowercase-initial)."
  (and (symbolp sym)
       (> (length (symbol-name sym)) 0)
       (string-match-p "\\`[a-z]" (symbol-name sym))))

(defun tl-type-parse (sexp &optional var-alist)
  "Parse surface type expression SEXP into a type.
VAR-ALIST maps lowercase symbols to shared type variables.  Returns
\(TYPE . VAR-ALIST')."
  (cond
   ((tl-type-var-symbol-p sexp)
    (let ((cell (assq sexp var-alist)))
      (if cell (cons (cdr cell) var-alist)
        (let ((tv (tl-fresh-tvar)))
          (cons tv (cons (cons sexp tv) var-alist))))))
   ((symbolp sexp) (cons (tl-tcon sexp nil) var-alist))
   ((and (consp sexp) (memq '-> sexp))
    (let ((parts (tl-split-arrow sexp)))
      (tl-type-parse-arrow parts var-alist)))
   ((consp sexp)
    (let ((ty (tl-tcon (car sexp) nil)) (alist var-alist))
      (dolist (arg (cdr sexp))
        (let ((r (tl-type-parse arg alist)))
          (setf (tl-tcon-args ty) (append (tl-tcon-args ty) (list (car r))))
          (setq alist (cdr r))))
      (cons ty alist)))
   (t (signal 'termlisp-type-error (list (format "Bad type: %S" sexp))))))

(defun tl-split-arrow (sexp)
  "Split SEXP on `->' into its component type expressions."
  (let ((parts nil) (cur nil))
    (dolist (x sexp)
      (if (eq x '->)
          (progn (push (nreverse cur) parts) (setq cur nil))
        (push x cur)))
    (push (nreverse cur) parts)
    (nreverse parts)))

(defun tl-type-parse-arrow (parts var-alist)
  "Parse PARTS as a right-associative arrow chain."
  (if (null (cdr parts))
      (tl-type-parse (car parts) var-alist)
    (let* ((lhs (tl-type-parse (car parts) var-alist))
           (rhs (tl-type-parse-arrow (cdr parts) (cdr lhs))))
      (cons (tl-tarrow (car lhs) (car rhs)) (cdr rhs)))))

(defun tl-type-parse-scheme (sexp)
  "Parse SEXP into a type scheme, quantifying its free variables."
  (let* ((r (tl-type-parse sexp nil))
         (ty (car r)))
    (tl-tscheme (tl-free-tvars ty) ty)))
```

Note: `tl-free-tvars` is defined in Task 3; add a temporary forward reference or reorder. If you run Task 2 before Task 3, define `tl-free-tvars` in Task 3 and move the `tl-type-parse-scheme` test there. To keep tasks independently green, **implement `tl-free-tvars` in this task** (it is needed by the scheme test):

```elisp
(defun tl-free-tvars (type)
  "Return the list of type variables occurring in TYPE."
  (let ((acc nil))
    (cl-labels ((walk (t)
                  (cond ((tl-tvar-p t) (cl-pushnew t acc :test #'eq))
                        ((tl-tcon-p t) (mapc #'walk (tl-tcon-args t))))))
      (walk type))
    acc))
```

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add termlisp-types.el test/termlisp-test.el
git commit -m "feat: add type expression parser and schemes"
```

---

## Task 3: Substitution, generalization, instantiation

**Files:**
- Modify: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest type/subst ()
  (let* ((a (tl-fresh-tvar))
         (ty (tl-tarrow a a))
         (sub (list (cons a (tl-tint)))))
    (should (equal (tl-type-subst ty sub) (tl-tarrow (tl-tint) (tl-tint))))))

(ert-deftest type/generalize-instantiate ()
  (let* ((a (tl-fresh-tvar))
         (ty (tl-tarrow a a))
         (sc (tl-generalize ty nil))
         (i1 (tl-instantiate sc))
         (i2 (tl-instantiate sc)))
    (should (tl-tscheme-p sc))
    (should (= (length (tl-tscheme-vars sc)) 1))
    ;; each instantiation is independent
    (should-not (eq (nth 0 (tl-tcon-args i1)) (nth 0 (tl-tcon-args i2))))))

(ert-deftest type/generalize-respects-env ()
  (let* ((a (tl-fresh-tvar))
         (sc (tl-generalize (tl-tarrow a a) (list a))))
    (should (null (tl-tscheme-vars sc)))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-type-subst`.

- [ ] **Step 3: Implement substitution/generalization/instantiation**

```elisp
(defun tl-type-subst (type sub)
  "Apply substitution SUB (alist tvar -> type) to TYPE."
  (cond
   ((tl-tvar-p type)
    (let ((cell (assq type sub))) (if cell (cdr cell) type)))
   ((tl-tcon-p type)
    (tl-tcon (tl-tcon-name type)
             (mapcar (lambda (t) (tl-type-subst t sub)) (tl-tcon-args type))))
   (t type)))

(defun tl-deref-type (type bindings)
  "Resolve the head of TYPE through BINDINGS."
  (tl-deref type bindings))

(defun tl-apply-bindings (type bindings)
  "Fully apply BINDINGS to TYPE."
  (let ((ty (tl-deref type bindings)))
    (if (tl-tcon-p ty)
        (tl-tcon (tl-tcon-name ty)
                 (mapcar (lambda (t) (tl-apply-bindings t bindings))
                         (tl-tcon-args ty)))
      ty)))

(defun tl-free-tvars-b (type bindings)
  "Free type variables of TYPE under BINDINGS."
  (tl-free-tvars (tl-apply-bindings type bindings)))

(defun tl-generalize (type env-tvars)
  "Generalize TYPE into a scheme, quantifying tvars not in ENV-TVARS."
  (let* ((ftv (tl-free-tvars type))
         (vars (cl-remove-if (lambda (v) (memq v env-tvars)) ftv)))
    (tl-tscheme vars type)))

(defun tl-instantiate (scheme)
  "Instantiate SCHEME (a `tl-tscheme') with fresh type variables."
  (if (tl-tscheme-p scheme)
      (let ((sub (mapcar (lambda (v) (cons v (tl-fresh-tvar)))
                         (tl-tscheme-vars scheme))))
        (tl-type-subst (tl-tscheme-type scheme) sub))
    scheme))
```

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add termlisp-types.el test/termlisp-test.el
git commit -m "feat: add type substitution, generalization, instantiation"
```

---

## Task 4: Type environment and constructor types

**Files:**
- Modify: `termlisp-base.el` (add `type-env` slot)
- Modify: `termlisp-types.el`
- Modify: `termlisp-eval.el` (register constructor types on `datatype`)
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest typeenv/constructors ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Bool (True) (False))" env)
    (should (tl-tscheme-p (gethash 'True (tl-env-type-env env))))
    (should (equal (tl-tscheme-type (gethash 'True (tl-env-type-env env)))
                   (tl-tcon 'Bool nil)))))

(ert-deftest typeenv/constructor-arrow ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Nat (Zero) (Succ Nat))" env)
    (let ((ty (tl-tscheme-type (gethash 'Succ (tl-env-type-env env)))))
      (should (equal ty (tl-tarrow (tl-tcon 'Nat nil) (tl-tcon 'Nat nil)))))))

(ert-deftest typeenv/constructor-polymorphic ()
  (let ((env (termlisp-make-env)))
    (termlisp-eval "(datatype Pair (Pair a b))" env)
    (let* ((sc (gethash 'Pair (tl-env-type-env env)))
           (ty (tl-tscheme-type sc)))
      (should (= (length (tl-tscheme-vars sc)) 2))
      ;; a -> b -> Pair a b
      (should (eq (tl-tcon-name ty) '->)))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `tl-env-type-env` void.

- [ ] **Step 3: Add `type-env` to `tl-env`**

In `termlisp-base.el`, add a slot to the struct:

```elisp
  (type-env (make-hash-table :test #'eq))
```

- [ ] **Step 4: Register constructor types on `datatype`**

In `termlisp-eval.el`'s `tl-eval-datatype`, after registering constructors in `tl-env-constructors`, register their type schemes. Add a helper in `termlisp-types.el`:

```elisp
(defun tl-register-datatype-types (env name ctors)
  "Register constructor type schemes for datatype NAME with CTORS.
Each CTOR is `(CON ARGTYPE...)'.  Lowercase symbols in ARGTYPE are type
parameters of NAME."
  (let* ((type-vars nil)
         (param-list
          ;; Collect type parameters from all constructor arg types.
          (dolist (ctor ctors type-vars)
            (dolist (arg (cdr ctor))
              (let ((r (tl-type-parse arg nil)))
                (dolist (v (tl-free-tvars (car r)))
                  (cl-pushnew v type-vars :test #'eq))))))
         (params (nreverse type-vars))
         (result (tl-tcon name params)))
    (dolist (ctor ctors)
      (let ((ty result))
        (dolist (arg (reverse (cdr ctor)))
          (let ((r (tl-type-parse arg
                                  (mapcar (lambda (v) (cons (gensym) v)) params))))
            (setq ty (tl-tarrow (car r) ty))))
        (puthash (car ctor) (tl-tscheme params ty)
                 (tl-env-type-env env))))))
```

Simplification note for the implementer: the mapping from lowercase parameter symbols to shared type variables must be consistent across constructors (e.g. `Pair a b` uses the same `a` in `a -> b -> Pair a b`). Use a single `var-alist` built once from the datatype's type-parameter symbols, then reuse it for every constructor. A correct implementation:

```elisp
(defun tl-register-datatype-types (env name ctors)
  "Register constructor type schemes for datatype NAME with CTORS."
  (let* ((param-syms nil)
         (alist nil))
    ;; Collect parameter symbols (lowercase) across all constructor args.
    (dolist (ctor ctors)
      (dolist (arg (cdr ctor))
        (let ((r (tl-type-parse arg nil)))
          (ignore r))))
    ;; Build a shared var-alist from lowercase symbols.
    (dolist (ctor ctors)
      (dolist (arg (cdr ctor))
        (tl-collect-type-param-syms arg param-syms)))
    (setq param-syms (nreverse param-syms))
    (dolist (s param-syms)
      (push (cons s (tl-fresh-tvar)) alist))
    (setq alist (nreverse alist))
    (let* ((params (mapcar #'cdr alist))
           (result (tl-tcon name params)))
      (dolist (ctor ctors)
        (let ((ty result))
          (dolist (arg (reverse (cdr ctor)))
            (setq ty (tl-tarrow (car (tl-type-parse arg alist)) ty)))
          (puthash (car ctor) (tl-tscheme params ty)
                   (tl-env-type-env env)))))))

(defun tl-collect-type-param-syms (sexp acc)
  "Collect lowercase type-variable symbols in SEXP into ACC."
  (cond
   ((tl-type-var-symbol-p sexp)
    (unless (memq sexp acc) (setq acc (append acc (list sexp)))))
   ((consp sexp) (dolist (x sexp) (tl-collect-type-param-syms x acc))))
  acc)
```

Then in `tl-eval-datatype`, call `(tl-register-datatype-types env name ctors)` after registering constructors. Add `(require 'termlisp-types)` to `termlisp-eval.el`.

- [ ] **Step 5: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add termlisp-base.el termlisp-types.el termlisp-eval.el test/termlisp-test.el
git commit -m "feat: register datatype constructor type schemes"
```

---

## Task 5: Inference — literals, symbols, application, lambda

**Files:**
- Modify: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest infer/literals ()
  (should (equal (car (tl-infer nil 1)) (tl-tint)))
  (should (equal (car (tl-infer nil "x")) (tl-tstring))))

(ert-deftest infer/lambda ()
  ;; (lambda (x) x) : a -> a
  (let ((ty (car (tl-infer nil '(lambda (x) x)))))
    (should (eq (tl-tcon-name ty) '->))
    (let ((args (tl-tcon-args ty)))
      (should (eq (nth 0 args) (nth 1 args))))))

(ert-deftest infer/application-identity ()
  ;; ((lambda (x) x) 1) : Int
  (let ((r (tl-infer nil '((lambda (x) x) 1))))
    (should (equal (car r) (tl-tint)))))

(ert-deftest infer/type-error ()
  (should-error (tl-infer nil '(1 2)) :type 'termlisp-type-error))
```

`tl-infer` signature: `(tl-infer env expr)` returns `(TYPE . BINDINGS)`. `env` is a `tl-env` or nil (then only literals/lambdas are typeable).

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-infer`.

- [ ] **Step 3: Implement inference core**

```elisp
(defun tl-infer (env expr)
  "Infer the type of EXPR in ENV.  Return `(type . bindings)'.
Signals `termlisp-type-error' on failure."
  (cond
   ((numberp expr) (cons (tl-tint) nil))
   ((stringp expr) (cons (tl-tstring) nil))
   ((symbolp expr) (tl-infer-symbol env expr))
   ((and (consp expr) (eq (car expr) 'lambda))
    (tl-infer-lambda env (cadr expr) (caddr expr)))
   ((consp expr) (tl-infer-application env expr))
   (t (signal 'termlisp-type-error (list (format "Cannot infer: %S" expr))))))

(defun tl-infer-symbol (env sym)
  "Infer the type of a bare symbol SYM."
  (let ((sc (and env (gethash sym (tl-env-type-env env)))))
    (cond
     (sc (cons (tl-instantiate sc) nil))
     (t (cons (tl-fresh-tvar) nil)))))

(defun tl-infer-lambda (env params body)
  "Infer `(lambda PARAMS BODY)'."
  (let ((bindings nil) (ptypes nil))
    (dolist (p params)
      (let ((tv (tl-fresh-tvar)))
        (push (cons p tv) bindings)
        (push tv ptypes)))
    (setq ptypes (nreverse ptypes))
    (let ((r (tl-infer (tl-infer-extend-env env bindings) body)))
      (let ((ty (car r)))
        (dolist (pt (reverse ptypes))
          (setq ty (tl-tarrow pt ty)))
        (cons ty (cdr r))))))

(defun tl-infer-extend-env (env bindings)
  "Return an env-like object with BINDINGS of local names to types.
Since ENV is a `tl-env', local bindings are kept in a dynamic alist."
  (cons bindings env))
```

**Design note:** to keep `tl-infer` simple, local variable types are carried in a `(LOCAL-BINDINGS . ENV)` pair. `tl-infer-symbol` must consult `LOCAL-BINDINGS` first. Update it:

```elisp
(defun tl-infer-symbol (env sym)
  "Infer the type of a bare symbol SYM.
ENV is either nil, a `tl-env', or `(LOCAL-BINDINGS . TL-ENV)'."
  (let* ((locals (and (consp env) (consp (car env)) (car env)))
         (real-env (if (consp env) (cdr env) env))
         (cell (assq sym locals)))
    (cond
     (cell (cons (cdr cell) nil))
     ((and real-env (gethash sym (tl-env-type-env real-env)))
      (cons (tl-instantiate (gethash sym (tl-env-type-env real-env))) nil))
     (t (cons (tl-fresh-tvar) nil)))))
```

Application:

```elisp
(defun tl-infer-application (env expr)
  "Infer a function application EXPR = (F A1 ... AN)."
  (let* ((head (car expr))
         (args (cdr expr))
         (r (tl-infer env head))
         (ftype (car r))
         (bindings (cdr r)))
    (dolist (arg args)
      (let* ((ra (tl-infer env arg))
             (aty (car ra))
             (rb (tl-unify-types bindings (cdr ra) nil)))
        (unless (car rb)
          (signal 'termlisp-type-error (list (format "Unify failed in %S" expr))))
        (setq bindings (cdr rb))
        (let ((res (tl-fresh-tvar))
              (ru (tl-unify-types ftype (tl-tarrow aty res) bindings)))
          (unless (car ru)
            (signal 'termlisp-type-error
                    (list (format "Cannot apply %S to %S" head arg))))
          (setq bindings (cdr ru))
          (setq ftype res))))
    (cons (tl-apply-bindings ftype bindings) bindings)))
```

Note: bindings from sub-inferences must be merged; the code above unifies the sub-bindings into `bindings` via `tl-unify-types bindings (cdr ra) nil`, which is incorrect (that unifies two substitution lists as types). The implementer must merge substitutions properly: a substitution is a list of `(tvar . type)`; to compose, apply `(cdr ra)` to `bindings` and vice versa. Provide a helper:

```elisp
(defun tl-compose-bindings (b1 b2)
  "Compose substitutions B1 and B2 (B2 applied after B1)."
  (append
   (mapcar (lambda (cell) (cons (car cell) (tl-apply-bindings (cdr cell) b2))) b1)
   b2))
```

Use `(setq bindings (tl-compose-bindings (cdr ra) bindings))` after each sub-inference, and unify with the composed `bindings`. The implementer must ensure `tl-apply-bindings` handles unbound tvars (it does).

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS. Iterate until the four tests pass.

- [ ] **Step 5: Commit**

```bash
git add termlisp-types.el test/termlisp-test.el
git commit -m "feat: add type inference for literals, symbols, lambda, application"
```

---

## Task 6: Inference for definitions and patterns

**Files:**
- Modify: `termlisp-types.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest infer/define-id ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(define (id x) x)")
    (let ((ty (tl-tscheme-type (gethash 'id (tl-env-type-env env)))))
      (should (eq (tl-tcon-name ty) '->))
      (should (eq (nth 0 (tl-tcon-args ty)) (nth 1 (tl-tcon-args ty)))))))

(ert-deftest infer/define-peano-plus ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Nat (Zero) (Succ Nat))")
    (termlisp-typecheck-def env "(define (plus Zero b) b)")
    (termlisp-typecheck-def env "(define (plus (Succ a) b) (Succ (plus a b)))")
    (let ((ty (tl-tscheme-type (gethash 'plus (tl-env-type-env env)))))
      (should (equal ty (tl-tarrow (tl-tcon 'Nat nil)
                                   (tl-tarrow (tl-tcon 'Nat nil)
                                              (tl-tcon 'Nat nil))))))))

(ert-deftest infer/type-mismatch-clauses ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(datatype Bool (True) (False))")
    (termlisp-typecheck-def env "(define (bad True) 1)")
    (should-error (termlisp-typecheck-def env "(define (bad False) \"x\")")
                  :type 'termlisp-type-error)))
```

`termlisp-typecheck-def` type-checks one top-level form (a string) into an env, registering functions/constructors, or signals. It is defined in this task.

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function termlisp-typecheck-def`.

- [ ] **Step 3: Implement pattern inference and definition inference**

```elisp
(defun tl-infer-pattern (env pat expected)
  "Infer bindings of PAT at type EXPECTED.  Return `(bindings . BINDINGS)'."
  (cond
   ((eq pat '_) (cons nil nil))
   ((symbolp pat)
    (cons (list (cons pat expected)) nil))
   ((and (consp pat) (eq (car pat) :literal))
    (let ((r (tl-infer env (cadr pat))))
      (let ((u (tl-unify-types (car r) expected (cdr r))))
        (unless (car u)
          (signal 'termlisp-type-error
                  (list (format "Literal pattern %S mismatches" pat))))
        (cons nil (cdr u)))))
   ((and (consp pat) (eq (car pat) :list))
    ;; rest binds a fresh type variable
    (cons (list (cons (cadr pat) (tl-fresh-tvar))) nil))
   ((and (consp pat) (eq (car pat) :lambda))
    ;; the bound function has a fresh type
    (cons (list (cons (cadr pat) (tl-fresh-tvar))) nil))
   ((and (consp pat) (eq (car pat) 'guard))
    (let* ((sub (tl-infer-pattern env (cadr pat) expected))
           (env2 (tl-infer-extend-env env (car sub)))
           (g (tl-infer env2 (caddr pat)))
           (u (tl-unify-types (car g) (tl-tbool) (tl-compose-bindings (cdr g) (cdr sub)))))
      (unless (car u)
        (signal 'termlisp-type-error (list "Guard is not Bool")))
      (cons (car sub) (cdr u))))
   ((and (consp pat) (eq (car pat) 'or))
    (let ((binds nil) (bs nil))
      (dolist (p (cdr pat))
        (let ((r (tl-infer-pattern env p expected)))
          (setq binds (car r) bs (tl-compose-bindings (cdr r) bs))))
      (cons binds bs)))
   ((and (consp pat) (eq (car pat) 'and))
    (let ((binds nil) (bs nil))
      (dolist (p (cdr pat))
        (let ((r (tl-infer-pattern env p expected)))
          (setq binds (append (car r) binds)
                bs (tl-compose-bindings (cdr r) bs))))
      (cons binds bs)))
   ((consp pat)
    ;; constructor pattern (Con SUB...)
    (let ((ctor (car pat))
          (subs (cdr pat)))
      (let ((sc (and (tl-env-p (tl-real-env env))
                     (gethash ctor (tl-env-type-env (tl-real-env env))))))
        (unless sc
          (signal 'termlisp-type-error
                  (list (format "Unknown constructor in pattern: %S" ctor))))
        (let* ((cty (tl-instantiate sc))
               (result-type (tl-infer-result-of-constructor cty (length subs))))
          (let ((u (tl-unify-types result-type expected nil)))
            (unless (car u)
              (signal 'termlisp-type-error
                      (list (format "Constructor %S mismatches %S" ctor expected))))
            (let ((arg-types (tl-infer-arg-types-of-constructor cty (length subs)))
                  (binds nil) (bs (cdr u)))
              (while subs
                (let ((r (tl-infer-pattern env (car subs) (car arg-types))))
                  (setq binds (append (car r) binds)
                        bs (tl-compose-bindings (cdr r) bs)))
                (setq subs (cdr subs) arg-types (cdr arg-types)))
              (cons binds bs)))))))
   (t (signal 'termlisp-type-error (list (format "Bad pattern: %S" pat))))))
```

Helpers `tl-real-env`, `tl-infer-result-of-constructor`, `tl-infer-arg-types-of-constructor`:

```elisp
(defun tl-real-env (env)
  (if (consp env) (cdr env) env))

(defun tl-infer-arg-types-of-constructor (cty n)
  "Return the first N argument types of constructor type CTY."
  (let ((acc nil))
    (dotimes (_ n)
      (let ((args (tl-tfun-args cty)))
        (push (nth 0 args) acc)
        (setq cty (nth 1 args))))
    (nreverse acc)))

(defun tl-infer-result-of-constructor (cty n)
  "Return the result type of constructor type CTY applied to N args."
  (dotimes (_ n) (setq cty (nth 1 (tl-tfun-args cty))))
  cty)
```

Definition inference (registering a monomorphic placeholder while checking clauses, then generalizing):

```elisp
(defun tl-infer-define-clauses (env name clauses)
  "Infer NAME from CLAUSES (list of (PARAMS . BODY)).  Return a scheme."
  (let* ((placeholder (tl-fresh-tvar))
         (tyenv (tl-env-type-env env))
         (existing (gethash name tyenv)))
    (puthash name (tl-tscheme nil placeholder) tyenv)
    (let ((bindings nil))
      (dolist (clause clauses)
        (let* ((params (car clause))
               (body (cdr clause))
               (ptypes (mapcar (lambda (_) (tl-fresh-tvar)) params))
               (binds nil) (bs nil))
          (while params
            (let ((r (tl-infer-pattern (cons nil env) (car params) (car ptypes))))
              (setq binds (append (car r) binds)
                    bs (tl-compose-bindings (cdr r) bs)))
            (setq params (cdr params) ptypes (cdr ptypes)))
          (let* ((env2 (tl-infer-extend-env (cons nil env) binds))
                 (rb (tl-infer env2 body))
                 (ctype (car rb))
                 (bs2 (tl-compose-bindings (cdr rb) bs)))
            (dolist (pt (reverse (mapcar (lambda (p) (tl-apply-bindings p bs2)) ptypes)))
              (setq ctype (tl-tarrow pt ctype)))
            (let ((u (tl-unify-types placeholder ctype bs2)))
              (unless (car u)
                (signal 'termlisp-type-error
                        (list (format "Clause of %S has inconsistent type" name))))
              (setq bindings (cdr u))))))
      (let ((final (tl-apply-bindings placeholder bindings)))
        (puthash name (tl-generalize final nil) tyenv)))))
```

**Value restriction note:** for phase B, generalize function definitions (they are lambdas — syntactic values). For `(define name expr)` constants, only generalize if `expr` is a syntactic value (lambda, constructor application, literal, or symbol); otherwise register monomorphically. Implement:

```elisp
(defun tl-syntactic-value-p (expr)
  "Return non-nil if EXPR is a syntactic value (value restriction)."
  (or (atom expr)
      (and (consp expr) (eq (car expr) 'lambda))))

(defun tl-infer-constant (env name expr)
  "Infer a constant binding NAME = EXPR."
  (let ((r (tl-infer (cons nil env) expr)))
    (let ((ty (tl-apply-bindings (car r) (cdr r))))
      (puthash name
               (if (tl-syntactic-value-p expr)
                   (tl-generalize ty nil)
                 (tl-tscheme nil ty))
               (tl-env-type-env env))
      ty)))
```

Top-level typecheck entry (used by Task 7's API):

```elisp
(defun termlisp-typecheck-def (env string)
  "Typecheck all top-level forms in STRING into ENV.  Return ENV."
  (dolist (form (termlisp-parse string) env)
    (tl-typecheck-form env form)))

(defun tl-typecheck-form (env form)
  "Typecheck one top-level FORM in ENV, updating its type environment."
  (cond
   ((and (consp form) (eq (car form) 'datatype))
    (tl-eval-datatype env form))
   ((and (consp form) (eq (car form) 'datatype-extension))
    (tl-eval-datatype-extension env form))
   ((and (consp form) (eq (car form) ':)) (tl-register-signature env form))
   ((and (consp form) (eq (car form) 'define))
    (tl-typecheck-define env form))
   (t (tl-infer (cons nil env) form) nil)))

(defun tl-typecheck-define (env form)
  "Typecheck a `define' FORM, registering it in ENV."
  (let ((target (cadr form)))
    (if (consp target)
        (let* ((name (car target))
               (params (cdr target))
               (body (caddr form))
               (existing (gethash name (tl-env-type-env env))))
          (if existing
              ;; additional clause: re-infer all clauses together
              (let ((clauses (tl-collect-clauses env name)))
                (tl-infer-define-clauses env name
                                         (append clauses (list (cons params body)))))
            (tl-infer-define-clauses env name (list (cons params body)))))
      (tl-infer-constant env target (caddr form)))))
```

`tl-collect-clauses` must recover previously checked clauses of NAME. Since Plan 2 type-checks forms incrementally, store each function's clauses in a side table `tl-env-fn-clauses` (add a hash slot to `tl-env`) or reuse the evaluator's `tl-env-functions` if the evaluator already ran. Simplest: maintain a hash `type-clauses` in `tl-env` mapping name → list of `(params . body)`, updated by `tl-typecheck-define`. Add the slot in Task 4 alongside `type-env`.

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS. This task is the hardest; iterate on `tl-compose-bindings` ordering until the Peano `plus` test passes.

- [ ] **Step 5: Commit**

```bash
git add termlisp-types.el termlisp-base.el test/termlisp-test.el
git commit -m "feat: add type inference for definitions and patterns"
```

---

## Task 7: Signatures, public API, eval integration, prelude acceptance

**Files:**
- Modify: `termlisp-types.el`
- Modify: `termlisp.el`
- Test: `test/termlisp-test.el`

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest signature/checked ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(: id (a -> a))")
    (termlisp-typecheck-def env "(define (id x) x)")
    (should (gethash 'id (tl-env-type-env env)))))

(ert-deftest signature/mismatch ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck-def env "(: id Int)")
    (should-error (termlisp-typecheck-def env "(define (id x) x)")
                  :type 'termlisp-type-error)))

(ert-deftest api/typecheck-string ()
  (let ((env (termlisp-make-env)))
    (termlisp-typecheck "(define (id x) x)" env)
    (should (gethash 'id (tl-env-type-env env)))))

(ert-deftest api/typecheck-prelude ()
  "The prelude must typecheck without error."
  (let ((env (termlisp-make-env)))
    (should (termlisp-typecheck-file
             (expand-file-name "termlisp-prelude.tlsp" termlisp--directory)
             env))))

(ert-deftest api/eval-with-type-check ()
  (let ((env (termlisp-make-env '(:type-check t))))
    (should (equal (termlisp-eval "(define (id x) x) (id 42)" env) 42))
    (should-error (termlisp-eval "(define (bad x) (+ x 1)) (bad \"s\")" env)
                  :type 'termlisp-type-error)))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-register-signature` / `termlisp-typecheck` stub.

- [ ] **Step 3: Implement signatures and API**

```elisp
(defun tl-register-signature (env form)
  "Register a `(: NAME TYPE)' signature in ENV."
  (let* ((name (cadr form))
         (sc (tl-type-parse-scheme (caddr form))))
    (puthash name sc (tl-env-type-env env))
    (puthash name :signature (tl-env-sig-env env))
    name))
```

`tl-typecheck-define` must check the inferred type against a registered signature: after inferring, if `(gethash name (tl-env-sig-env env))` is `:signature`, unify the inferred (generalized) type with the signature and signal on mismatch. Add a `sig-env` hash slot in Task 4.

Public API in `termlisp-types.el`:

```elisp
(defun termlisp-typecheck (string &optional env)
  "Typecheck STRING in ENV (fresh if nil).  Return ENV; signal on error."
  (let ((env (or env (termlisp-make-env))))
    (termlisp-typecheck-def env string)))

(defun termlisp-typecheck-file (file &optional env)
  "Typecheck the contents of FILE in ENV."
  (termlisp-typecheck
   (with-temp-buffer (insert-file-contents file) (buffer-string))
   env))
```

Update `termlisp.el`'s `termlisp-typecheck` stub to require `termlisp-types` and delegate to `termlisp-types`' version (or remove the stub and let `termlisp-types` provide it; ensure only one definition — delete the stub in `termlisp.el` and add `termlisp-types` to the loader's feature list).

- [ ] **Step 4: Wire `:type-check` into `termlisp-eval`**

In `termlisp-eval.el`, when `(tl-env-option env :type-check)` is non-nil, run `termlisp-typecheck-def` on each top-level form before `tl-eval-top`:

```elisp
(dolist (form (termlisp-parse string) result)
  (when (tl-env-option env :type-check)
    (tl-typecheck-form env form))
  (setq result (tl-eval-top env form)))
```

Add `(require 'termlisp-types)` to `termlisp-eval.el`.

- [ ] **Step 5: Run test to verify it passes**

Run: `make test`
Expected: PASS. The prelude typecheck test is the acceptance gate; if the prelude does not typecheck, fix the inference (do not weaken the test). Likely issues: `map`'s `:lambda` type, `and`/`or` clause types, `not`'s Bool type.

- [ ] **Step 6: Byte-compile and commit**

Run: `make compile` (exit 0, no warnings).

```bash
git add termlisp-types.el termlisp.el termlisp-eval.el termlisp-base.el test/termlisp-test.el
git commit -m "feat: add type signatures, public typecheck API, eval integration"
```

---

## Self-Review

**Spec coverage (Plan 2 / spec §8):**
- §8.1 type representation (`tl-tvar`, `tl-tcon`, `tl-tscheme`) — Tasks 1–2. Minimal kind checking is deferred (note below).
- §8.2 phase B: Algorithm W/J, generalize/instantiate, value restriction, recursion via monomorphic placeholder, constructor types from datatypes — Tasks 3–6.
- §8.3 type classes — **deferred to Plan 4** (explicitly out of scope).
- §12 `termlisp-typecheck` — Task 7.
- §13 type tests — all tasks; prelude acceptance in Task 7.

**Known deferrals (tracked):**
- Kind checking (`*`, `* -> *`) — not needed for phase B monomorphic/polymorphic ADTs; add with type classes in Plan 4.
- peg-based type parsing — hand-written parser used; peg can replace `tl-type-parse` later.
- Exhaustiveness/coverage checking — not required (open types are intentionally partial).
- `Maybe`-typed match failure — Plan 3.

**Type/name consistency:** `tl-tcon` (name, args), `tl-tscheme` (vars, type), `tl-unify-types` returns `(ok . bindings)`, `tl-infer` returns `(type . bindings)`, `tl-infer-pattern` returns `(bindings . bindings)`.
