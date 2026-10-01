# term-lisp Emacs Lisp Port — Plan 1: Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a working, tested, lazy, TCO-capable term-rewriting evaluator in Emacs Lisp with pattern matching, open datatypes, and an embedded library API.

**Architecture:** Terms are plain S-expressions. A CEK-style evaluator (`tl-run`) evaluates to weak head normal form; function application is a tail call in the driver loop (giving TCO), while sub-expressions are evaluated lazily via memoized thunks forced on demand. Patterns are compiled to a small AST and matched with callbacks for forcing and literal/guard evaluation. Runtime objects (thunk, closure, function) are `cl-defstruct`s. A shared unification kernel (`tl-unify`) will later serve both the type checker and open-term matching.

**Tech Stack:** GNU Emacs 32 (built-in `cl-lib`, `ert`), `peg.el` (later, for type/pattern sub-grammar), vendored `emacs-cats` (GPLv3, used from Plan 3 onward).

**Scope:** This plan produces an untyped-but-working language. Static types (phase B then A) are Plan 2/4; language-level monads are Plan 3; full prelude is Plan 5.

---

## File Structure

```
LICENSE                        ; replaced with GPLv3
vendor/cats/                   ; vendored emacs-cats (GPLv3)
termlisp.el                    ; public API, load-path, require
termlisp-base.el               ; errors, options, tl-env struct
termlisp-reader.el             ; S-exp reading
termlisp-unify.el              ; unification kernel
termlisp-machine.el            ; runtime objects + value helpers
termlisp-pattern.el            ; pattern parse/match
termlisp-builtins.el           ; primitive functions
termlisp-eval.el               ; tl-run, define, datatypes, top-level
termlisp-prelude.tlsp          ; MVP prelude in new syntax
test/termlisp-test.el          ; ERT suite
```

All elisp files use `lexical-binding: t`.

---

## Task 1: License change, vendor cats, test harness

**Files:**
- Modify: `LICENSE`
- Create: `vendor/cats/` (copied)
- Create: `test/termlisp-test.el`
- Create: `Makefile`

- [ ] **Step 1: Replace LICENSE with GPLv3 text**

Fetch the canonical text and replace the file:

```bash
cd /home/iris/termlisp
curl -fsSL https://www.gnu.org/licenses/gpl-3.0.txt -o LICENSE
head -1 LICENSE
```

Expected: `                    GNU GENERAL PUBLIC LICENSE`

(If offline, copy from an Emacs installation: `cp /usr/share/emacs/*/etc/COPYING LICENSE`.)

- [ ] **Step 2: Vendor emacs-cats**

```bash
cd /home/iris/termlisp
mkdir -p vendor
cp -r /home/iris/Downloads/emacs-cats vendor/cats
rm -rf vendor/cats/.git vendor/cats/tests vendor/cats/.github
ls vendor/cats
```

Expected: files like `cats.el`, `cats-macros.el`, `cats-data-state.el`, `LICENSE`.

- [ ] **Step 3: Write the loader and the ERT test harness**

Create `termlisp.el`. It conditionally loads whichever modules exist, so
tests can run from the very first task:

```elisp
;;; termlisp.el --- Lazy term-rewriting language -*- lexical-binding: t; -*-

;;; Commentary:
;; Embedded library API for term-lisp.

;;; Code:

(defvar termlisp--root
  (file-name-directory (or load-file-name buffer-file-name))
  "Root directory of the termlisp package.")

(add-to-list 'load-path (expand-file-name "vendor/cats" termlisp--root))

(dolist (feature '(termlisp-base termlisp-reader termlisp-unify
                   termlisp-machine termlisp-pattern termlisp-builtins
                   termlisp-eval))
  (when (locate-library (symbol-name feature))
    (require feature)))

(provide 'termlisp)
;;; termlisp.el ends here
```

Create `test/termlisp-test.el`:

```elisp
;;; termlisp-test.el --- Tests for termlisp -*- lexical-binding: t; -*-

(require 'ert)
(add-to-list 'load-path (expand-file-name ".." (file-name-directory load-file-name)))
(require 'termlisp)

(provide 'termlisp-test)
;;; termlisp-test.el ends here
```

- [ ] **Step 4: Write the Makefile**

Create `Makefile`:

```makefile
EMACS ?= emacs

.PHONY: test compile clean

test:
	$(EMACS) -Q --batch -L . -L test -l test/termlisp-test.el \
	  -f ert-run-tests-batch-and-exit

compile:
	$(EMACS) -Q --batch -L . -L test \
	  -f batch-byte-compile termlisp*.el

clean:
	rm -f *.elc test/*.elc
```

- [ ] **Step 5: Commit**

```bash
cd /home/iris/termlisp
git add LICENSE vendor Makefile termlisp.el test/termlisp-test.el
git commit -m "chore: relicense to GPLv3, vendor cats, add ERT harness"
```

---

## Task 2: `termlisp-base.el` — errors, options, environment

**Files:**
- Create: `termlisp-base.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing test**

Append to `test/termlisp-test.el` (before the `provide` line; for all later tasks, insert tests before `(provide 'termlisp-test)`):

```elisp
(ert-deftest base/env-defaults ()
  (let ((env (termlisp-make-env)))
    (should (tl-env-p env))
    (should (hash-table-p (tl-env-functions env)))
    (should (eq (tl-env-option env :phase) 'B))
    (should (eq (tl-env-option env :occurs-check) t))))

(ert-deftest base/env-option-override ()
  (let ((env (termlisp-make-env '(:fuel 10))))
    (should (= (tl-env-option env :fuel) 10))
    (should (eq (tl-env-option env :occurs-check) t))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function termlisp-make-env`.

- [ ] **Step 3: Implement `termlisp-base.el`**

```elisp
;;; termlisp-base.el --- Core types, errors, environment -*- lexical-binding: t; -*-

;;; Commentary:
;; Shared definitions used by every other termlisp module.

;;; Code:

(require 'cl-lib)

(define-error 'termlisp-error "Term-lisp error")
(define-error 'termlisp-parse-error "Term-lisp parse error" 'termlisp-error)
(define-error 'termlisp-type-error "Term-lisp type error" 'termlisp-error)
(define-error 'termlisp-eval-error "Term-lisp evaluation error" 'termlisp-error)

(defconst termlisp-default-options
  '(:occurs-check t :fuel 100000 :type-check nil :phase B)
  "Default evaluation options.")

(cl-defstruct (tl-env (:constructor tl-env--make))
  "Term-lisp evaluation context."
  (functions (make-hash-table :test #'eq))
  (datatypes (make-hash-table :test #'eq))
  (constructors (make-hash-table :test #'eq))
  (globals nil)
  (options termlisp-default-options))

(defun termlisp-make-env (&optional options)
  "Create a fresh evaluation environment, merging OPTIONS over defaults."
  (tl-env--make
   :options (append options termlisp-default-options)))

(defun tl-env-option (env key &optional default)
  "Return option KEY of ENV, or DEFAULT if unset."
  (let ((plist (tl-env-options env)))
    (if (plist-member plist key)
        (plist-get plist key)
      default)))

(provide 'termlisp-base)
;;; termlisp-base.el ends here
```

Note: `append options termlisp-default-options` lets user options win because `plist-get` returns the first match.

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add termlisp-base.el test/termlisp-test.el
git commit -m "feat: add termlisp-base (errors, options, env)"
```

---

## Task 3: `termlisp-unify.el` — unification kernel

**Files:**
- Create: `termlisp-unify.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

`tl-unify` returns `(ok . bindings)` so success is distinguishable from an empty binding list.

```elisp
(ert-deftest unify/atom-equal ()
  (should (car (tl-unify 'a 'a nil)))
  (should (null (car (tl-unify 'a 'b nil)))))

(ert-deftest unify/var-binding ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify x 1 nil)))
    (should (car r))
    (should (equal (tl-deref x (cdr r)) 1))))

(ert-deftest unify/structural ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify (list 'f x) (list 'f 2) nil)))
    (should (car r))
    (should (equal (tl-deref x (cdr r)) 2))))

(ert-deftest unify/occurs-check ()
  (let* ((x (tl-make-lvar 'x))
         (r (tl-unify x (list 'f x) nil t)))
    (should (null (car r)))))

(ert-deftest unify/mismatch ()
  (should (null (car (tl-unify (list 'f 1) (list 'g 1) nil))))
  (should (null (car (tl-unify 1 2 nil)))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-unify`.

- [ ] **Step 3: Implement `termlisp-unify.el`**

```elisp
;;; termlisp-unify.el --- Unification kernel -*- lexical-binding: t; -*-

;;; Commentary:
;; Shared by pattern matching (open terms) and, in Plan 2, type inference.
;; A logic variable is a `tl-lvar' struct; bindings are an alist lvar -> term.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(cl-defstruct (tl-lvar (:constructor tl-make-lvar (id))) id)

(defun tl-deref (term bindings)
  "Follow variable BINDINGS on TERM until a non-variable or unbound."
  (let (cell)
    (while (and (tl-lvar-p term)
                (setq cell (assq term bindings)))
      (setq term (cdr cell)))
    term))

(defun tl-occurs (var term bindings)
  "Return non-nil if VAR occurs in TERM under BINDINGS."
  (let ((work (list term)) (found nil))
    (while (and work (not found))
      (let ((t0 (tl-deref (pop work) bindings)))
        (cond ((eq t0 var) (setq found t))
              ((consp t0)
               (push (car t0) work)
               (push (cdr t0) work)))))
    found))

(defun tl-unify (a b bindings &optional occurs-check)
  "Unify A and B under BINDINGS.
Return a cons `(ok . bindings)'; ok is t on success, nil on failure.
When OCCURS-CHECK is non-nil, reject cyclic bindings."
  (let ((pending (list (cons a b))) (ok t))
    (while (and pending ok)
      (let* ((pair (pop pending))
             (x (tl-deref (car pair) bindings))
             (y (tl-deref (cdr pair) bindings)))
        (cond
         ((eq x y))
         ((tl-lvar-p x)
          (if (and occurs-check (tl-occurs x y bindings))
              (setq ok nil)
            (setq bindings (cons (cons x y) bindings))))
         ((tl-lvar-p y)
          (if (and occurs-check (tl-occurs y x bindings))
              (setq ok nil)
            (setq bindings (cons (cons y x) bindings))))
         ((and (consp x) (consp y))
          (push (cons (car x) (car y)) pending)
          (push (cons (cdr x) (cdr y)) pending))
         ((equal x y))
         (t (setq ok nil)))))
    (cons ok bindings)))

(provide 'termlisp-unify)
;;; termlisp-unify.el ends here
```

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS (all tests).

- [ ] **Step 5: Commit**

```bash
git add termlisp-unify.el test/termlisp-test.el
git commit -m "feat: add unification kernel"
```

---

## Task 4: `termlisp-reader.el` — read S-expressions

**Files:**
- Create: `termlisp-reader.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest reader/single-form ()
  (should (equal (termlisp-parse "(id 42)") '((id 42)))))

(ert-deftest reader/multiple-forms ()
  (should (equal (termlisp-parse "(a) (b c)") '((a) (b c)))))

(ert-deftest reader/comments-and-whitespace ()
  (should (equal (termlisp-parse ";; hi\n(a)\n  (b)") '((a) (b)))))

(ert-deftest reader/keyword-pattern ()
  (should (equal (termlisp-parse "(:literal true)")
                 '((:literal true)))))

(ert-deftest reader/unbalanced-signals ()
  (should-error (termlisp-parse "(a b") :type 'termlisp-parse-error))

(ert-deftest reader/extra-close-signals ()
  (should-error (termlisp-parse "(a))") :type 'termlisp-parse-error))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function termlisp-parse`.

- [ ] **Step 3: Implement `termlisp-reader.el`**

```elisp
;;; termlisp-reader.el --- Read term-lisp source -*- lexical-binding: t; -*-

;;; Commentary:
;; Top-level forms are ordinary S-expressions read with the Emacs reader.

;;; Code:

(require 'termlisp-base)

(defun termlisp-parse (string)
  "Read all top-level forms from STRING and return them as a list."
  (with-temp-buffer
    (insert string)
    (goto-char (point-min))
    (let (forms form)
      (condition-case err
          (while (progn (skip-chars-forward " \t\n\r\f")
                        (not (eobp)))
            (setq form (read (current-buffer)))
            (push form forms))
        (end-of-file
         (signal 'termlisp-parse-error
                 (list (format "Unbalanced parentheses: unexpected end of input"))))
        (error
         (signal 'termlisp-parse-error
                 (list (format "Parse error at %d: %s"
                               (point) (error-message-string err))))))
      (nreverse forms))))

(defun termlisp-parse-file (file)
  "Read all top-level forms from FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (termlisp-parse (buffer-string))))

(provide 'termlisp-reader)
;;; termlisp-reader.el ends here
```

Note: `(read ...)` signals `end-of-file` for a missing close paren and `invalid-read-syntax` for a stray `)`. Both are converted to `termlisp-parse-error`.

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add termlisp-reader.el test/termlisp-test.el
git commit -m "feat: add S-expression reader"
```

---

## Task 5: `termlisp-machine.el` — runtime objects and value helpers

**Files:**
- Create: `termlisp-machine.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest machine/thunk-accessors ()
  (let ((t0 (tl-make-thunk '(f 1) '((x . 1)))))
    (should (tl-thunk-p t0))
    (should (equal (tl-thunk-expr t0) '(f 1)))
    (should (null (tl-thunk-forced-p t0)))))

(ert-deftest machine/value-equal-atoms ()
  (should (tl-value-equal 1 1 #'identity))
  (should-not (tl-value-equal 1 2 #'identity))
  (should (tl-value-equal 'Foo 'Foo #'identity)))

(ert-deftest machine/value-equal-constructors ()
  (should (tl-value-equal '(Pair 1 2) '(Pair 1 2) #'identity))
  (should-not (tl-value-equal '(Pair 1 2) '(Pair 1 3) #'identity))
  (should-not (tl-value-equal '(Pair 1 2) '(Cons 1 2) #'identity)))

(ert-deftest machine/true-value-p ()
  (should (tl-true-value-p 'True))
  (should-not (tl-true-value-p 'False)))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-make-thunk`.

- [ ] **Step 3: Implement `termlisp-machine.el`**

```elisp
;;; termlisp-machine.el --- Runtime objects and value helpers -*- lexical-binding: t; -*-

;;; Commentary:
;; Runtime values are: atoms (symbol/number/string), constructor values
;; (a symbol for nullary, or a list `(Con . fields)'), closures, function
;; objects, and thunks.  Constructor fields are stored as thunks (lazy).

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(cl-defstruct (tl-thunk (:constructor tl-make-thunk (expr env)))
  expr env (forced nil) (value nil) (busy nil))

(cl-defstruct (tl-closure (:constructor tl-make-closure (params body env)))
  params body env)

(cl-defstruct (tl-function (:constructor tl-make-function (clauses)))
  clauses)

(defun tl-value-equal (a b force)
  "Compare runtime values A and B structurally, forcing thunks with FORCE."
  (let ((a (funcall force a))
        (b (funcall force b)))
    (cond
     ((and (consp a) (consp b))
      (and (eq (car a) (car b))
           (tl-value-equal (cdr a) (cdr b) force)))
     ((or (consp a) (consp b)) nil)
     (t (equal a b)))))

(defun tl-true-value-p (v)
  "Return non-nil if V is the boolean constructor `True'."
  (eq v 'True))

(defun tl-lookup (name env)
  "Look up NAME in local ENV, then in the current environment's globals."
  (or (assq name env)
      (assq name (tl-env-globals termlisp--current-env))))

(provide 'termlisp-machine)
;;; termlisp-machine.el ends here
```

`tl-lookup` references `termlisp--current-env`, defined in `termlisp-eval.el`; add a forward declaration:

```elisp
(defvar termlisp--current-env)
```

at the top of `termlisp-machine.el` (after the requires).

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add termlisp-machine.el test/termlisp-test.el
git commit -m "feat: add runtime objects and value equality"
```

---

## Task 6: `termlisp-pattern.el` — pattern parse and match

**Files:**
- Create: `termlisp-pattern.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest pattern/parse-shapes ()
  (should (equal (tl-pattern-parse 'x) '(var . x)))
  (should (equal (tl-pattern-parse '_) '(wild)))
  (should (equal (tl-pattern-parse '(:literal foo)) '(lit foo)))
  (should (equal (tl-pattern-parse '(:list rest)) '(rest . rest)))
  (should (equal (tl-pattern-parse '(Pair a b))
                 '(con Pair (var . a) (var . b)))))

(defun tl-test-ctx ()
  (tl-make-match-ctx
   :force #'identity
   :lit-eval #'identity
   :guard-eval (lambda (e _b) e)
   :lambda-value #'identity))

(ert-deftest pattern/match-var ()
  (let* ((p (tl-pattern-parse 'x))
         (b (tl-match p 5 nil (tl-test-ctx))))
    (should (equal (cdr (assq 'x b)) 5))))

(ert-deftest pattern/match-wild ()
  (should (null (tl-match (tl-pattern-parse '_) 5 nil (tl-test-ctx)))))

(ert-deftest pattern/match-constructor ()
  (let* ((p (tl-pattern-parse '(Pair a b)))
         (b (tl-match p '(Pair 1 2) nil (tl-test-ctx))))
    (should (equal (cdr (assq 'a b)) 1))
    (should (equal (cdr (assq 'b b)) 2))))

(ert-deftest pattern/match-constructor-fail ()
  (should (null (tl-match (tl-pattern-parse '(Pair a b)) '(Cons 1 2)
                          nil (tl-test-ctx)))))

(ert-deftest pattern/match-nullary-constructor ()
  (should (tl-match (tl-pattern-parse '(True)) 'True nil (tl-test-ctx)))
  (should-not (tl-match (tl-pattern-parse '(True)) 'False nil (tl-test-ctx))))

(ert-deftest pattern/match-literal ()
  (should (tl-match (tl-pattern-parse '(:literal foo)) 'foo nil (tl-test-ctx)))
  (should-not (tl-match (tl-pattern-parse '(:literal foo)) 'bar nil (tl-test-ctx))))

(ert-deftest pattern/match-nonlinear ()
  (let* ((p (tl-pattern-parse '(Pair a a))))
    (should (tl-match p '(Pair 1 1) nil (tl-test-ctx)))
    (should-not (tl-match p '(Pair 1 2) nil (tl-test-ctx)))))

(ert-deftest pattern/match-rest ()
  (let* ((p (tl-pattern-parse '(:list rest)))
         (b (tl-match-seq (list p) '(1 2 3) nil (tl-test-ctx))))
    (should (equal (cdr (assq 'rest b)) '(1 2 3)))))

(ert-deftest pattern/match-guard ()
  (let* ((p (tl-pattern-parse '(guard x True)))
         (b (tl-match p 'anything nil (tl-test-ctx))))
    (should (equal (cdr (assq 'x b)) 'anything)))
  (let* ((p (tl-pattern-parse '(guard x False))))
    (should-not (tl-match p 'anything nil (tl-test-ctx)))))

(ert-deftest pattern/match-or ()
  (let ((p (tl-pattern-parse '(or (True) (False)))))
    (should (tl-match p 'True nil (tl-test-ctx)))
    (should (tl-match p 'False nil (tl-test-ctx)))
    (should-not (tl-match p 'Other nil (tl-test-ctx)))))
```

Note: `pattern/match-var` and `pattern/match-wild` return the bindings alist, which is `nil` when there are no bindings — so `match-wild`'s "success with empty env" is `nil`. To make success unambiguous, `tl-match` returns `(ok . bindings)` like `tl-unify`.

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-pattern-parse`.

- [ ] **Step 3: Implement `termlisp-pattern.el`**

```elisp
;;; termlisp-pattern.el --- Pattern parsing and matching -*- lexical-binding: t; -*-

;;; Commentary:
;; A compiled pattern is a list whose car is a tag:
;;   (wild)            match anything, bind nothing
;;   (var . NAME)      bind NAME
;;   (lit . EXPR)      compare with value of EXPR
;;   (con . (NAME . SUBPATTERNS))
;;   (rest . NAME)     bind remaining sequence elements
;;   (lam . NAME)      bind a function value
;;   (guard SUBPAT EXPR)
;;   (or PAT...)
;;   (and PAT...)
;; `tl-match' returns a cons `(ok . bindings)' or nil.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-machine)

(cl-defstruct (tl-match-ctx (:constructor tl-make-match-ctx))
  force lit-eval guard-eval lambda-value)

(defun tl-pattern-parse (pat)
  "Parse surface pattern PAT into a compiled pattern."
  (cond
   ((eq pat '_) '(wild))
   ((symbolp pat) (cons 'var pat))
   ((and (consp pat) (eq (car pat) :literal)) (list 'lit (cadr pat)))
   ((and (consp pat) (eq (car pat) :list)) (cons 'rest (cadr pat)))
   ((and (consp pat) (eq (car pat) :lambda)) (cons 'lam (cadr pat)))
   ((and (consp pat) (eq (car pat) 'guard))
    (list 'guard (tl-pattern-parse (nth 1 pat)) (nth 2 pat)))
   ((and (consp pat) (eq (car pat) 'or))
    (cons 'or (mapcar #'tl-pattern-parse (cdr pat))))
   ((and (consp pat) (eq (car pat) 'and))
    (cons 'and (mapcar #'tl-pattern-parse (cdr pat))))
   ((consp pat)
    (cons 'con (cons (car pat) (mapcar #'tl-pattern-parse (cdr pat)))))
   (t (signal 'termlisp-error (list (format "Bad pattern: %S" pat))))))

(defun tl-match (pat value bindings ctx)
  "Match compiled pattern PAT against VALUE, extending BINDINGS.
Return `(ok . bindings)'.  CTX provides force/lit-eval/guard-eval/lambda-value."
  (pcase (car pat)
    ('wild (cons t bindings))
    ('var
     (let* ((name (cdr pat))
            (cell (assq name bindings)))
       (if cell
           (if (tl-value-equal (cdr cell) value (tl-match-ctx-force ctx))
               (cons t bindings)
             nil)
         (cons t (cons (cons name value) bindings)))))
    ('lit
     (let ((expected (funcall (tl-match-ctx-lit-eval ctx) (cadr pat))))
       (if (tl-value-equal expected value (tl-match-ctx-force ctx))
           (cons t bindings)
         nil)))
    ('con
     (let* ((name (cadr pat))
            (subpats (cddr pat))
            (v (funcall (tl-match-ctx-force ctx) value)))
       (cond
        ((null subpats)
         (when (eq v name) (cons t bindings)))
        ((and (consp v) (eq (car v) name))
         (tl-match-seq subpats (cdr v) bindings ctx))
        (t nil))))
    ('lam
     (cons t (cons (cons (cdr pat)
                         (funcall (tl-match-ctx-lambda-value ctx) value))
                   bindings)))
    ('guard
     (let ((r (tl-match (nth 1 pat) value bindings ctx)))
       (when r
         (let ((g (funcall (tl-match-ctx-guard-eval ctx) (nth 2 pat) (cdr r))))
           (when (tl-true-value-p g) r)))))
    ('or
     (let ((pats (cdr pat)) (result nil))
       (while (and pats (not result))
         (setq result (tl-match (car pats) value bindings ctx))
         (setq pats (cdr pats)))
       result))
    ('and
     (let ((pats (cdr pat)) (r (cons t bindings)) (ok t))
       (while (and pats ok)
         (setq r (tl-match (car pats) value (cdr r) ctx))
         (unless r (setq ok nil))
         (setq pats (cdr pats)))
       (when ok r)))
    (_ (signal 'termlisp-error (list (format "Bad compiled pattern: %S" pat))))))

(defun tl-match-seq (pats values bindings ctx)
  "Match PATS against VALUES; exact arity unless a `rest' pattern is present."
  (let ((ok t) (pats pats) (values values) (bindings bindings))
    (while (and pats ok)
      (let ((pat (car pats)))
        (if (eq (car pat) 'rest)
            (progn
              (setq bindings (cons (cons (cdr pat) values) bindings))
              (setq pats nil values nil))
          (if (null values)
              (setq ok nil)
            (let ((r (tl-match pat (car values) bindings ctx)))
              (if r
                  (progn (setq bindings (cdr r))
                         (setq values (cdr values))
                         (setq pats (cdr pats)))
                (setq ok nil)))))))
    (when (and ok (null pats) (null values))
      (cons t bindings))))

(provide 'termlisp-pattern)
;;; termlisp-pattern.el ends here
```

Update the tests to the cons contract. The `match-var`/`wild`/`literal` tests need `(car ...)`:

```elisp
(ert-deftest pattern/match-var ()
  (let* ((p (tl-pattern-parse 'x))
         (r (tl-match p 5 nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'x (cdr r))) 5))))

(ert-deftest pattern/match-wild ()
  (should (car (tl-match (tl-pattern-parse '_) 5 nil (tl-test-ctx)))))

(ert-deftest pattern/match-constructor ()
  (let* ((p (tl-pattern-parse '(Pair a b)))
         (r (tl-match p '(Pair 1 2) nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'a (cdr r))) 1))
    (should (equal (cdr (assq 'b (cdr r))) 2))))

(ert-deftest pattern/match-nullary-constructor ()
  (should (car (tl-match (tl-pattern-parse '(True)) 'True nil (tl-test-ctx))))
  (should-not (tl-match (tl-pattern-parse '(True)) 'False nil (tl-test-ctx))))

(ert-deftest pattern/match-literal ()
  (should (car (tl-match (tl-pattern-parse '(:literal foo)) 'foo nil (tl-test-ctx))))
  (should-not (tl-match (tl-pattern-parse '(:literal foo)) 'bar nil (tl-test-ctx))))

(ert-deftest pattern/match-nonlinear ()
  (let* ((p (tl-pattern-parse '(Pair a a))))
    (should (car (tl-match p '(Pair 1 1) nil (tl-test-ctx))))
    (should-not (tl-match p '(Pair 1 2) nil (tl-test-ctx)))))

(ert-deftest pattern/match-rest ()
  (let* ((p (tl-pattern-parse '(:list rest)))
         (r (tl-match-seq (list p) '(1 2 3) nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'rest (cdr r))) '(1 2 3)))))

(ert-deftest pattern/match-guard ()
  (let* ((p (tl-pattern-parse '(guard x True)))
         (r (tl-match p 'anything nil (tl-test-ctx))))
    (should (car r))
    (should (equal (cdr (assq 'x (cdr r))) 'anything)))
  (should-not (tl-match (tl-pattern-parse '(guard x False)) 'anything nil (tl-test-ctx))))

(ert-deftest pattern/match-or ()
  (let ((p (tl-pattern-parse '(or (True) (False)))))
    (should (car (tl-match p 'True nil (tl-test-ctx))))
    (should (car (tl-match p 'False nil (tl-test-ctx))))
    (should-not (tl-match p 'Other nil (tl-test-ctx)))))
```

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add termlisp-pattern.el test/termlisp-test.el
git commit -m "feat: add pattern parse and match"
```

---

## Task 7: `termlisp-builtins.el` — primitive functions

**Files:**
- Create: `termlisp-builtins.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest builtins/registry ()
  (should (tl-builtin-p 'eq))
  (should (tl-builtin-p '+))
  (should-not (tl-builtin-p 'nope)))

(ert-deftest builtins/eq ()
  (should (eq (funcall (gethash 'eq tl-builtins) '(1 1)) 'True))
  (should (eq (funcall (gethash 'eq tl-builtins) '(1 2)) 'False)))

(ert-deftest builtins/arith ()
  (should (= (funcall (gethash '+ tl-builtins) '(2 3)) 5))
  (should (= (funcall (gethash '- tl-builtins) '(7 3)) 4))
  (should (= (funcall (gethash '* tl-builtins) '(2 3)) 6))
  (should (eq (funcall (gethash '< tl-builtins) '(1 2)) 'True)))
```

Here the builtin functions receive **already-forced** values (the evaluator forces arguments before calling builtins). This keeps builtins simple and strict.

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function tl-builtin-p`.

- [ ] **Step 3: Implement `termlisp-builtins.el`**

```elisp
;;; termlisp-builtins.el --- Primitive functions -*- lexical-binding: t; -*-

;;; Commentary:
;; Builtins receive a list of already-forced argument values.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(defvar tl-builtins (make-hash-table :test #'eq)
  "Registry mapping builtin names to functions of a list of values.")

(defun tl-builtin-p (name)
  "Return non-nil if NAME is a builtin."
  (gethash name tl-builtins))

(defun tl-register-builtin (name fn)
  "Register builtin NAME implemented by FN."
  (puthash name fn tl-builtins))

(defun tl-bool (b) (if b 'True 'False))

(tl-register-builtin 'eq
  (lambda (args) (tl-bool (equal (nth 0 args) (nth 1 args)))))
(tl-register-builtin '+
  (lambda (args) (+ (nth 0 args) (nth 1 args))))
(tl-register-builtin '-
  (lambda (args) (- (nth 0 args) (nth 1 args))))
(tl-register-builtin '*
  (lambda (args) (* (nth 0 args) (nth 1 args))))
(tl-register-builtin '<
  (lambda (args) (tl-bool (< (nth 0 args) (nth 1 args)))))

(provide 'termlisp-builtins)
;;; termlisp-builtins.el ends here
```

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add termlisp-builtins.el test/termlisp-test.el
git commit -m "feat: add primitive builtins"
```

---

## Task 8: `termlisp-eval.el` — evaluator core (lazy, TCO)

**Files:**
- Create: `termlisp-eval.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(require 'termlisp-eval)

(ert-deftest eval/atom-and-symbol ()
  (should (equal (termlisp-eval "42") 42))
  (should (eq (termlisp-eval "Foo") 'Foo)))

(ert-deftest eval/constant ()
  (should (equal (termlisp-eval "(define x 5) x") 5)))

(ert-deftest eval/lambda-immediate ()
  (should (equal (termlisp-eval "((lambda (x) x) 42)") 42)))

(ert-deftest eval/constructor-lazy ()
  (should (equal (termlisp-value->string (termlisp-eval "(Pair 1 2)"))
                 "(Pair 1 2)")))

(ert-deftest eval/tco-deep-recursion ()
  "A tail-recursive loop of 100000 iterations must not overflow."
  (should (= (termlisp-eval
              "(define (loop n acc)
                 (if (eq n 0) acc (loop (- n 1) (+ acc 1))))
               (loop 100000 0)")
             100000)))

(ert-deftest eval/laziness-shares ()
  "A forced thunk is memoized: the counter increments once."
  (should (= (termlisp-eval
              "(define (id x) x)
               (define (bump n) (+ n 1))
               (+ (id (bump 0)) (id (bump 0)))")
             2)))
```

The laziness test above is weak (it does not actually observe sharing). A stronger test is added in Task 11.

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function termlisp-eval`.

- [ ] **Step 3: Implement `termlisp-eval.el`**

```elisp
;;; termlisp-eval.el --- Evaluator -*- lexical-binding: t; -*-

;;; Commentary:
;; CEK-style evaluator.  Function application is a tail call in the driver
;; loop (TCO); arguments become memoized thunks forced on demand (laziness).

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-reader)
(require 'termlisp-machine)
(require 'termlisp-pattern)
(require 'termlisp-builtins)

(defvar termlisp--current-env nil
  "Dynamically bound evaluation context during `tl-run'.")

;;; Thunks ---------------------------------------------------------------

(defun tl-force (value)
  "Force VALUE to weak head normal form; memoize if it is a thunk."
  (cond
   ((not (tl-thunk-p value)) value)
   ((tl-thunk-forced-p value) (tl-thunk-value value))
   ((tl-thunk-busy-p value)
    (signal 'termlisp-eval-error '("<<loop>> detected while forcing a thunk")))
   (t
    (setf (tl-thunk-busy-p value) t)
    (let ((v (tl-run (tl-thunk-expr value) (tl-thunk-env value))))
      (setf (tl-thunk-value value) v)
      (setf (tl-thunk-forced-p value) t)
      (setf (tl-thunk-busy-p value) nil)
      v))))

(defun tl-make-arg-thunks (exprs env)
  "Turn argument expressions EXPRS into thunks capturing ENV."
  (mapcar (lambda (e) (tl-make-thunk e env)) exprs))

;;; Lambda application ---------------------------------------------------

(defun tl-bind-params (params args base-env caller-env)
  "Extend BASE-ENV binding PARAMS to thunks of ARGS evaluated in CALLER-ENV."
  (let ((new base-env) (params params) (args args))
    (while params
      (push (cons (car params) (tl-make-thunk (car args) caller-env)) new)
      (setq params (cdr params) args (cdr args)))
    new))

;;; Clause selection -----------------------------------------------------

(cl-defstruct (tl-clause (:constructor tl-make-clause (name params body)))
  name params body)

(defun tl-match-ctx-for-eval ()
  "Build a match context that forces thunks and evaluates literals/guards."
  (tl-make-match-ctx
   :force #'tl-force
   :lit-eval (lambda (expr) (tl-run expr nil))
   :guard-eval (lambda (expr bindings) (tl-run expr bindings))
   :lambda-value
   (lambda (value)
     (let ((v (tl-force value)))
       (cond
        ((tl-closure-p v) v)
        ((tl-function-p v) v)
        ((and (symbolp v)
              (gethash v (tl-env-functions termlisp--current-env)))
         (tl-make-function (gethash v (tl-env-functions termlisp--current-env))))
        (t v))))))

(defun tl-select-clause (clauses arg-thunks)
  "Return `(clause . bindings)' for the first matching CLAUSES, or nil."
  (let ((ctx (tl-match-ctx-for-eval)) (result nil))
    (while (and clauses (not result))
      (let ((r (tl-match-seq (tl-clause-params (car clauses))
                             arg-thunks nil ctx)))
        (when r
          (setq result (cons (car clauses) (cdr r)))))
      (setq clauses (cdr clauses)))
    result))

;;; The driver -----------------------------------------------------------

(defun tl-run (expr env)
  "Evaluate EXPR in lexical ENV to weak head normal form."
  (let ((control expr)
        (cenv env)
        (result nil)
        (done nil)
        (fuel (or (tl-env-option termlisp--current-env :fuel) 100000)))
    (while (not done)
      (when (<= fuel 0)
        (signal 'termlisp-eval-error '("fuel exhausted")))
      (setq fuel (1- fuel))
      (cond
       ((symbolp control)
        (let ((cell (tl-lookup control cenv)))
          (if cell
              (setq result (tl-force (cdr cell)) done t)
            (setq result control done t))))
       ((atom control) (setq result control done t))
       ((consp control)
        (let ((head (car control)) (args (cdr control)))
          (cond
           ;; ((lambda (params) body) args...)
           ((and (consp head) (eq (car head) 'lambda))
            (setq cenv (tl-bind-params (cadr head) args cenv cenv))
            (setq control (caddr head)))
           ;; (name args...)
           ((symbolp head)
            (let ((cell (assq head cenv))
                  (global (assq head (tl-env-globals termlisp--current-env)))
                  (fns (gethash head (tl-env-functions termlisp--current-env))))
              (cond
               ((or cell global)
                (let ((v (tl-force (cdr (or cell global)))))
                  (cond
                   ((tl-closure-p v)
                    (setq cenv (tl-bind-params (tl-closure-params v) args
                                               (tl-closure-env v) cenv))
                    (setq control (tl-closure-body v)))
                   ((tl-function-p v)
                    (let ((sel (tl-select-clause (tl-function-clauses v)
                                                 (tl-make-arg-thunks args cenv))))
                      (if sel
                          (progn (setq cenv (cdr sel))
                                 (setq control (tl-clause-body (car sel))))
                        (signal 'termlisp-eval-error
                                (list (format "No matching clause for %S" head))))))
                   (t (signal 'termlisp-eval-error
                              (list (format "Not a function: %S" head)))))))
               (fns
                (let ((sel (tl-select-clause fns (tl-make-arg-thunks args cenv))))
                  (if sel
                      (progn (setq cenv (cdr sel))
                             (setq control (tl-clause-body (car sel))))
                    (signal 'termlisp-eval-error
                            (list (format "No matching clause for %S with %S"
                                          head (mapcar #'termlisp-value->string args)))))))
               ((tl-builtin-p head)
                (setq result (funcall (gethash head tl-builtins)
                                      (mapcar #'tl-force (tl-make-arg-thunks args cenv)))
                      done t))
               (t
                (setq result
                      (if args
                          (cons head (tl-make-arg-thunks args cenv))
                        head)
                      done t)))))
           ;; ((f ...) args...) — evaluate head, then apply
           (t
            (let ((fv (tl-run head cenv)))
              (cond
               ((tl-closure-p fv)
                (setq cenv (tl-bind-params (tl-closure-params fv) args
                                           (tl-closure-env fv) cenv))
                (setq control (tl-closure-body fv)))
               ((tl-function-p fv)
                (let ((sel (tl-select-clause (tl-function-clauses fv)
                                             (tl-make-arg-thunks args cenv))))
                  (if sel
                      (progn (setq cenv (cdr sel))
                             (setq control (tl-clause-body (car sel))))
                    (signal 'termlisp-eval-error
                            (list (format "No matching clause for %S" head))))))
               (t (signal 'termlisp-eval-error
                          (list (format "Not a function: %S"
                                        (termlisp-value->string fv))))))))))))
    result))

;;; Formatting -----------------------------------------------------------

(defun termlisp-value->string (v)
  "Render runtime value V as a string, forcing thunks."
  (let ((v (if (tl-thunk-p v) (tl-force v) v)))
    (cond
     ((consp v)
      (concat "(" (mapconcat #'termlisp-value->string v " ") ")"))
     ((tl-closure-p v) "#<closure>")
     ((tl-function-p v) "#<function>")
     (t (format "%s" v)))))

(provide 'termlisp-eval)
;;; termlisp-eval.el ends here
```

- [ ] **Step 4: Run test to verify it fails for the right reason**

Run: `make test`
Expected: FAIL — `void-function termlisp-eval` (top-level API not defined yet). This is expected; Task 9 adds it. Temporarily, to exercise `tl-run`, add these two tests using `tl-run` directly:

```elisp
(ert-deftest eval/run-atom ()
  (let ((termlisp--current-env (termlisp-make-env)))
    (should (equal (tl-run 42 nil) 42))))

(ert-deftest eval/run-lambda ()
  (let ((termlisp--current-env (termlisp-make-env)))
    (should (equal (tl-run '((lambda (x) x) 42) nil) 42))))
```

Run: `make test`
Expected: PASS for the `eval/run-*` tests; the `termlisp-eval` tests still fail until Task 9.

- [ ] **Step 5: Commit**

```bash
git add termlisp-eval.el test/termlisp-test.el
git commit -m "feat: add lazy TCO evaluator core"
```

---

## Task 9: `termlisp-eval.el` — top-level forms and public API

**Files:**
- Modify: `termlisp-eval.el`
- Create: `termlisp.el`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest eval/define-function ()
  (should (equal (termlisp-eval "(define (id x) x) (id 42)") 42)))

(ert-deftest eval/if-clauses ()
  (should (eq (termlisp-eval
               "(datatype Bool (True) (False))
                (define (if (True) a b) a)
                (define (if (False) a b) b)
                (if True yes no)")
              'yes)))

(ert-deftest eval/pattern-destructure ()
  (should (eq (termlisp-eval
               "(datatype Pair (Pair a b))
                (define (fst (Pair a b)) a)
                (fst (Pair hello world))")
              'hello)))

(ert-deftest eval/open-constructor ()
  "Undeclared names are open constructors."
  (should (equal (termlisp-value->string (termlisp-eval "(Foo 1 (Bar 2))"))
                 "(Foo 1 (Bar 2))")))

(ert-deftest eval/match-failure-signals ()
  (should-error (termlisp-eval "(define (f (True)) 1) (f (False))")
                :type 'termlisp-eval-error))

(ert-deftest eval/annotations-ignored ()
  (should (equal (termlisp-eval "(: id (a -> a)) (define (id x) x) (id 7)") 7)))

(ert-deftest api/value->string ()
  (should (equal (termlisp-value->string '(Pair 1 2)) "(Pair 1 2)"))
  (should (equal (termlisp-value->string 'Foo) "Foo")))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — `void-function termlisp-eval`.

- [ ] **Step 3: Add top-level evaluation to `termlisp-eval.el`**

Insert before `(provide 'termlisp-eval)`:

```elisp
;;; Top-level forms ------------------------------------------------------

(defun tl-eval-define (env form)
  "Handle a top-level `define' FORM in ENV."
  (let ((target (cadr form)))
    (if (consp target)
        ;; (define (name params...) body)
        (let* ((name (car target))
               (params (mapcar #'tl-pattern-parse (cdr target)))
               (clause (tl-make-clause name params (caddr form))))
          (puthash name
                   (append (gethash name (tl-env-functions env)) (list clause))
                   (tl-env-functions env))
          name)
      ;; (define name expr)
      (let ((value (tl-run (caddr form) nil)))
        (setf (tl-env-globals env)
              (cons (cons target value) (tl-env-globals env)))
        value))))

(defun tl-eval-datatype (env form)
  "Handle `(datatype [open] NAME (CON ARGTYPE...) ...)' in ENV."
  (let* ((rest (cdr form))
         (open (eq (car rest) 'open))
         (rest (if open (cdr rest) rest))
         (name (car rest))
         (ctors (cdr rest)))
    (puthash name (list :open open :constructors (mapcar #'car ctors))
             (tl-env-datatypes env))
    (dolist (ctor ctors)
      (puthash (car ctor) name (tl-env-constructors env)))
    name))

(defun tl-eval-datatype-extension (env form)
  "Handle `(datatype-extension NAME (CON ARGTYPE...) ...)' in ENV."
  (let* ((name (cadr form))
         (ctors (cddr form))
         (existing (gethash name (tl-env-datatypes env))))
    (unless (and existing (plist-get existing :open))
      (signal 'termlisp-eval-error
              (list (format "Cannot extend non-open datatype %S" name))))
    (puthash name
             (plist-put existing :constructors
                        (append (plist-get existing :constructors)
                                (mapcar #'car ctors)))
             (tl-env-datatypes env))
    (dolist (ctor ctors)
      (puthash (car ctor) name (tl-env-constructors env)))
    name))

(defun tl-eval-top (env form)
  "Evaluate one top-level FORM in ENV."
  (cond
   ((and (consp form) (eq (car form) 'define)) (tl-eval-define env form))
   ((and (consp form) (eq (car form) 'datatype)) (tl-eval-datatype env form))
   ((and (consp form) (eq (car form) 'datatype-extension))
    (tl-eval-datatype-extension env form))
   ((and (consp form) (eq (car form) ':)) nil) ; annotations parsed in Plan 2
   (t (tl-run form nil))))

(defun termlisp-eval (string &optional env)
  "Parse and evaluate STRING in ENV (creating a fresh env if nil)."
  (let* ((env (or env (termlisp-make-env)))
         (termlisp--current-env env)
         (result nil))
    (dolist (form (termlisp-parse string) result)
      (setq result (tl-eval-top env form)))))

(defun termlisp-eval-file (file &optional env)
  "Evaluate the contents of FILE in ENV."
  (termlisp-eval (with-temp-buffer
                   (insert-file-contents file)
                   (buffer-string))
                 env))

(defun termlisp-load-prelude (&optional env)
  "Load the bundled prelude into ENV."
  (termlisp-eval-file
   (expand-file-name "termlisp-prelude.tlsp"
                     (file-name-directory (or load-file-name buffer-file-name)))
   env))
```

- [ ] **Step 4: Add the public API stub to `termlisp.el`**

`termlisp.el` already exists from Task 1 (conditional loader). Append the
`termlisp-typecheck` stub before the `(provide 'termlisp)` line:

```elisp
(defun termlisp-typecheck (string &optional env)
  "Typecheck STRING in ENV.  Implemented in Plan 2; returns ENV for now."
  (ignore string)
  (or env (termlisp-make-env)))
```

- [ ] **Step 5: Run test to verify it passes**

Run: `make test`
Expected: PASS (all tests).

- [ ] **Step 6: Commit**

```bash
git add termlisp-eval.el termlisp.el test/termlisp-test.el
git commit -m "feat: add top-level forms and public API"
```

---

## Task 10: Prelude MVP and example

**Files:**
- Create: `termlisp-prelude.tlsp`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest prelude/booleans ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(if True 1 2)" env) 1))
    (should (eq (termlisp-eval "(if False 1 2)" env) 2))
    (should (eq (termlisp-eval "(not True)" env) 'False))
    (should (eq (termlisp-eval "(and True False)" env) 'False))
    (should (eq (termlisp-eval "(or True False)" env) 'True))))

(ert-deftest prelude/pairs ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(car (cons A B))" env) 'A))
    (should (eq (termlisp-eval "(cdr (cons A B))" env) 'B))))

(ert-deftest prelude/peano ()
  (let ((env (termlisp-load-prelude)))
    (should (equal (termlisp-value->string (termlisp-eval "(plus two two)" env))
                   "(Succ (Succ (Succ (Succ Zero))))"))))

(ert-deftest prelude/map-lambda ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval "(map Foo (lambda (a) (Wrap a)))" env)
                '(Wrap Foo)))))
```

- [ ] **Step 2: Run test to verify it fails**

Run: `make test`
Expected: FAIL — prelude file missing / `car` unbound.

- [ ] **Step 3: Write `termlisp-prelude.tlsp`**

```lisp
;;; term-lisp prelude (Plan 1 MVP)

;; Booleans
(datatype Bool (True) (False))
(define true True)
(define false False)

(define (if (True) a b) a)
(define (if (False) a b) b)
(define (not (True)) (False))
(define (not (False)) (True))
(define (and (True) (True)) (True))
(define (and (True) (False)) (False))
(define (and (False) a) (False))
(define (or (True) a) (True))
(define (or (False) (True)) (True))
(define (or (False) (False)) (False))

;; Pairs
(datatype Pair (Pair a b))
(define (cons a b) (Pair a b))
(define (car (Pair a b)) a)
(define (cdr (Pair a b)) b)

;; Peano naturals
(datatype Nat (Zero) (Succ Nat))
(define zero Zero)
(define one (Succ Zero))
(define two (Succ (Succ Zero)))
(define (plus Zero b) b)
(define (plus (Succ a) b) (Succ (plus a b)))

;; Higher-order: map over one argument with a passed function
(define (map a (:lambda fun)) (fun a))
```

- [ ] **Step 4: Run test to verify it passes**

Run: `make test`
Expected: PASS.

If `prelude/map-lambda` fails because `:lambda` receives `(lambda (a) (Wrap a))` whose forced value is a closure and `fun` is bound to it, verify `tl-match-ctx-for-eval`'s `:lambda-value` returns the closure unchanged. Debug before proceeding.

- [ ] **Step 5: Commit**

```bash
git add termlisp-prelude.tlsp test/termlisp-test.el
git commit -m "feat: add Plan 1 prelude MVP"
```

---

## Task 11: Dedicated laziness and TCO tests

**Files:**
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the failing tests**

```elisp
(ert-deftest laziness/unused-argument-not-evaluated ()
  "An argument to a function that ignores it is never forced.
`boom' diverges, so eager argument evaluation would exhaust fuel."
  (should (eq (termlisp-eval
               "(define (const a b) a)
                (define (boom x) (boom x))
                (const 1 (boom 0))")
             1)))

(ert-deftest laziness/sharing-via-memoization ()
  "A thunk bound to a name is forced at most once.
We observe this by counting side effects through a builtin."
  (let ((count 0))
    (tl-register-builtin 'tick
      (lambda (_args) (setq count (1+ count)) 'True))
    (termlisp-eval
     "(define (dup x) (Pair x x))
      (define (used p) (eq (car p) (cdr p)))
      (used (dup (tick)))")
    (should (= count 1))))

(ert-deftest tco/mutual-recursion ()
  "Mutually recursive tail calls must not overflow."
  (should (eq (termlisp-eval
               "(define (evenp n) (if (eq n 0) True (oddp (- n 1))))
                (define (oddp n) (if (eq n 0) False (evenp (- n 1))))
                (evenp 100000)")
              'True)))

(ert-deftest tco/large-accumulator ()
  (should (= (termlisp-eval
              "(define (sum n acc)
                 (if (eq n 0) acc (sum (- n 1) (+ acc n))))
               (sum 10000 0)")
             50005000)))
```

- [ ] **Step 2: Run tests**

Run: `make test`
Expected: PASS. If `unused-argument-not-evaluated` errors, argument thunks are being forced eagerly — user-function application must build thunks, not force them. If `sharing-via-memoization` yields a count other than 1, `tl-force` is not memoizing the shared variable thunk.

- [ ] **Step 3: Fix any failures**

Common fixes:
- If `unused-argument-not-evaluated` fails: ensure `tl-run` builds arg thunks (not forced) for user function clauses.
- If sharing fails: ensure `tl-force` memoizes (it does) and that constructor fields store the same thunk object when the same variable is used twice. In `(define (dup x) (Pair x x))`, the body `(Pair x x)` builds constructor fields as thunks of `x`; both fields are separate thunks whose expression is `x` and env is the clause env. Forcing each resolves `x` to the same thunk via `tl-lookup` and forces it, hitting the memo. So count is 1.

- [ ] **Step 4: Run tests to verify they pass**

Run: `make test`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add test/termlisp-test.el
git commit -m "test: add laziness and TCO coverage"
```

---

## Task 12: Example programs and acceptance test

**Files:**
- Create: `examples/bool.tlsp`
- Create: `examples/nat.tlsp`
- Test: `test/termlisp-test.el` (append)

- [ ] **Step 1: Write the example files**

`examples/bool.tlsp`:

```lisp
(if (eq (a b) (a b)) booleans-work booleans-differ)
```

`examples/nat.tlsp`:

```lisp
(datatype Nat (Zero) (Succ Nat))
(define (pred (Succ n)) n)
(define (plus Zero b) b)
(define (plus (Succ a) b) (Succ (plus a b)))
(plus (Succ (Succ Zero)) (Succ Zero))
```

- [ ] **Step 2: Write the acceptance test**

```elisp
(ert-deftest acceptance/examples ()
  (let ((env (termlisp-load-prelude)))
    (should (eq (termlisp-eval-file
                 (expand-file-name "examples/bool.tlsp"
                                   (file-name-directory (locate-library "termlisp")))
                 env)
                'booleans-work))
    (should (equal (termlisp-value->string
                    (termlisp-eval-file
                     (expand-file-name "examples/nat.tlsp"
                                       (file-name-directory (locate-library "termlisp")))
                     env))
                   "(Succ (Succ (Succ Zero)))"))))
```

- [ ] **Step 3: Run test to verify it passes**

Run: `make test`
Expected: PASS.

- [ ] **Step 4: Byte-compile check**

Run: `make compile`
Expected: no errors. Fix any warnings about undefined functions by adding `declare-function` forms.

- [ ] **Step 5: Commit**

```bash
git add examples test/termlisp-test.el
git commit -m "test: add example programs and acceptance test"
```

---

## Self-Review

**Spec coverage (Plan 1 slice):**
- §4 module layout: base, reader, unify, machine, pattern, builtins, eval, prelude — covered. `syntax.el`, `elaborate.el`, `types.el`, `monad.el`, `data-reader.el` deferred to Plans 2–4 as designed.
- §5 surface syntax: `define`, `datatype`, `datatype open`, `datatype-extension`, `:`, patterns (var/wild/literal/list/lambda/guard/or/and), lambda — covered.
- §6 S-exp terms, lazy constructor fields, open datatypes — covered.
- §9 unification kernel + pattern matching — covered (non-linear, backtracking via `or`, failure as signal).
- §10 CEK/TCO/laziness — covered by `tl-run` + thunks.
- §12 API: `termlisp-make-env`, `termlisp-eval`, `termlisp-eval-file`, `termlisp-parse`, `termlisp-load-prelude`, `termlisp-value->string` — covered. `termlisp-typecheck` stubbed for Plan 2.
- §13 tests: reader, unify, patterns, laziness, TCO, prelude — covered.

**Deferred (tracked):**
- peg sub-grammar for type/pattern expressions (Plan 2, when types exist).
- backtracking as a `List` monad choice point (Plan 3); Plan 1 uses clause retry + `or` patterns.
- cats usage in the evaluator (Plan 3), since Plan 1 keeps the hot loop plain for correctness first.
- guard/or/and are implemented and tested but `and` returning `(ok . bindings)` is used as truthy — verify in Task 6 tests (done).

**Type/name consistency:** `tl-env`, `tl-thunk`, `tl-closure`, `tl-function`, `tl-clause`, `tl-match-ctx`, `tl-lvar` are defined once and used consistently. `tl-match`/`tl-match-seq`/`tl-unify` all return `(ok . bindings)`.
