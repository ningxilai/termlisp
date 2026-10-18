;;; termlisp-ir-types.el --- HM typing for the lowering IR -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; The Aldor lowering emits termlisp surface forms that carry statement
;; and data constructors (`Seq', `Let', `Setq', `While', `if', `Record',
;; `ArrayRef', ...).  `tl-infer' does not know these, so this module adds
;; typing rules for them and registers type schemes for the IR primitives
;; and runtime helpers.  With that, `tl-infer' becomes a type oracle for
;; the lowered IR -- the basis for type-directed decisions such as which
;; locals may be substituted and which are references/handles.
;;
;; Types reuse the HM representation (`tl-tcon'); statements have type
;; `Unit'.  Locals are monomorphic within a body (matching the IR, whose
;; variables are pre-bound and then mutated with `Setq').

;;; Code:

(require 'cl-lib)
(require 'termlisp-types)

(defun tl-tunit () (tl-tcon 'Unit nil))
(defun tl-tchar () (tl-tcon 'Char nil))
(defun tl-tlist (a) (tl-tcon 'List (list a)))
(defun tl-tvector (a) (tl-tcon 'Array (list a)))
(defun tl-trecord (args) (tl-tcon 'Record args))
(defun tl-tunion (a) (tl-tcon 'Union (list a)))

(defun tl-ir-unify (a b bindings)
  "Unify A and B under BINDINGS, signalling on mismatch.
In oracle mode (`tl-type-lenient') a mismatch leaves BINDINGS unchanged."
  (let ((r (tl-unify-types a b bindings)))
    (if (car r)
        (cdr r)
      (if tl-type-lenient
          bindings
        (signal 'termlisp-type-error
                (list (format "IR type mismatch: %S vs %S"
                              (tl-apply-bindings a bindings)
                              (tl-apply-bindings b bindings))))))))

(defun tl-ir-expect (env bindings expr ty)
  "Infer EXPR in ENV under BINDINGS and unify its type with TY.
Return the extended bindings."
  (let ((r (tl-infer (tl-zonk-env env bindings) expr)))
    (tl-ir-unify ty (car r) (tl-compose-bindings bindings (cdr r)))))

;;; Sequences and bindings.

(defun tl-ir-infer-seq (env exprs bindings)
  "Infer EXPRS left to right; return (TYPE . BINDINGS) of the last."
  (if (null exprs)
      (cons (tl-tunit) bindings)
    (let ((b bindings) (ty (tl-tunit)))
      (dolist (e exprs)
        (let ((r (tl-infer (tl-zonk-env env b) e)))
          (setq b (tl-compose-bindings b (cdr r)))
          (setq ty (tl-apply-bindings (car r) b))))
      (cons ty b))))

(defun tl-infer-ir-Seq (env expr)
  (tl-ir-infer-seq env (cdr expr) nil))

(defun tl-infer-ir-Let (env expr)
  "Infer `(Let ((NAME EXPR) ...) BODY...)'.
During dictionary-passing elaboration a binding whose type generalizes
with class constraints is recorded in `tl-elab-let-dicts' and bound
polymorphically so its dictionary can be abstracted.  Everywhere else the
value restriction decides, via `tl-ir-bind-let-binding'."
  (let ((b nil) (env2 env))
    (dolist (binding (nth 1 expr))
      (let* ((name (car binding))
             (tl-infer-constraints nil)
             (r (tl-infer (tl-zonk-env env b) (cadr binding)))
             (ty (tl-apply-bindings (car r) b)))
        (setq b (tl-compose-bindings b (cdr r)))
        (setq env2
              (tl-tenv-extend
               env2
               (list (cons name
                           (tl-ir-bind-let-binding env binding ty b)))))))
    (tl-ir-infer-seq env2 (cddr expr) b)))

(defun tl-ir-bind-let-binding (env binding ty bindings)
  "Choose the type-environment entry for `Let' BINDING, inferred as TY.
The value restriction decides, and it decides the same way under
elaboration as under plain checking -- that is the point of asking it
here rather than inside either branch.  A syntactic value, an atom or a
lambda, has not run anything yet, so nothing but its type can still
change and the variables it introduced inside this scope are safe to
quantify over.  Anything else is an application, and an application is
where an effect would already have happened, so it stays monomorphic and
every use of it agrees.  Generalizing unconditionally while elaborating
would make one program polymorphic under `:elaborate' and monomorphic
under `:type-check', decided by a flag with nothing to do with the
program -- the same fault that made the elaborator rewrite `let' into a
lambda application.  During elaboration a binding that does generalize is
recorded in `tl-elab-let-dicts', so its dictionary can be abstracted.

BINDINGS, the constraints accumulated so far, go to
`tl-ir-generalize-binding' so what the binding's own constraints imply is
solved against the bindings that produced them -- the same way
`tl-infer-constant' closes a definition.  STRICT drops while elaborating,
which has always swallowed an unsolved constraint there; letting it
signal is the behavior `tl-infer-constant' shows for a definition."
  (if (tl-syntactic-value-p (cadr binding))
      (tl-ir-generalize-binding env binding ty bindings (not tl-elab-active))
    ty))

(defun tl-ir-generalize-binding (env binding ty &optional bindings strict)
  "Generalize a `Let' BINDING of type TY; record its dictionary parameters.
Return a scheme, or TY unchanged when it does not generalize -- a
binding with nothing to quantify and nothing to retain keeps the type it
already had.  A closed scheme would say nothing, and would only make the
binding opaque to `tl-infer-ir-Setq', which has to be able to tell a
genuinely polymorphic accumulator from an ordinary loop variable.

BINDINGS, the constraints accumulated so far, close against what the
binding's own constraints imply; nil is what the elaborating caller has
always passed.  With STRICT, an unsolved ground constraint signals
instead of being swallowed -- a constraint with no instance is a claim
the program never proved, and dropping it would let the binding keep a
type whose evidence does not exist."
  (let* ((base (tl-tenv-base env))
         ;; Which variables are generalizable here is a question about
         ;; *time*, not about the environment: one asked of the levels
         ;; the variables carry.  It used to be asked of the environment
         ;; instead, and that was unsound -- the environment consulted
         ;; was the type environment, which does not mention a lambda's
         ;; own parameters, so `y''s type variable looked like something
         ;; no one else could be using and `z' was quantified over it:
         ;;
         ;;   (define (h y) (Let ((z y)) (let ((u (z 1))) (z "s"))))
         ;;
         ;; came out accepted, `z' having become `forall a. a' inside a
         ;; scope where `y' is still an ordinary parameter.  A variable
         ;; created before this scope opened cannot be generalized here,
         ;; whatever the environment does or does not say about it.
         (gen-vars (tl-generalized-vars ty))
         (kept (condition-case err
                   (tl-close-constraints base gen-vars tl-infer-constraints
                                         bindings)
                 (error (when strict (signal (car err) (cdr err)))))))
    (when kept
      (let ((dicts (cl-loop for c in kept for i from 0
                            collect (intern (format "$d%s%d"
                                                    (tl-constraint-class c) i)))))
        (push (cons binding (cons kept dicts)) tl-elab-let-dicts)))
    ;; A binding with nothing to quantify and nothing to retain keeps the
    ;; type it already had.  Returning a closed scheme instead would say
    ;; nothing -- a scheme with no quantifiers is a monomorphic type
    ;; wearing a hat -- and would only make it opaque to
    ;; `tl-infer-ir-Setq', which has to be able to tell a genuinely
    ;; polymorphic accumulator from an ordinary loop variable.
    (if (or gen-vars kept)
        (tl-generalize ty kept)
      ty)))

(defun tl-infer-ir-Setq (env expr)
  "Infer `(setq NAME EXPR)'.
A `let' may have put a *scheme* in NAME's cell, in which case the name
stands for one value read at as many types as it was instantiated at.
Assigning would swap the value under all of them at once, which is the
one thing generalization must not allow, so the reassignment is refused
rather than unified: unify would have to pick a single type for a
variable that is deliberately being used at several."
  (let* ((name (nth 1 expr))
         (r (tl-infer env (nth 2 expr)))
         (ty (car r))
         (b (cdr r))
         (cell (assq name (tl-tenv-locals env))))
    (when cell
      (if (tl-tscheme-p (cdr cell))
          (signal 'termlisp-type-error
                  (list (format "Cannot reassign %S: it is bound polymorphically" name)))
        (setq b (tl-ir-unify (cdr cell) ty b))))
    (cons (tl-apply-bindings ty b) b)))

;;; Control flow.

(defun tl-infer-ir-While (env expr)
  (let ((b (tl-ir-expect env nil (nth 1 expr) (tl-tbool))))
    (dolist (e (cddr expr))
      (let ((r (tl-infer (tl-zonk-env env b) e)))
        (setq b (tl-compose-bindings b (cdr r)))))
    (cons (tl-tunit) b)))

(defun tl-infer-ir-if (env expr)
  (let* ((b (tl-ir-expect env nil (nth 1 expr) (tl-tbool)))
         (rt (tl-infer (tl-zonk-env env b) (nth 2 expr)))
         (b (tl-compose-bindings b (cdr rt)))
         (re (tl-infer (tl-zonk-env env b) (nth 3 expr)))
         (b (tl-compose-bindings b (cdr re)))
         (b (tl-ir-unify (tl-apply-bindings (car rt) b)
                         (tl-apply-bindings (car re) b) b)))
    (cons (tl-apply-bindings (car rt) b) b)))

(defun tl-infer-ir-Catch (env expr)
  (tl-infer env (nth 2 expr)))

(defun tl-infer-ir-and-or (env expr)
  (let ((b nil))
    (dolist (e (cdr expr))
      (setq b (tl-ir-expect env b e (tl-tbool))))
    (cons (tl-tbool) b)))

(defun tl-infer-ir-polymorphic (_env _expr)
  "Break/Iterate/Throw have no informative type (bottom)."
  (cons (tl-fresh-tvar) nil))

(defun tl-infer-ir-minus (env expr)
  "Type unary/binary `-', or defer to a program-defined `-'."
  (let ((base (tl-tenv-base env)))
    (if (and base (gethash '- (tl-env-type-env base)))
        (tl-infer-application env expr)
      (let ((a (tl-fresh-tvar)) (b nil))
        (dolist (e (cdr expr))
          (setq b (tl-ir-expect env b e a)))
        (cons (tl-apply-bindings a b) b)))))

;;; Data construction and access.

(defun tl-infer-ir-Record (env expr)
  (let ((b nil) (tys nil))
    (dolist (e (cdr expr))
      (let ((r (tl-infer (tl-zonk-env env b) e)))
        (setq b (tl-compose-bindings b (cdr r)))
        (push (tl-apply-bindings (car r) b) tys)))
    (cons (tl-trecord (nreverse tys)) b)))

(defun tl-infer-ir-Union (env expr)
  (let ((r (tl-infer env (nth 2 expr))))
    (cons (tl-tunion (tl-apply-bindings (car r) (cdr r))) (cdr r))))

(defun tl-infer-ir-Field (env expr)
  (let* ((rv (tl-infer env (nth 1 expr)))
         (b (cdr rv))
         (ty (tl-apply-bindings (car rv) b))
         (idx (nth 2 expr)))
    (cons (if (and (integerp idx)
                   (tl-tcon-p ty) (eq (tl-tcon-name ty) 'Record))
              (or (nth idx (tl-tcon-args ty)) (tl-fresh-tvar))
            (tl-fresh-tvar))
          b)))

(defun tl-infer-ir-FieldSet (env expr)
  (let* ((rv (tl-infer env (nth 1 expr)))
         (b (cdr rv))
         (ty (tl-apply-bindings (car rv) b))
         (rx (tl-infer (tl-zonk-env env b) (nth 3 expr)))
         (b (tl-compose-bindings b (cdr rx)))
         (idx (nth 2 expr)))
    (when (and (integerp idx) (tl-tcon-p ty) (eq (tl-tcon-name ty) 'Record))
      (let ((fields (copy-sequence (tl-tcon-args ty))))
        (when (< idx (length fields))
          (setcar (nthcdr idx fields) (tl-apply-bindings (car rx) b)))
        (setq ty (tl-trecord fields))))
    (cons ty b)))

(defun tl-infer-ir-UnionCase (_env _expr)
  (cons (tl-tbool) nil))

(defun tl-infer-ir-NewArray (env expr)
  (let* ((b (tl-ir-expect env nil (nth 1 expr) (tl-tint)))
         (rf (tl-infer (tl-zonk-env env b) (nth 2 expr)))
         (b (tl-compose-bindings b (cdr rf))))
    (cons (tl-tvector (tl-apply-bindings (car rf) b)) b)))

(defun tl-infer-ir-ArrayRef (env expr)
  (let* ((ra (tl-infer env (nth 1 expr)))
         (b (cdr ra))
         (aty (tl-apply-bindings (car ra) b))
         (b (tl-ir-expect env b (nth 2 expr) (tl-tint)))
         (elt (if (and (tl-tcon-p aty) (eq (tl-tcon-name aty) 'Array))
                  (car (tl-tcon-args aty))
                (tl-fresh-tvar))))
    (cons elt b)))

(defun tl-infer-ir-ArraySet (env expr)
  (let* ((ra (tl-infer env (nth 1 expr)))
         (b (cdr ra))
         (b (tl-ir-expect env b (nth 2 expr) (tl-tint)))
         (rx (tl-infer (tl-zonk-env env b) (nth 3 expr)))
         (xt (tl-apply-bindings (car rx) b))
         (b (tl-compose-bindings b (cdr rx))))
    (setq b (tl-ir-unify (tl-apply-bindings (car ra) b) (tl-tvector xt) b))
    (cons xt b)))

(defun tl-infer-ir-ListToVector (env expr)
  (let* ((rl (tl-infer env (nth 1 expr)))
         (b (cdr rl))
         (lty (tl-apply-bindings (car rl) b))
         (elt (if (and (tl-tcon-p lty) (eq (tl-tcon-name lty) 'List))
                  (car (tl-tcon-args lty))
                (tl-fresh-tvar))))
    (cons (tl-tvector elt) b)))

(defun tl-infer-ir-quote (_env _expr)
  (cons (tl-fresh-tvar) nil))

;;; Application forms.

(defun tl-ir-apply (_env ftype arg-types bindings)
  "Unify FTYPE with the arrow ARG-TYPES -> R and return (R . BINDINGS).
An arity mismatch (tuples vs curried parameters) is tolerated: the
result is left unconstrained rather than aborting the whole program."
  (let ((res (tl-fresh-tvar))
        (want nil))
    (setq want res)
    (dolist (at (reverse arg-types))
      (setq want (tl-tarrow at want)))
    (let ((r (tl-unify-types (tl-apply-bindings ftype bindings) want bindings)))
      (if (car r)
          (cons (tl-apply-bindings res (cdr r)) (cdr r))
        (cons res bindings)))))

(defun tl-infer-ir-funcall (env expr)
  (let* ((rf (tl-infer env (nth 1 expr)))
         (b (cdr rf))
         (ats nil))
    (dolist (a (cddr expr))
      (let ((ra (tl-infer (tl-zonk-env env b) a)))
        (setq b (tl-compose-bindings b (cdr ra)))
        (push (tl-apply-bindings (car ra) b) ats)))
    (tl-ir-apply env (car rf) (nreverse ats) b)))

(defun tl-infer-ir-ApplyTuple (env expr)
  (let* ((rf (tl-infer env (nth 1 expr)))
         (b (cdr rf))
         (rt (tl-infer (tl-zonk-env env b) (nth 2 expr)))
         (b (tl-compose-bindings b (cdr rt)))
         (tty (tl-apply-bindings (car rt) b))
         (ats (if (and (tl-tcon-p tty) (eq (tl-tcon-name tty) 'Record))
                  (tl-tcon-args tty)
                (list (tl-fresh-tvar)))))
    (tl-ir-apply env (car rf) ats b)))

;;; Registration.

(defun tl-ir-register (head handler)
  (puthash head handler tl-infer-ir-heads))

(tl-ir-register 'Seq #'tl-infer-ir-Seq)
(tl-ir-register 'Let #'tl-infer-ir-Let)
(tl-ir-register 'Setq #'tl-infer-ir-Setq)
(tl-ir-register 'While #'tl-infer-ir-While)
(tl-ir-register 'if #'tl-infer-ir-if)
(tl-ir-register 'Catch #'tl-infer-ir-Catch)
(tl-ir-register 'and #'tl-infer-ir-and-or)
(tl-ir-register 'or #'tl-infer-ir-and-or)
(tl-ir-register 'Break #'tl-infer-ir-polymorphic)
(tl-ir-register 'Iterate #'tl-infer-ir-polymorphic)
(tl-ir-register 'Throw #'tl-infer-ir-polymorphic)
(tl-ir-register 'Record #'tl-infer-ir-Record)
(tl-ir-register 'Union #'tl-infer-ir-Union)
(tl-ir-register 'Field #'tl-infer-ir-Field)
(tl-ir-register 'FieldSet #'tl-infer-ir-FieldSet)
(tl-ir-register 'UnionCase #'tl-infer-ir-UnionCase)
(tl-ir-register 'NewArray #'tl-infer-ir-NewArray)
(tl-ir-register 'ArrayRef #'tl-infer-ir-ArrayRef)
(tl-ir-register 'ArraySet #'tl-infer-ir-ArraySet)
(tl-ir-register 'ListToVector #'tl-infer-ir-ListToVector)
(tl-ir-register
 'NewRef
 (lambda (env expr)
   (let ((r (tl-infer env (nth 1 expr))))
     (cons (tl-tcon 'Ref (list (tl-apply-bindings (car r) (cdr r))))
           (cdr r)))))
(tl-ir-register 'quote #'tl-infer-ir-quote)
(tl-ir-register 'funcall #'tl-infer-ir-funcall)
(tl-ir-register 'ApplyTuple #'tl-infer-ir-ApplyTuple)
(tl-ir-register '- #'tl-infer-ir-minus)

;; Constructor and primitive schemes.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'Cons
    (tl-tscheme (list a) (tl-tarrow a (tl-tarrow (tl-tlist a) (tl-tlist a))))))
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'Nil (tl-tscheme (list a) (tl-tlist a))))
(let ((a (tl-fresh-tvar)))
  (dolist (n '(first ListFirst))
    (tl-register-builtin-type n (tl-tscheme (list a) (tl-tarrow (tl-tlist a) a)))))
(let ((a (tl-fresh-tvar)))
  (dolist (n '(rest ListRest))
    (tl-register-builtin-type n
      (tl-tscheme (list a) (tl-tarrow (tl-tlist a) (tl-tlist a))))))
(let ((a (tl-fresh-tvar)))
  (dolist (n '(empty? ListEmpty))
    (tl-register-builtin-type n
      (tl-tscheme (list a) (tl-tarrow (tl-tlist a) (tl-tbool))))))
(dolist (n '(zero? even? odd?))
  (tl-register-builtin-type n
    (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tbool)))))
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'neq
    (tl-tscheme (list a) (tl-tarrow a (tl-tarrow a (tl-tbool))))))
(tl-register-builtin-type 'not
  (tl-tscheme nil (tl-tarrow (tl-tbool) (tl-tbool))))
(dolist (n '(quo mod cl-gcd))
  (tl-register-builtin-type n
    (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tint))))))
(dolist (n '(<= > >=))
  (tl-register-builtin-type n
    (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tbool))))))
(tl-register-builtin-type '/
  (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tint)))))
(tl-register-builtin-type '^
  (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tint)))))
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'tl-output-char
    (tl-tscheme (list a) (tl-tarrow a (tl-tarrow (tl-tchar) a)))))
(let ((a (tl-fresh-tvar)) (b (tl-fresh-tvar)))
  (tl-register-builtin-type 'tl-output-<<
    (tl-tscheme (list a b) (tl-tarrow a (tl-tarrow b a)))))
(tl-register-builtin-type 'tl-format
  (tl-tscheme nil (tl-tarrow (tl-fresh-tvar) (tl-tstring))))

;;; HM schemes for the remaining term-level builtins.
;;
;; Every numeric literal is inferred as `Int' regardless of its runtime
;; representation (see the `numberp' case of `tl-infer'), and `/' is already
;; registered `Int -> Int -> Int' although it may return a float.  The
;; transcendental functions therefore follow the same convention and are
;; typed `Int -> Int', which keeps `(sin (sin x))' composable.
(dolist (n '(sin cos tan exp log sqrt))
  (tl-register-builtin-type n
    (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tint)))))
;; The roundings take a number the checker reads as `Int' (a float
;; literal included, per the literal rule) and hand back a whole one,
;; so `Int -> Int' is both the convention and the truth here.
(dolist (n '(floor ceiling round))
  (tl-register-builtin-type n
    (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tint)))))
;; `factorial' is a builtin for the reason termlisp-builtins gives;
;; its scheme is Integer all the way.
(tl-register-builtin-type 'factorial
  (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tint))))
;; `format' takes the format string (the runtime only accepts "~a") and then
;; the value to render.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'format
    (tl-tscheme (list a)
                (tl-tarrow (tl-tstring) (tl-tarrow a (tl-tstring))))))
;; `print' renders any value and answers True.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'print
    (tl-tscheme (list a) (tl-tarrow a (tl-tbool)))))
;; `read-line' is nullary and answers the next line as a String.
(tl-register-builtin-type 'read-line (tl-tscheme nil (tl-tstring)))
;; The world handle is opaque: it is only ever threaded through the State
;; monad, so its type is kept fully general.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'stdin (tl-tscheme (list a) a)))
;; String helpers.  `string->list' answers single-character Strings (the
;; runtime maps each character through `string'), so `list->string' consumes
;; the same representation.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'string-join
    (tl-tscheme (list a) (tl-tarrow (tl-tlist a) (tl-tstring)))))
(tl-register-builtin-type 'string->list
  (tl-tscheme nil (tl-tarrow (tl-tstring) (tl-tlist (tl-tstring)))))
(tl-register-builtin-type 'list->string
  (tl-tscheme nil (tl-tarrow (tl-tlist (tl-tstring)) (tl-tstring))))
;; `seq' evaluates its first argument for its effect and answers the second.
(let ((a (tl-fresh-tvar)) (b (tl-fresh-tvar)))
  (tl-register-builtin-type 'seq
    (tl-tscheme (list a b) (tl-tarrow a (tl-tarrow b b)))))
;; `absurd' eliminates the uninhabited type `Void'.  Propositionally
;; `Void' is false, so this is bot-elimination: any proposition follows
;; from a contradiction, which is why the result type is free.  Unreachable
;; in well-typed code, because `Void' declares no constructors.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'absurd
    (tl-tscheme (list a) (tl-tarrow (tl-tcon 'Void nil) a))))
;; `load' reads a `.tls' file into the environment it runs in and
;; answers `Unit', the prelude's unit datatype; its argument is the file
;; name as a String.
(tl-register-builtin-type 'load
  (tl-tscheme nil (tl-tarrow (tl-tstring) (tl-tunit))))
;; `remove' undoes the most recent `load' of a file, taking the same
;; String argument and giving the same `Unit' answer; a file that is
;; not loaded is an error rather than a type-level no-op.
(tl-register-builtin-type 'remove
  (tl-tscheme nil (tl-tarrow (tl-tstring) (tl-tunit))))

;;; HM schemes for the exact-numeric IR helpers.
;;
;; These model Aldor's `Integer'/`DoubleFloat' tower, where an exact operand
;; promotes the operation to Calc's `frac'/`cplx'/`float' representation.  The
;; value universe has no `Fraction', `Complex' or `Bigfloat' constructor (see
;; `tl-ir-value-type-names'), so the operators are typed polymorphically over
;; the tower and the constructors answer an opaque result.
(let ((a (tl-fresh-tvar)))
  (dolist (n '(tl-num-add tl-num-sub tl-num-mul tl-num-div tl-num-quo))
    (tl-register-builtin-type n
      (tl-tscheme (list a) (tl-tarrow a (tl-tarrow a a))))))
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'tl-num-zero?
    (tl-tscheme (list a) (tl-tarrow a (tl-tbool)))))
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'tl-num-less?
    (tl-tscheme (list a) (tl-tarrow a (tl-tarrow a (tl-tbool))))))
(let ((r (tl-fresh-tvar)))
  (dolist (n '(tl-fraction tl-complex))
    (tl-register-builtin-type n
      (tl-tscheme (list r)
                  (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) r))))))
;; `tl-bigfloat' carries its precision as the second argument; the
;; result is a tower value again, so it answers the operand's type.
(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type 'tl-bigfloat
    (tl-tscheme (list a) (tl-tarrow a (tl-tarrow (tl-tint) a)))))

;;; Handle / reference types.

(defconst tl-ir-value-type-names
  '(Int DoubleFloat Bool Char String List Unit -> Record Union)
  "Type constructors whose values are immutable, substitutable values.
A `Record'/`Union' is value-like here (its fields are extracted, not
aliased); reference/handle types are the complement.")

(defun tl-ir-handle-type-p (ty)
  "Non-nil when TY denotes a handle/reference (identity-carrying) value.
Such values must be bound to a variable and are candidates for the
store, unlike plain immutable values."
  (and (tl-tcon-p ty)
       (let ((name (tl-tcon-name ty)))
         (or (memq name '(File TextReader TextWriter Ref Store Array
                          Generator))
             (not (memq name tl-ir-value-type-names))))))

(defun tl-typecheck-ir (forms &optional env)
  "Typecheck lowered IR FORMS in ENV (fresh if nil).  Return ENV.
Overloaded names (common in the IR) fall back to unconstrained
schemes instead of failing."
  (let ((env (or env (termlisp-make-env)))
        (tl-type-lenient-clauses t)
        (tl-type-lenient t))
    (dolist (form forms env)
      (tl-typecheck-form env form))))

(provide 'termlisp-ir-types)
;;; termlisp-ir-types.el ends here
