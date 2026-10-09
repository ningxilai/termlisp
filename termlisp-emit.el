;;; termlisp-emit.el --- Emit Emacs Lisp from termlisp forms -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Compiles termlisp surface forms to Emacs Lisp.  The emitted code is
;; standalone: functions become `defun's, values `defconst's, `if'
;; becomes the Emacs special form (both branches lazy, matching Aldor's
;; conditional), `and'/`or'/`not' the corresponding special forms, and
;; constructor applications become tagged lists.  Booleans map to t/nil.
;;
;; Supported: single-clause function defines with plain parameters,
;; value defines, lambdas, if, and/and/or/not, arithmetic and
;; comparison operators, constructor applications, nullary constructor
;; references, the list operations first/rest/empty? (inlined to
;; car/cdr-style accesses on tagged lists), even?/odd?, and
;; records/unions, which become plain vectors: (Record v...) and
;; (Union tag payload) emit `vector', (Field v i) emits `aref',
;; (FieldSet v i x) copies and updates, and (UnionCase u i) compares
;; the tag slot.  Statement forms from the loop lowering: Seq emits
;; `progn', Let emits `let*' (sequential bindings), While emits
;; `while', Setq emits `setq', Catch emits `catch', and Break and
;; Iterate throw to the fixed tags tl-loop-break and tl-loop-next.
;; Arrays are vectors: NewArray emits `make-vector', ArrayRef `aref',
;; and ArraySet `aset'.  Top-level statements are emitted as program
;; forms executed in source order.  Nil and Cons are known
;; constructors even without a datatype declaration.  Self tail calls
;; are optimized: a `defun' whose body calls itself in tail position
;; is rewritten as a loop that rebinds its parameters from an argument
;; vector, so tail recursion runs in constant stack.  Multi-clause
;; pattern dispatch is not yet emitted.

;;; Code:

(require 'cl-lib)

(define-error 'termlisp-emit-error "termlisp emit error")

(defconst tl-emit--default-ctors
  '((Nil . 0) (Cons . 2))
  "Constructors assumed present in every program, with their arities.")

(cl-defstruct (tl-emit-ctx (:constructor tl-emit-ctx--make)
                           (:copier nil))
  "Emission context: names known to the program being emitted.
The `locals' slot lists the parameters and lambda bindings in scope."
  (functions (make-hash-table :test #'eq))
  (constructors (make-hash-table :test #'eq))
  (locals nil))

(defun tl-emit--ctx-extend (ctx names)
  "Return a context like CTX with NAMES bound as locals."
  (let ((new (tl-emit-ctx--make)))
    (setf (tl-emit-ctx-functions new) (tl-emit-ctx-functions ctx)
          (tl-emit-ctx-constructors new) (tl-emit-ctx-constructors ctx)
          (tl-emit-ctx-locals new)
          (append names (tl-emit-ctx-locals ctx)))
    new))

(defun tl-emit--var-name (sym)
  "Rename a variable symbol that collides with an Emacs Lisp constant.
Aldor allows identifiers such as `t', which Emacs Lisp will not let
`setq' rebind; such a variable is emitted under a prefixed name."
  (if (eq sym 't)
      'tl-var-t
    sym))

(defun tl-emit--ctor-arity (head ctx)
  "Return the arity of constructor HEAD in CTX, or nil."
  (or (gethash head (tl-emit-ctx-constructors ctx))
      (alist-get head tl-emit--default-ctors)))

(defun tl-emit-program (forms)
  "Emit termlisp top-level FORMS as a list of Emacs Lisp forms."
  (let ((ctx (tl-emit-ctx--make))
        (seen (make-hash-table :test #'eq))
        out)
    (tl-emit--collect forms ctx)
    (dolist (form forms (nreverse out))
      (cond ((eq (car-safe form) ':) nil)
            ((eq (car-safe form) 'datatype) nil)
            ((eq (car-safe form) 'define)
             (let ((name (tl-emit--define-name (nth 1 form))))
               (unless (gethash name seen)
                 (puthash name t seen)
                 (let ((emitted (tl-emit--define name
                                                 (tl-emit--clauses name forms)
                                                 ctx)))
                   (when emitted
                     (push emitted out))))))
            (t
             ;; Top-level statement: emit its expression as a program
             ;; form, executed in source order.
             (push (tl-emit--expr form ctx) out))))))

(defun tl-emit-form (form)
  "Emit a single termlisp top-level FORM."
  (car (tl-emit-program (list form))))

(defun tl-emit-expr (expr &optional ctx)
  "Emit termlisp expression EXPR as an Emacs Lisp form."
  (tl-emit--expr expr (or ctx (tl-emit-ctx--make))))

(defun tl-emit--collect (forms ctx)
  (dolist (form forms)
    (pcase (car-safe form)
      ('define
       (let ((target (nth 1 form)))
         (if (consp target)
             (puthash (car target) t (tl-emit-ctx-functions ctx))
           (when (tl-emit--lambda-p (nth 2 form))
             (puthash target t (tl-emit-ctx-functions ctx))))))
      ('datatype
       (dolist (ctor (cddr form))
         (puthash (car ctor) (length (cdr ctor))
                  (tl-emit-ctx-constructors ctx))))
      (_ nil))))

(defun tl-emit--clauses (name forms)
  (cl-remove-if-not
   (lambda (form)
     (and (eq (car-safe form) 'define)
          (let ((target (nth 1 form)))
            (eq (if (consp target) (car target) target) name))))
   forms))

(defun tl-emit--define-name (target)
  (if (consp target) (car target) target))

(defun tl-emit--lambda-p (form)
  (and (consp form) (eq (car form) 'lambda)))

(defun tl-emit--guard-test (body)
  "Return BODY's %guard dispatch test, or t when unguarded."
  (if (eq (car-safe body) '%guard) (nth 1 body) t))

(defun tl-emit--strip-guard (body)
  "Return BODY without its %guard marker, if any."
  (if (eq (car-safe body) '%guard) (nth 2 body) body))

(defun tl-emit--define (name clauses ctx)
  (pcase clauses
    (`((define (,name . ,params) ,body))
     (unless (cl-every #'symbolp params)
       (signal 'termlisp-emit-error
               (list (format "Pattern parameters not yet supported in %s"
                             name))))
     (let ((rparams (mapcar #'tl-emit--var-name params)))
       (tl-emit--tco-defun
        `(defun ,name ,rparams
           ,(tl-emit--expr (tl-emit--strip-guard body)
                           (tl-emit--ctx-extend ctx rparams))))))
    (`((define ,name ,body))
     (let ((value (tl-emit--expr (tl-emit--strip-guard body) ctx)))
       (if (tl-emit--lambda-p value)
           (tl-emit--tco-defun
            `(defun ,name ,(nth 1 value) ,(nth 2 value)))
         `(defconst ,name ,value))))
    ;; Overloaded definitions: dispatch on argument count, and on
    ;; the lowering's type guards when two clauses share an arity.
    ((pred (lambda (cs)
             (and (> (length cs) 1)
                  (cl-every (lambda (c)
                              (and (eq (car-safe c) 'define)
                                   (consp (nth 1 c))))
                            cs))))
     (tl-emit--multi-define name clauses ctx))
    (_ (signal 'termlisp-emit-error
               (list (format "Multiple clauses for %s not yet supported"
                             name))))))

(defun tl-emit--multi-define (name clauses ctx)
  "Emit an arity-dispatching defun for overloaded CLAUSES.
Clauses may carry a %guard marker from the lowering; clauses sharing
an arity dispatch on those runtime type tests, in source order."
  (let ((by-arity (make-hash-table))
        (order nil))
    (dolist (clause clauses)
      (let ((arity (length (cdr (nth 1 clause)))))
        (push clause (gethash arity by-arity))
        (unless (memq arity order)
          (push arity order))))
    (let ((pcases
           (mapcar
            (lambda (arity)
              `(,arity
                ,(tl-emit--arity-dispatch
                  name (nreverse (gethash arity by-arity)) ctx)))
            (nreverse order))))
      `(defun ,name (&rest tl-args)
         (pcase (length tl-args)
           ,@pcases
           (_ (error "Wrong number of arguments to %s" ',name)))))))

(defun tl-emit--arity-dispatch (name clauses ctx)
  "Emit the call form for CLAUSES of one arity under NAME.
A single clause applies directly.  Several clauses become a `cond'
over their %guard tests; an unguarded clause's test is t, so source
order still decides, and a %p<i> placeholder stands for argument i."
  (if (null (cdr clauses))
      (let* ((clause (car clauses))
             (params (mapcar #'tl-emit--var-name (cdr (nth 1 clause))))
             (body (tl-emit--expr
                    (tl-emit--strip-guard (nth 2 clause))
                    (tl-emit--ctx-extend ctx params))))
        `(apply (lambda ,params ,body) tl-args))
    (let ((arity (length (cdr (nth 1 (car clauses))))))
      `(let ,(cl-loop
              for i below arity
              collect `(,(intern (format "%%p%d" i)) (nth ,i tl-args)))
         (cond ,@(mapcar
                  (lambda (clause)
                     (let* ((params (mapcar #'tl-emit--var-name
                                            (cdr (nth 1 clause))))
                            (test (tl-emit--guard-test (nth 2 clause)))
                           (body (tl-emit--expr
                                  (tl-emit--strip-guard (nth 2 clause))
                                  (tl-emit--ctx-extend ctx params))))
                      `(,test (apply (lambda ,params ,body) tl-args))))
                  clauses)
               (t (error "No applicable overload of %s" ',name)))))))

;;; Tail self-call optimization
;;
;; A self-call in tail position (nothing evaluates after it on the path
;; to the function's return) is rewritten to rebind the parameters from
;; a fresh argument vector and loop, so tail recursion runs in constant
;; stack.  The function's parameters are re-`let' -bound each iteration
;; from that vector; the vector slot starts as the entry arguments and
;; is cleared at the top of every iteration, so a tail-call site only
;; has to store the next arguments to request another iteration.

(defun tl-emit--tco-defun (form)
  "Return FORM with its self tail calls turned into a loop, if any.
FORM is an emitted `defun'."
  (let* ((name (nth 1 form))
         (params (nth 2 form))
         (body (nth 3 form)))
    (if (tl-emit--tco-site-p name body)
        (tl-emit--tco-wrap name params (tl-emit--tco name body))
      form)))

(defun tl-emit--tco-site-p (name form)
  "Non-nil if FORM contains a call to NAME in tail position.
Only value-flow tail positions are considered: branches of `if', the
last element of `progn'/`and'/`or'/`let' bodies, and `catch' bodies.
Conditions, binding initializers, and `lambda' bodies are not."
  (cond ((not (consp form)) nil)
        ((eq (car form) name) t)
        ((memq (car form) '(quote lambda)) nil)
        ((eq (car form) 'if)
         (or (tl-emit--tco-site-p name (nth 2 form))
             (and (> (length form) 3)
                  (tl-emit--tco-site-p name (nth 3 form)))))
        ((memq (car form) '(progn and or))
         (tl-emit--tco-site-p name (car (last form))))
        ((memq (car form) '(let let*))
         (tl-emit--tco-site-p name (car (last form))))
        ((eq (car form) 'catch)
         (tl-emit--tco-site-p name (nth 2 form)))
        (t nil)))

(defun tl-emit--tco (name form)
  "Replace tail-position calls to NAME in FORM with a loop restart."
  (cond ((not (consp form)) form)
        ((eq (car form) name)
         `(setq tl-tco-args (vector ,@(cdr form))))
        ((memq (car form) '(quote lambda)) form)
        ((eq (car form) 'if)
         (if (> (length form) 3)
             `(if ,(nth 1 form)
                  ,(tl-emit--tco name (nth 2 form))
                ,(tl-emit--tco name (nth 3 form)))
           `(if ,(nth 1 form) ,(tl-emit--tco name (nth 2 form)))))
        ((memq (car form) '(progn and or))
         `(,(car form) ,@(butlast (cdr form))
           ,(tl-emit--tco name (car (last form)))))
        ((memq (car form) '(let let*))
         `(,(car form) ,(nth 1 form)
           ,@(append (butlast (cddr form))
                     (list (tl-emit--tco name (car (last form)))))))
        ((eq (car form) 'catch)
         `(catch ,(nth 1 form) ,(tl-emit--tco name (nth 2 form))))
        (t form)))

(defun tl-emit--tco-wrap (name params body)
  "Build a `defun' for NAME whose BODY restarts on tail self calls.
PARAMS is the parameter list; BODY is the rewritten body."
  (let ((binds (cl-loop for p in params
                        for i from 0
                        collect `(,p (aref tl-tco-args ,i)))))
    `(defun ,name ,params
       (let ((tl-tco-args (vector ,@params))
             (tl-tco-ret nil))
         (while tl-tco-args
           (setq tl-tco-ret
                 (let ,binds
                   (setq tl-tco-args nil)
                   ,body)))
         tl-tco-ret))))

(defun tl-emit--expr (expr ctx)
  (cond ((numberp expr) expr)
        ((stringp expr) expr)
        ((symbolp expr) (tl-emit--symbol expr ctx))
        ((not (consp expr))
         (signal 'termlisp-emit-error
                 (list (format "Not an expression: %S" expr))))
        ((eq (car expr) 'quote) expr)
        ((eq (car expr) 'if)
         (unless (= (length expr) 4)
           (signal 'termlisp-emit-error
                   (list (format "if expects 3 arguments: %S" expr))))
         `(if ,(tl-emit--expr (nth 1 expr) ctx)
              ,(tl-emit--expr (nth 2 expr) ctx)
            ,(tl-emit--expr (nth 3 expr) ctx)))
        ((eq (car expr) 'lambda)
         (let ((params (nth 1 expr))
               (body (cddr expr)))
           (unless (cl-every #'symbolp params)
             (signal 'termlisp-emit-error
                     (list (format "Pattern parameters not yet supported: %S"
                                   params))))
           (unless (= (length body) 1)
             (signal 'termlisp-emit-error
                     (list "Lambda with multiple body expressions")))
            (let ((rparams (mapcar #'tl-emit--var-name params)))
              `(lambda ,rparams
                 ,(tl-emit--expr (car body)
                                 (tl-emit--ctx-extend ctx rparams))))))
        ;; Statement forms emitted by the Aldor loop lowering.  `Let'
        ;; uses let* so a loop variable can seed a direction flag in a
        ;; later binding of the same form.
        ((eq (car expr) 'Seq)
         (cons 'progn (mapcar (lambda (e) (tl-emit--expr e ctx))
                              (cdr expr))))
        ((eq (car expr) 'Let)
         (unless (>= (length expr) 2)
           (signal 'termlisp-emit-error
                   (list (format "Let expects bindings: %S" expr))))
         (let ((ctx1 ctx)
               (binds nil))
           (dolist (b (nth 1 expr))
             (unless (and (consp b) (= (length b) 2)
                          (symbolp (car b)))
               (signal 'termlisp-emit-error
                       (list (format "Bad Let binding: %S" b))))
             (let ((name (tl-emit--var-name (car b))))
               (push (list name (tl-emit--expr (cadr b) ctx1)) binds)
               ;; A bound name may hold a function value; calls to it
               ;; must go through funcall.
               (setq ctx1 (tl-emit--ctx-extend ctx1 (list name)))))
           `(let* ,(nreverse binds)
              ,@(mapcar (lambda (e) (tl-emit--expr e ctx1))
                        (cddr expr)))))
        ((eq (car expr) 'While)
         (unless (>= (length expr) 2)
           (signal 'termlisp-emit-error
                   (list (format "While expects a condition: %S" expr))))
         `(while ,(tl-emit--expr (nth 1 expr) ctx)
            ,@(mapcar (lambda (e) (tl-emit--expr e ctx)) (cddr expr))))
        ((eq (car expr) 'Setq)
         (unless (and (= (length expr) 3) (symbolp (nth 1 expr)))
           (signal 'termlisp-emit-error
                   (list (format "Bad Setq: %S" expr))))
         `(setq ,(tl-emit--var-name (nth 1 expr))
                ,(tl-emit--expr (nth 2 expr) ctx)))
        ((eq (car expr) 'Catch)
         (unless (and (= (length expr) 3) (symbolp (nth 1 expr)))
           (signal 'termlisp-emit-error
                   (list (format "Bad Catch: %S" expr))))
         `(catch ',(nth 1 expr) ,(tl-emit--expr (nth 2 expr) ctx)))
        ((eq (car expr) 'Break)
         (unless (= (length expr) 1)
           (signal 'termlisp-emit-error
                   (list (format "Bad Break: %S" expr))))
         `(throw 'tl-loop-break nil))
        ((eq (car expr) 'Iterate)
         (unless (= (length expr) 1)
           (signal 'termlisp-emit-error
                   (list (format "Bad Iterate: %S" expr))))
         `(throw 'tl-loop-next nil))
        ((eq (car expr) 'Throw)
         (unless (and (= (length expr) 3) (symbolp (nth 1 expr)))
           (signal 'termlisp-emit-error
                   (list (format "Bad Throw: %S" expr))))
         `(throw ',(nth 1 expr) ,(tl-emit--expr (nth 2 expr) ctx)))
        ;; Arrays are plain vectors: new makes one, reads and writes
        ;; use aref/aset (aset returns the stored value, matching the
        ;; value of an assignment).
        ((eq (car expr) 'NewArray)
         (unless (= (length expr) 3)
           (signal 'termlisp-emit-error
                   (list (format "Bad NewArray: %S" expr))))
         ;; One extra slot: PrimitiveArray is 0-based with no bound
         ;; checking, so a program may legitimately touch index N of a
         ;; `new N' array (sieve writes the composite N).  The spare
         ;; slot keeps such accesses in range.
         `(make-vector (1+ ,(tl-emit--expr (nth 1 expr) ctx))
                       ,(tl-emit--expr (nth 2 expr) ctx)))
        ;; A tuple argument is spread over the callee's parameters.
        ((eq (car expr) 'ApplyTuple)
         (unless (= (length expr) 3)
           (signal 'termlisp-emit-error
                   (list (format "Bad ApplyTuple: %S" expr))))
         `(apply ,(tl-emit--expr (nth 1 expr) ctx)
                 (append ,(tl-emit--expr (nth 2 expr) ctx) nil)))
        ((eq (car expr) 'ArrayRef)
         (unless (= (length expr) 3)
           (signal 'termlisp-emit-error
                   (list (format "Bad ArrayRef: %S" expr))))
         `(aref ,(tl-emit--expr (nth 1 expr) ctx)
                ,(tl-emit--expr (nth 2 expr) ctx)))
        ((eq (car expr) 'ArraySet)
         (unless (= (length expr) 4)
           (signal 'termlisp-emit-error
                   (list (format "Bad ArraySet: %S" expr))))
         `(aset ,(tl-emit--expr (nth 1 expr) ctx)
                ,(tl-emit--expr (nth 2 expr) ctx)
                ,(tl-emit--expr (nth 3 expr) ctx)))
        ;; An Array-typed bracket literal builds a Cons chain first,
        ;; then converts it to the vector that Array represents.
        ((eq (car expr) 'ListToVector)
         (unless (= (length expr) 2)
           (signal 'termlisp-emit-error
                   (list (format "Bad ListToVector: %S" expr))))
         `(tl-list-to-vector ,(tl-emit--expr (nth 1 expr) ctx)))
        (t (tl-emit--app expr ctx))))

(defun tl-emit--symbol (sym ctx)
  (setq sym (tl-emit--var-name sym))
  (cond ((eq sym 'True) t)
        ((eq sym 'False) nil)
        ;; A local variable shadows any function or constructor of
        ;; the same name, as in Aldor.
        ((memq sym (tl-emit-ctx-locals ctx))
         sym)
        ((gethash sym (tl-emit-ctx-functions ctx))
         (list 'function sym))
        ((let ((arity (tl-emit--ctor-arity sym ctx)))
           (and arity (zerop arity)))
         (list 'quote sym))
        (t sym)))

(defun tl-emit--app (expr ctx)
  (let ((head (car expr))
        (args (mapcar (lambda (arg) (tl-emit--expr arg ctx))
                      (cdr expr))))
    (when (symbolp head)
      (setq head (tl-emit--var-name head)))
    (if (not (symbolp head))
        ;; A computed function value: call it with funcall.
        (cons 'funcall (cons (tl-emit--expr head ctx) args))
      (if (memq head (tl-emit-ctx-locals ctx))
          ;; A parameter applied as a function: call its value.
          `(funcall ,head ,@args)
        (pcase head
        ('and `(and ,@args))
        ('or `(or ,@args))
        ('not (unless (= (length args) 1)
                (signal 'termlisp-emit-error
                        (list (format "not expects 1 argument: %S" expr))))
              `(not ,@args))
        ('eq (tl-emit--binary 'equal args expr))
        ('neq (tl-emit--binary (lambda (a b) `(not (equal ,a ,b)))
                               args expr))
        ;; List operations on (Cons h t)/Nil data, inlined so the
        ;; output stays standalone -- unless the program defines its
        ;; own operations of that name, which then win.
        ('first (if (gethash 'first (tl-emit-ctx-functions ctx))
                    (cons head args)
                  (tl-emit--unary 'cadr args expr)))
        ('rest (if (gethash 'rest (tl-emit-ctx-functions ctx))
                   (cons head args)
                 (tl-emit--unary 'caddr args expr)))
        ('empty? (if (gethash 'empty? (tl-emit-ctx-functions ctx))
                     (cons head args)
                   (tl-emit--unary (lambda (a) `(eq ,a 'Nil)) args expr)))
        ;; Internal walks over generator-built Cons lists: always
        ;; inlined, whatever the program defines.
        ('ListFirst (tl-emit--unary 'cadr args expr))
        ('ListRest (tl-emit--unary 'caddr args expr))
        ('ListEmpty (tl-emit--unary (lambda (a) `(eq ,a 'Nil)) args expr))
        ;; Integer predicates from the Boolean view.
        ('zero? (tl-emit--unary (lambda (a) `(zerop ,a)) args expr))
        ('even? (tl-emit--unary (lambda (a) `(zerop (mod ,a 2))) args expr))
        ('odd? (tl-emit--unary (lambda (a) `(not (zerop (mod ,a 2))))
                               args expr))
        ;; Aldor quo truncates toward zero, like elisp truncate.
        ('quo (tl-emit--binary (lambda (a b) `(truncate ,a ,b)) args expr))
        ;; Records and unions become plain vectors: a record holds its
        ;; fields at declaration indices, a union holds [tag payload].
        ('Record (tl-emit--min-args 1 args expr)
                 `(vector ,@args))
        ('Union (unless (= (length args) 2)
                  (signal 'termlisp-emit-error
                          (list (format "expected 2 arguments: %S" expr))))
                `(vector ,@args))
        ('Field (tl-emit--binary 'aref args expr))
        ('FieldSet (unless (= (length args) 3)
                     (signal 'termlisp-emit-error
                             (list (format "expected 3 arguments: %S" expr))))
                    ;; Records are mutable: update the field in place so
                    ;; aliases observe the change, and return the record.
                    `(let ((rec ,(nth 0 args)))
                       (aset rec ,(nth 1 args) ,(nth 2 args))
                       rec))
        ('UnionCase (tl-emit--binary
                     (lambda (u idx) `(eq (aref ,u 0) ,idx))
                     args expr))
        (_ (if (tl-emit--ctor-arity head ctx)
               (if (null args)
                   (list 'quote head)
                 (cons 'list (cons (list 'quote head) args)))
             (cons head args))))))))

(defun tl-emit--binary (op args expr)
  (unless (= (length args) 2)
    (signal 'termlisp-emit-error
            (list (format "expected 2 arguments: %S" expr))))
  (if (symbolp op)
      (cons op args)
    (apply op args)))

(defun tl-emit--min-args (n args expr)
  "Signal an error unless ARGS has at least N elements."
  (when (< (length args) n)
    (signal 'termlisp-emit-error
            (list (format "expected at least %d arguments: %S" n expr)))))

(defun tl-emit--unary (op args expr)
  (unless (= (length args) 1)
    (signal 'termlisp-emit-error
            (list (format "expected 1 argument: %S" expr))))
  (if (symbolp op)
      (cons op args)
    (funcall op (car args))))

(provide 'termlisp-emit)
;;; termlisp-emit.el ends here
