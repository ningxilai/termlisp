;;; termlisp-builtins.el --- Primitive functions -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Builtins receive a list of already-forced argument values.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-machine)

(declare-function tl-force "termlisp-eval" (value))

(defun tl-force-or-identity (v)
  "Force V with `tl-force' when available, else return V."
  (if (and (tl-thunk-p v) (fboundp 'tl-force))
      (tl-force v)
    v))

(defvar tl-builtins (make-hash-table :test #'eq)
  "Registry mapping builtin names to functions of a list of values.")

(cl-defstruct (tl-builtin-fn (:constructor tl-make-builtin-fn (name)))
  "First-class callable wrapping the builtin NAME.
Lets a bare builtin (e.g. `+' in `(foldl + 0 xs)') be passed as a value."
  name)

(defun tl-builtin-p (name)
  "Return non-nil if NAME is a builtin."
  (gethash name tl-builtins))

(defun tl-resolve-value (name)
  "If NAME is a builtin, return its `tl-builtin-fn' wrapper, else nil."
  (when (tl-builtin-p name)
    (tl-make-builtin-fn name)))

(defun tl-register-builtin (name fn)
  "Register builtin NAME implemented by FN."
  (puthash name fn tl-builtins))

(defun tl-bool (b) (if b 'True 'False))

(defun tl-check-numbers (args name)
  "Signal `termlisp-type-error' unless ARGS is two numbers."
  (unless (= (length args) 2)
    (signal 'termlisp-type-error
            (list (format "%s expects 2 arguments, got %d" name (length args)))))
  (dolist (a args)
    (unless (numberp a)
      (signal 'termlisp-type-error
              (list (format "%s expects numbers, got %S" name a))))))

(defun tl-check-one-number (args name)
  "Signal a `termlisp-type-error' mentioning NAME unless ARGS is one number."
  (tl-check-one-arg args name)
  (unless (numberp (car args))
    (signal 'termlisp-type-error
            (list (format "%s expects a number, got %S" name (car args))))))

;; Strict sequencing: builtin arguments are already forced to WHNF by the
;; driver (see `tl-run'), so evaluating `seq' forces A for its side effects
;; and returns B.  State's bind uses it to run a suspended effect held in a
;; lazy constructor field before handing control to the continuation.
(tl-register-builtin 'seq
  (lambda (args)
    (unless (= (length args) 2)
      (signal 'termlisp-type-error
              (list (format "seq expects 2 arguments, got %d" (length args)))))
    (cadr args)))

(tl-register-builtin 'eq
  (lambda (args)
    (tl-bool (tl-value-equal (nth 0 args) (nth 1 args) #'tl-force-or-identity))))
(tl-register-builtin '+
  (lambda (args) (tl-check-numbers args '+) (+ (nth 0 args) (nth 1 args))))
(tl-register-builtin '-
  (lambda (args)
    (unless (memq (length args) '(1 2))
      (signal 'termlisp-type-error
              (list (format "- expects 1 or 2 arguments, got %d"
                            (length args)))))
    (dolist (a args)
      (unless (numberp a)
        (signal 'termlisp-type-error
                (list (format "- expects numbers, got %S" a)))))
    (if (cdr args)
        (- (nth 0 args) (nth 1 args))
      (- (nth 0 args)))))
(tl-register-builtin '*
  (lambda (args) (tl-check-numbers args '*) (* (nth 0 args) (nth 1 args))))
(tl-register-builtin '<
  (lambda (args) (tl-check-numbers args '<) (tl-bool (< (nth 0 args) (nth 1 args)))))
(tl-register-builtin '<=
  (lambda (args) (tl-check-numbers args '<=) (tl-bool (<= (nth 0 args) (nth 1 args)))))
(tl-register-builtin '>
  (lambda (args) (tl-check-numbers args '>) (tl-bool (> (nth 0 args) (nth 1 args)))))
(tl-register-builtin '>=
  (lambda (args) (tl-check-numbers args '>=) (tl-bool (>= (nth 0 args) (nth 1 args)))))

(tl-register-builtin '/
  (lambda (args)
    (tl-check-numbers args '/)
    (let ((a (nth 0 args))
          (b (nth 1 args)))
      (when (zerop b)
        (signal 'termlisp-eval-error (list "Division by zero")))
      (if (and (integerp a) (integerp b) (zerop (mod a b)))
          (/ a b)
        (/ (float a) (float b))))))

;; The integer operator language.  Each of these carries a type scheme
;; in `termlisp-ir-types' already, so before they had runtimes a call
;; to any of them typechecked and then sat there as a stuck form --
;; rendering back as source instead of answering.  The semantics are
;; the emitter's own, copied so both paths agree: `quo' truncates
;; toward zero (Aldor's and C's), `mod' floors (elisp's, which is what
;; `tl-emit' falls through to), and the predicates read a number the
;; way `tl-emit' inlines them.
(tl-register-builtin 'quo
  (lambda (args)
    (tl-check-numbers args 'quo)
    (let ((b (nth 1 args)))
      (when (zerop b)
        (signal 'termlisp-eval-error (list "Division by zero")))
      (truncate (nth 0 args) b))))
(tl-register-builtin 'mod
  (lambda (args)
    (tl-check-numbers args 'mod)
    (let ((b (nth 1 args)))
      (when (zerop b)
        (signal 'termlisp-eval-error (list "Division by zero")))
      (mod (nth 0 args) b))))
(tl-register-builtin 'cl-gcd
  (lambda (args)
    (tl-check-numbers args 'cl-gcd)
    (dolist (a args)
      (unless (integerp a)
        (signal 'termlisp-type-error
                (list (format "cl-gcd expects integers, got %S" a)))))
    (cl-gcd (nth 0 args) (nth 1 args))))
(tl-register-builtin '^
  (lambda (args)
    (tl-check-numbers args '^)
    (expt (nth 0 args) (nth 1 args))))
;; `factorial' is a primitive because the prelude cannot spell it: an
;; accumulator loop over Integers has only variable positions to
;; match, so its recursive call would re-match its own clause under
;; the `if' that guards it -- the dangling cut the locality trial
;; refuses, and the prelude carries no exceptions to it.  Aldor's
;; Integer domain has factorial as a basic operation anyway (the
;; operator table lowers it to `tl-factorial' for the corpus), and
;; the loop answers 1 for every n <= 1, the mathematical base
;; included.
(tl-register-builtin 'factorial
  (lambda (args)
    (tl-check-one-number args 'factorial)
    (unless (integerp (car args))
      (signal 'termlisp-type-error
              (list (format "factorial expects an integer, got %S"
                            (car args)))))
    (let ((n (car args))
          (acc 1))
      (while (> n 1)
        (setq acc (* acc n)
              n (1- n)))
      acc)))
(tl-register-builtin 'zero?
  (lambda (args)
    (tl-check-one-number args 'zero?)
    (tl-bool (zerop (car args)))))
(tl-register-builtin 'even?
  (lambda (args)
    (tl-check-one-number args 'even?)
    (tl-bool (zerop (mod (car args) 2)))))
(tl-register-builtin 'odd?
  (lambda (args)
    (tl-check-one-number args 'odd?)
    (tl-bool (not (zerop (mod (car args) 2))))))
;; `neq' is `eq' decided over the same value equality and negated, so
;; the two always disagree exactly.
(tl-register-builtin 'neq
  (lambda (args)
    (tl-bool (not (tl-value-equal (nth 0 args) (nth 1 args)
                                  #'tl-force-or-identity)))))

(dolist (spec '((sin . sin) (cos . cos) (tan . tan) (exp . exp)))
  (let ((name (car spec))
        (impl (cdr spec)))
    (tl-register-builtin name
      (lambda (args)
        (tl-check-one-number args name)
        (float (funcall impl (float (car args))))))))

(tl-register-builtin 'log
  (lambda (args)
    (tl-check-one-number args 'log)
    (let ((x (float (car args))))
      (when (<= x 0.0)
        (signal 'termlisp-eval-error
                (list "Logarithm requires positive number")))
      (float (log x)))))

(tl-register-builtin 'sqrt
  (lambda (args)
    (tl-check-one-number args 'sqrt)
    (let ((x (float (car args))))
      (when (< x 0.0)
        (signal 'termlisp-eval-error
                (list "Square root requires non-negative number")))
      (float (sqrt x)))))

;; Float-to-integer roundings: the answer is a real integer in both
;; directions (a number the checker reads as `Int' comes back whole),
;; and `round' halves to even, elisp's own rule.  These are kept
;; primitives for parity, not for want of a spelling: the emitter's
;; fallback already lands on elisp's own of these names, so binding
;; the interpreter to the same functions keeps both paths exact at
;; the float/bignum boundary -- and a floor is anyway one
;; sign-adjustment over `(quo x 1)', which the suite pins.
(dolist (spec '((floor . floor) (ceiling . ceiling) (round . round)))
  (let ((name (car spec))
        (impl (cdr spec)))
    (tl-register-builtin name
      (lambda (args)
        (tl-check-one-number args name)
        (funcall impl (car args))))))

(defun tl-list-cons-p (v)
  "Return non-nil if V is a termlisp Cons cell."
  (and (consp v) (eq (car v) 'Cons)))

(defun tl-vector-to-list (v)
  "Convert vector V into the termlisp Cons chain of its elements."
  (let ((r 'Nil)
        (i (1- (length v))))
    (while (>= i 0)
      (setq r (list 'Cons (aref v i) r))
      (setq i (1- i)))
    r))

(defun tl-elements (v)
  "Return a Cons chain of the elements of V (a vector or a Cons list).
Used to iterate a value whose static type is unknown, so an Array and a
List are walkable by the same code."
  (if (vectorp v) (tl-vector-to-list v) v))

(defun tl-list-to-vector (l)
  "Convert the termlisp Cons chain L into a vector."
  (let ((n 0)
        (p l))
    (while (tl-list-cons-p p)
      (setq n (1+ n))
      (setq p (caddr p)))
    (let ((v (make-vector n nil))
          (i 0))
      (setq p l)
      (while (tl-list-cons-p p)
        (aset v i (cadr p))
        (setq i (1+ i))
        (setq p (caddr p)))
      v)))

(defun tl-check-one-arg (args name)
  "Signal `termlisp-type-error' unless ARGS holds exactly one value."
  (unless (= (length args) 1)
    (signal 'termlisp-type-error
            (list (format "%s expects 1 argument, got %d"
                          name (length args))))))

(tl-register-builtin 'first
  (lambda (args)
    (tl-check-one-arg args 'first)
    (let ((v (nth 0 args)))
      (if (tl-list-cons-p v)
          (cadr v)
        (signal 'termlisp-type-error
                (list (format "first expects a Cons, got %S" v)))))))

(tl-register-builtin 'rest
  (lambda (args)
    (tl-check-one-arg args 'rest)
    (let ((v (nth 0 args)))
      (if (tl-list-cons-p v)
          (caddr v)
        (signal 'termlisp-type-error
                (list (format "rest expects a Cons, got %S" v)))))))

(tl-register-builtin 'empty?
  (lambda (args)
    (tl-check-one-arg args 'empty?)
    (tl-bool (eq (nth 0 args) 'Nil))))

;; `absurd' is the elimination rule for `Void' (propositionally: ex falso
;; quodlibet, or bot-elimination).  Since `Void' has no constructors no
;; well-typed program can reach it; reaching it at all means `:type-check'
;; was off, so this signals rather than pretending to answer a value.
(tl-register-builtin 'absurd
  (lambda (args)
    (tl-check-one-arg args 'absurd)
    (signal 'termlisp-eval-error
            (list "absurd: Void has no values, so this call is unreachable"))))

(defun tl-values-to-list (values)
  "Convert the elisp list VALUES into the termlisp Cons chain of its elements."
  (let ((r 'Nil))
    (dolist (v (reverse values) r)
      (setq r (list 'Cons v r)))))

(tl-register-builtin 'list
  (lambda (args)
    (tl-values-to-list args)))

;;; Aldor output runtime ------------------------------------------------
;; The Aldor prelude's `stdout'/`newline'/`<<' have no termlisp
;; equivalent; emitted programs resolve them to these runtime values.
;; A program that defines its own `<<' (an OutputType method) keeps
;; that name -- only the prelude operator is renamed.

(defvar tl-gen-done (list 'tl-gen-done)
  "Unique value a lazy generator returns when exhausted.")

(defvar tl-stdout 'tl-stdout
  "Stand-in for Aldor's `stdout' TextWriter.")

(defvar tl-newline 10
  "Aldor's `newline' Character code.")

(defun tl-output--list-items (l)
  "Return the forced elements of the termlisp Cons chain L.
Cons arguments are thunks, so both the chain and each head are forced
while walking."
  (let (items)
    (setq l (tl-force-or-identity l))
    (while (tl-list-cons-p l)
      (push (tl-force-or-identity (cadr l)) items)
      (setq l (tl-force-or-identity (caddr l))))
    (nreverse items)))

(defun tl-output--format (value)
  "Render VALUE the way Aldor's basic OutputType instances print."
  (setq value (tl-force-or-identity value))
  (cond ((tl-list-cons-p value)
         (concat "[" (mapconcat #'tl-output--format
                                (tl-output--list-items value) ",") "]"))
        ;; Arrays, records and unions are vectors; print them like
        ;; Aldor `[a,b,c]'.
        ((vectorp value)
         (concat "[" (mapconcat (lambda (v) (tl-output--format (tl-force-or-identity v)))
                                (append value nil) ",") "]"))
        ((eq value 'Nil) "[]")
        ((eq value t) "true")
        ((eq value nil) "false")
        ((stringp value) value)
        ;; A constructor application, `(Succ Zero)'.  Aldor would send
        ;; this to an OutputType instance, and with none registered it
        ;; used to fall through to `%s' below, which prints the raw Lisp
        ;; -- the argument still unevaluated, and with it the
        ;; environment every thunk closes over.  Printing one natural
        ;; number therefore printed the world: tens of thousands of
        ;; characters of hash tables and clauses, none of them the
        ;; value asked for.  Rendering the spine keeps `print' on a
        ;; list of numbers a list of numbers.
        ((consp value)
         (concat "(" (mapconcat (lambda (v)
                                  (tl-output--format (tl-force-or-identity v)))
                                value " ")
                 ")"))
        (t (format "%s" value))))

(defun tl-output-value (value)
  "Print VALUE the way the prelude `<<' prints a basic OutputType."
  (princ (tl-output--format value)))

(defun tl-output-<< (writer value)
  "Print VALUE for the prelude output operator, returning WRITER."
  (tl-output-value value)
  writer)

(defun tl-format (value)
  "Format VALUE as a String (unary `<<')."
  (tl-output--format value))

(defun %guard (test body)
  "Runtime backing for a parameter type guard emitted by the lowering."
  (if test body (error "No applicable method (guard failed)")))

(defun tl-print (fmt)
  "FormattedOutput `print': return a function taking the format args.
Supports `~a' (consume an argument), `~n' (newline) and `~~'."
  (lambda (&rest args)
    (let ((i 0) (out "") (s fmt))
      (while (string-match "~\\([an~]\\)" s)
        (setq out (concat out (substring s 0 (match-beginning 0))))
        (pcase (match-string 1 s)
          ("a" (setq out (concat out (format "%s" (nth i args))))
               (setq i (1+ i)))
          ("n" (setq out (concat out "\n")))
          ("~" (setq out (concat out "~"))))
        (setq s (substring s (match-end 0))))
      (princ (concat out s)))))

(defun nputs (n text)
  "Stand-in for the C foreign function `nputs': print TEXT N times."
  (terpri)
  (dotimes (_ n n)
    (princ text)
    (terpri)))

;;; Aldor step operations ----------------------------------------------
;; `prev'/`next' are the predecessor/successor operations of the
;; prelude's integer StepType.

(defun tl-prev (n) (1- n))
(defun tl-next (n) (1+ n))

;; Standard combinators used by the corpus' example libraries.
(defun tl-factorial (n)
  "Factorial of N (matching the sample's `n <= 2 => n' base case)."
  (if (<= n 2) n (* n (tl-factorial (1- n)))))

(defun tl-choose (n k)
  "Binomial coefficient C(N, K)."
  (/ (tl-factorial n)
     (* (tl-factorial k) (tl-factorial (- n k)))))

;; `explode r' returns the fields of a record/union value as a tuple;
;; records are vectors, so this is the identity.
(defun tl-explode (v) v)

(defun tl-copy (v) v)

(defun tl-sort! (l)
  "Sort the termlisp Cons-list L, returning a fresh sorted list.
The comparison is chosen by the element type; the corpus uses
strings and integers."
  (let ((items nil)
        (p l))
    (while (tl-list-cons-p p)
      (push (cadr p) items)
      (setq p (caddr p)))
    (setq items (sort (nreverse items)
                      (lambda (a b)
                        (cond ((and (stringp a) (stringp b)) (string< a b))
                              ((and (numberp a) (numberp b)) (< a b))
                              (t (string< (format "%s" a)
                                          (format "%s" b)))))))
    (tl-values-to-list items)))

;; `nil? p' tests a Pointer for null; the null pointer is `Nil'.
(defun tl-pointer-null-p (p) (or (null p) (eq p 'Nil)))

(provide 'termlisp-builtins)
;;; termlisp-builtins.el ends here
