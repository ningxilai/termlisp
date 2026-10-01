;;; termlisp-eval.el --- Evaluator -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; CEK-style evaluator.  Function application and forcing a variable-bound
;; thunk are tail steps in the driver loop (TCO); arguments become memoized
;; thunks forced on demand (laziness).

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-reader)
(require 'termlisp-machine)
(require 'termlisp-pattern)
(require 'termlisp-builtins)
(require 'termlisp-types)
(require 'termlisp-elaborate)

(defvar termlisp--current-env nil
  "Dynamically bound evaluation context during `tl-run'.")

(defvar termlisp--load-env nil
  "Term-lisp environment used while loading `.tls' files.
Defined in `termlisp-load.el'; declared here so `termlisp-load-prelude'
byte-compiles without a free-variable warning.")

(defconst termlisp--magic-string
  ";;; -*- lexical-binding: t; mode: emacs-lisp; -*-"
  "First-line magic string marking a term-lisp (.tls) source file.")

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
    (unwind-protect
        (let* ((termlisp--current-env (or (tl-thunk-ctx value) termlisp--current-env))
               (v (tl-run (tl-thunk-expr value) (tl-thunk-env value))))
          (setf (tl-thunk-value value) v)
          (setf (tl-thunk-forced-p value) t)
          v)
      (setf (tl-thunk-busy-p value) nil)))))

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
      (let ((r (tl-match-seq (tl-clause-params (car clauses)) arg-thunks nil ctx)))
        (when r
          (setq result (cons (car clauses) (cdr r)))))
      (setq clauses (cdr clauses)))
    result))

(defun tl-apply-step (fv args caller-env)
  "Return `(BODY . ENV)' to continue applying FV to ARGS, or signal."
  (cond
   ((tl-closure-p fv)
    (cons (tl-closure-body fv)
          (tl-bind-params (tl-closure-params fv) args (tl-closure-env fv) caller-env)))
   ((tl-function-p fv)
    (let ((sel (tl-select-clause (tl-function-clauses fv)
                                 (tl-make-arg-thunks args caller-env))))
      (if sel
          (cons (tl-clause-body (car sel)) (cdr sel))
        (signal 'termlisp-eval-error '("No matching clause for function value")))))
   (t (signal 'termlisp-eval-error
              (list (format "Not a function: %S" fv))))))

(defun tl-resolve-callable (fv)
  "Resolve FV to a closure/function object, or return it unchanged."
  (cond
   ((tl-closure-p fv) fv)
   ((tl-function-p fv) fv)
   ((and (symbolp fv) (gethash fv (tl-env-functions termlisp--current-env)))
    (tl-make-function (gethash fv (tl-env-functions termlisp--current-env))))
   (t fv)))

;;; do-notation ----------------------------------------------------------

(defun tl-do-has-dict-p (form)
  "Non-nil if FORM is `(do DICT STMT...)' (explicit monad operand)."
  (let ((second (cadr form)))
    (not (or (and (consp second) (eq (cadr second) '<-))
             (and (consp second) (eq (car second) 'return))))))

(defun tl-desugar-do-method (form)
  "Desugar `(do STMT...)' to `bind'/`return' class-method calls.
The monad type is left to inference; the elaborator inserts the resolved
instance dictionary at each method call site."
  (let* ((stmts (cdr form))
         (last (car (last stmts)))
         (init (butlast stmts))
         (acc nil))
    (unless (and (consp last) (eq (car last) 'return))
      (signal 'termlisp-eval-error '("do block must end with (return e)")))
    (setq acc (list 'return (cadr last)))
    (dolist (stmt (reverse init))
      (if (and (consp stmt) (eq (cadr stmt) '<-))
          (setq acc (list 'bind (caddr stmt) (list 'lambda (list (car stmt)) acc)))
        (setq acc (list 'bind stmt (list 'lambda (list (gensym "ignored")) acc)))))
    acc))

(defun tl-desugar-do (form)
  "Desugar `(do ...)' into nested bind/return calls.
With an explicit dictionary, `(do DICT STMT...)' becomes
monad-bind/monad-return calls; without one, `(do STMT...)' becomes
class-method `bind'/`return' calls for type-directed elaboration.  Each STMT
is `(NAME <- EXPR)' or a bare monadic expression; the block must end with
`(return EXPR)'.  The block is desugared here so it may appear as a top-level
or nested `do' form (handled in `tl-eval-top' and `tl-run')."
  (if (tl-do-has-dict-p form)
      (let* ((dict (cadr form))
             (stmts (cddr form))
             (last (car (last stmts)))
             (init (butlast stmts))
             (acc nil))
        (unless (and (consp last) (eq (car last) 'return))
          (signal 'termlisp-eval-error '("do block must end with (return e)")))
        (setq acc (list 'monad-return dict (cadr last)))
        (dolist (stmt (reverse init))
          (if (and (consp stmt) (eq (cadr stmt) '<-))
              (setq acc (list 'monad-bind dict (caddr stmt)
                              (list 'lambda (list (car stmt)) acc)))
            (setq acc (list 'monad-bind dict stmt
                            (list 'lambda (list (gensym "ignored")) acc)))))
        acc)
    (tl-desugar-do-method form)))

;;; Driver ---------------------------------------------------------------

;; Known limitations (not addressed here):
;; * Forcing a variable-bound thunk in tail position pushes a `memoize'
;;   frame, so the continuation heap grows O(n) for the `if'-function loop
;;   idiom.  This avoids Elisp stack growth but is not constant-space.
;; * `:fuel' is a per-`tl-run' budget, not a global budget across nested
;;   `tl-run' calls (e.g. thunk forcing or literal/guard evaluation).

(defun tl-run (expr env)
  "Evaluate EXPR in lexical ENV to weak head normal form."
  (let* ((termlisp--current-env (or termlisp--current-env (termlisp-make-env)))
         (control expr) (cenv env) (kont nil) (value nil) (mode 'eval)
         (done nil)
         (fuel (or (tl-env-option termlisp--current-env :fuel) 100000)))
    (while (not done)
      (when (<= fuel 0)
        (signal 'termlisp-eval-error '("fuel exhausted")))
      (setq fuel (1- fuel))
      (if (eq mode 'eval)
          (cond
           ((symbolp control)
            (let ((cell (tl-lookup control cenv)))
              (cond
               ((null cell) (setq value control mode 'ret))
               ((and (tl-thunk-p (cdr cell)) (not (tl-thunk-forced-p (cdr cell))))
                (let ((tk (cdr cell)))
                  (when (tl-thunk-busy-p tk)
                    (signal 'termlisp-eval-error '("<<loop>> detected")))
                  (setf (tl-thunk-busy-p tk) t)
                  (push (list 'memoize tk) kont)
                  (setq cenv (tl-thunk-env tk) control (tl-thunk-expr tk))))
               ((tl-thunk-p (cdr cell))
                (setq value (tl-thunk-value (cdr cell)) mode 'ret))
               (t (setq value (cdr cell) mode 'ret)))))
           ((atom control) (setq value control mode 'ret))
           ((consp control)
            (let ((head (car control)) (args (cdr control)))
              (cond
               ((and (consp head) (eq (car head) 'lambda))
                (setq cenv (tl-bind-params (cadr head) args cenv cenv))
                (setq control (caddr head)))
               ((eq head 'lambda)
                (setq value (tl-make-closure (cadr control) (caddr control) cenv)
                      mode 'ret))
               ((eq head 'do)
                (setq control (tl-desugar-do control)))
               ((symbolp head)
                (let ((cell (assq head cenv))
                      (global (assq head (tl-env-globals termlisp--current-env)))
                      (fns (gethash head (tl-env-functions termlisp--current-env))))
                  (cond
                   ((or cell global)
                    (let* ((v (cdr (or cell global)))
                           (fv (tl-resolve-callable (if (tl-thunk-p v) (tl-force v) v)))
                           (step (tl-apply-step fv args cenv)))
                      (setq control (car step) cenv (cdr step))))
                   (fns
                    (let ((sel (tl-select-clause fns (tl-make-arg-thunks args cenv))))
                      (if sel
                          (progn (setq cenv (cdr sel))
                                 (setq control (tl-clause-body (car sel))))
                        (signal 'termlisp-eval-error
                                (list (format "No matching clause for %S" head))))))
                   ((tl-builtin-p head)
                    (let ((fn (gethash head tl-builtins))
                          (arg-thunks (tl-make-arg-thunks args cenv)))
                      (if (null arg-thunks)
                          (setq value (funcall fn nil) mode 'ret)
                        (push (list 'builtin fn nil (cdr arg-thunks)) kont)
                        (let ((tk (car arg-thunks)))
                          (setq cenv (tl-thunk-env tk)
                                control (tl-thunk-expr tk))))))
                   (t
                    (setq value (if args
                                    (cons head (tl-make-arg-thunks args cenv))
                                  head)
                          mode 'ret)))))
               (t
                (let* ((fv (tl-run head cenv))
                       (step (tl-apply-step fv args cenv)))
                  (setq control (car step) cenv (cdr step))))))))
        ;; return mode
        (if (null kont)
            (setq done t)
          (let ((frame (pop kont)))
            (pcase (car frame)
              ('memoize
               (let ((tk (cadr frame)))
                 (setf (tl-thunk-value tk) value)
                 (setf (tl-thunk-forced-p tk) t)
                 (setf (tl-thunk-busy-p tk) nil)))
              ('builtin
               (let* ((fn (nth 1 frame))
                      (collected (cons value (nth 2 frame)))
                      (remaining (nth 3 frame)))
                 (if (null remaining)
                     (setq value (funcall fn (nreverse collected)) mode 'ret)
                   (push (list 'builtin fn collected (cdr remaining)) kont)
                   (let ((tk (car remaining)))
                     (setq cenv (tl-thunk-env tk)
                           control (tl-thunk-expr tk)
                           mode 'eval)))))
              (_ (signal 'termlisp-eval-error
                         (list (format "Unknown continuation frame: %S" frame)))))))))
    value))

;;; Formatting -----------------------------------------------------------

(defun termlisp-value->string (v)
  "Render runtime value V as a string, forcing thunks."
  (let ((out nil) (stack (list v)))
    (while stack
      (let ((x (pop stack)))
        (cond
         ((stringp x) (push x out))
         (t
          (setq x (if (tl-thunk-p x) (tl-force x) x))
          (cond
           ((consp x)
            (push "(" out)
            (push ")" stack)
            (let* ((vec (vconcat x)) (n (length vec)))
              (dotimes (k n)
                (let ((idx (- n 1 k)))
                  (push (aref vec idx) stack)
                  (when (> idx 0) (push " " stack))))))
           ((tl-closure-p x) (push "#<closure>" out))
           ((tl-function-p x) (push "#<function>" out))
           (t (push (format "%s" x) out)))))))
    (apply #'concat (nreverse out))))

;;; Top-level forms ------------------------------------------------------

(defun tl-eval-define (env form)
  "Handle a top-level `define' FORM in ENV."
  (let ((target (cadr form)))
    (if (consp target)
        (let* ((name (car target))
               (params (mapcar (lambda (p)
                                 (tl-pattern-parse
                                  p (lambda (s) (gethash s (tl-env-constructors env)))))
                               (cdr target)))
               (clause (tl-make-clause name params (caddr form))))
          (puthash name
                   (append (gethash name (tl-env-functions env)) (list clause))
                   (tl-env-functions env))
          name)
      (let ((value (tl-run (caddr form) nil)))
        (setf (tl-env-globals env)
              (cons (cons target value) (tl-env-globals env)))
        value))))

(defun tl-eval-datatype (env form)
  "Handle `(datatype [open] NAME (CON ARGTYPE...) ...)' in ENV.
Datatype declarations are type-checked even when `:type-check' is nil:
constructor argument types are parsed and their schemes registered."
  (let* ((rest (cdr form))
         (open (eq (car rest) 'open))
         (rest (if open (cdr rest) rest))
         (name (car rest))
         (ctors (cdr rest))
         (old (gethash name (tl-env-datatypes env))))
    (when old
      (dolist (c (plist-get old :constructors))
        (remhash c (tl-env-constructors env))
        (remhash c (tl-env-type-env env))))
    (let ((syms (tl-register-datatype-types env name ctors)))
      (puthash name (list :open open :constructors (mapcar #'car ctors) :params syms)
               (tl-env-datatypes env)))
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
    (tl-register-datatype-types env name ctors (plist-get existing :params))
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
   ((and (consp form) (eq (car form) ':)) nil)
   ((and (consp form) (eq (car form) 'do)) (tl-run (tl-desugar-do form) nil))
   (t (tl-run form nil))))

(defun termlisp-eval-form (form &optional env)
  "Evaluate a single already-read term-lisp FORM in ENV.
Handles top-level `do' desugaring like `termlisp-eval', and honors the
`:type-check' and `:elaborate' options of ENV."
  (let* ((env (or env (termlisp-make-env)))
         (termlisp--current-env env)
         (form (if (and (consp form) (eq (car form) 'do))
                   (tl-desugar-do form)
                 form)))
    (if (tl-env-option env :elaborate)
        (setq form (tl-elaborate-form env form))
      (when (and (tl-env-option env :type-check)
                 (not (and (consp form)
                           (memq (car form) '(datatype datatype-extension)))))
        (tl-typecheck-form env form)))
    (tl-eval-top env form)))

(defun termlisp-eval (string &optional env)
  "Parse and evaluate STRING in ENV (creating a fresh env if nil).

A top-level `do' is desugared before inference/elaboration so that a
type-directed `(do ...)' exposes its `bind'/`return' class-method calls to
the elaborator.  A `do' nested inside a larger expression is instead
desugared at evaluation time by `tl-run' and is therefore not elaborated:
nested type-directed `do' (without an explicit monad operand) remains a
known limitation."
  (let ((env (or env (termlisp-make-env)))
        (result nil))
    (dolist (form (termlisp-parse string) result)
      (setq result (termlisp-eval-form form env)))))

(defun termlisp--ensure-magic-string (file)
  "Ensure FILE begins with `termlisp--magic-string', inserting it if absent.
Writes the file back only when the magic string is missing."
  (when (and (file-readable-p file) (file-writable-p file))
    (with-temp-buffer
      (insert-file-contents file)
      (goto-char (point-min))
      (unless (looking-at-p (regexp-quote termlisp--magic-string))
        (goto-char (point-min))
        (insert termlisp--magic-string "\n")
        (write-region (point-min) (point-max) file nil 'silent)))))

(defun termlisp-eval-file (file &optional env)
  "Evaluate the contents of FILE in ENV."
  (termlisp--ensure-magic-string file)
  (termlisp-eval (with-temp-buffer
                   (insert-file-contents file)
                   (buffer-string))
                 env))

(defun termlisp-load (file &optional env)
  "Load a `.tls' FILE into ENV (or a fresh env), ensuring its magic string.
Returns ENV."
  (termlisp--ensure-magic-string file)
  (let ((termlisp--load-env (or env (termlisp-make-env))))
    (load (expand-file-name file) nil t)
    termlisp--load-env))

(defconst termlisp--directory
  (file-name-directory (or load-file-name buffer-file-name))
  "Directory containing the termlisp sources.")

(defun termlisp-load-prelude (&optional env)
  "Load the bundled prelude into ENV (or a fresh env) and return it.
Loading goes through `load', so `termlisp-load' must be required for the
`datatype'/`define'/`class'/`instance' macros to be defined."
  (let ((termlisp--load-env (or env (termlisp-make-env)))
        (file (expand-file-name "termlisp-prelude.tls" termlisp--directory)))
    (termlisp--ensure-magic-string file)
    (load file nil t)
    termlisp--load-env))

(provide 'termlisp-eval)
;;; termlisp-eval.el ends here
