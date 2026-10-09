;;; termlisp-aldor.el --- Lower Aldor ABN trees to termlisp forms -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Frontend for compiling Aldor source to Emacs Lisp.  Programs are
;; annotated with `aldor -Fabn'; the annotated tree is lowered to
;; termlisp surface forms (the intermediate representation), which
;; `termlisp-emit' translates to Emacs Lisp.
;;
;; Supported subset: top-level function and value definitions,
;; Integer/Boolean arithmetic (+ - * < <= > >= =), if-then-else,
;; recursion, integer/string/float literals, lambdas (also as
;; arguments), blocks with local declarations and `cond => value'
;; early exits, sequences, assignment to locals (lowered by
;; substitution), unary minus, List values (nil, cons, [a, b]
;; literals, first/rest/empty?), and Records/Unions: construction
;; ([a, b] typed by the exported bracket), field and tag projection
;; (r.a, u.tag), union case tests (u case tag), and field assignment
;; (r.a := v, lowering to a functional update of the local).  Type
;; direction comes from the syme's type/exporter sefos.  Loops:
;; while/for/repeat with segment and list iterators, `|' filters,
;; break and iterate.  A local mutated by a loop is lowered to a real
;; variable -- a Let binds its entry value around the loop and the
;; rest of the sequence -- so repeated updates stay correct under the
;; substitution model.  Assignment to parameters outside loops and
;; unsupported nodes are rejected with a node-tagged error.

;;; Code:

(require 'cl-lib)
(require 'pp)
(require 'termlisp-abn)
(require 'termlisp-types)
(require 'termlisp-resolve)

(define-error 'termlisp-aldor-error "Aldor lowering error")

(defvar tl-aldor-program nil
  "Aldor compiler executable, or nil to search `exec-path'.")

(defvar tl-aldor-fricas-dir
  (expand-file-name "~/.local/lib/fricas/target/x86_64-linux-gnu")
  "FriCAS target directory whose algebra/ holds the Aldor library.")

(defvar tl-aldor-include "fricas"
  "Name of the Aldor header a program must include for Integer etc.")

(defvar tl-aldor-verbose nil
  "When non-nil, echo Aldor compiler output.")

(defconst tl-aldor--ops
  '(("+" . +) ("-" . -) ("*" . *) ("/" . /)
    ("<" . <) ("<=" . <=) (">" . >) (">=" . >=)
    ("=" . eq) ("~=" . neq) ("~" . not)
    ("and" . and) ("or" . or)
    ("quo" . quo) ("gcd" . cl-gcd) ("^" . expt)
    ("prev" . tl-prev) ("next" . tl-next)
    ("factorial" . tl-factorial) ("choose" . tl-choose)
    ("explode" . tl-explode)
    ("copy" . tl-copy) ("sort!" . tl-sort!)
    ("nil?" . tl-pointer-null-p)
    ("#" . tl-length) ("char" . tl-char)
    ("open" . tl-open) ("close!" . tl-close!)
    ("read!" . tl-read!) ("write!" . tl-write!)
    ("reader" . tl-reader) ("lines" . tl-lines)
    ("substring" . tl-substring) ("concat" . tl-concat)
    ("rightTrim" . tl-right-trim) ("print" . tl-print)
    ("true" . True) ("false" . False)
    ("nil" . Nil) ("cons" . Cons))
  "Mapping from Aldor operator names to termlisp function names.")

(defconst tl-aldor--array-type-names
  '(PrimitiveArray Array Vector String)
  "Type head names whose application is an element reference.
Strings count: aset/aref index them like arrays.")

(defvar tl-aldor--user-functions nil
  "Names the current program defines itself.
Such names shadow the builtin operator mapping of `tl-aldor--ops'.")

(defconst tl-aldor--reserved-fns '(<< empty? first rest)
  "Prelude names a program may redefine for a domain.
Their method definitions are renamed per definition site so the
prelude operator stays available at other call sites.")

(defvar tl-aldor--define-mangle nil
  "Alist mapping a definition's source position to a mangled name.")

(defvar tl-aldor--tuple-fns nil
  "Names of locally defined functions that return a tuple value.")

(defvar tl-aldor--reserved-def-params nil
  "Hash from a reserved name to its define parameter-node lists.
Used to resolve an overloaded operator by unifying the operand type
with the program's own signature versus the prelude one.")

(defvar tl-aldor--local-fn-results nil
  "Alist of locally defined function names to their result type sefo.")

(defun tl-aldor--scan-defines (abn node)
  "Record reserved-name definitions in NODE for per-site renaming."
  (when (and (consp node) (not (eq (car node) 'Id)))
    (when (eq (car node) 'Define)
      (let* ((decl (nth 1 node))
             (id (if (tl-abn-node-p decl 'Declare) (nth 1 decl) decl)))
        (when (tl-abn-node-p id 'Id)
          (let ((name (tl-abn-id-name id))
                (srcpos (tl-abn-id-srcpos id)))
            (when (and name (memq name tl-aldor--reserved-fns)
                       srcpos
                       (not (assoc srcpos tl-aldor--define-mangle)))
              (push (cons srcpos
                          (intern (format "%s$%d" name
                                          (length tl-aldor--define-mangle))))
                    tl-aldor--define-mangle))
            (when (and name (tl-abn-node-p decl 'Declare))
              (let* ((ty (tl-aldor--unwrap-type (nth 2 decl)))
                     (res (and (tl-abn-node-p ty 'Apply) (nth 3 ty))))
                (when res
                  (push (cons name res) tl-aldor--local-fn-results)
                  (when (tl-abn-node-p (tl-aldor--unwrap-type res) 'Comma)
                    (push name tl-aldor--tuple-fns)))
                ;; Reserved overloads: record the parameter type nodes so
                ;; a call site can be resolved by type unification.
                (when (and name (memq name tl-aldor--reserved-fns)
                           (tl-abn-node-p ty 'Apply)
                           (eq (tl-aldor--sefo-head-name abn ty) '->)
                           tl-aldor--reserved-def-params)
                  (let ((params (mapcar (lambda (p) (tl-aldor--sefo-to-type abn p))
                                        (tl-aldor--fun-param-types abn ty))))
                    (puthash name
                             (cons params (gethash name tl-aldor--reserved-def-params))
                             tl-aldor--reserved-def-params))))))))))
    (let ((tail (cdr node)))
      (while (consp tail)
        (when (consp (car tail))
           (tl-aldor--scan-defines abn (car tail)))
        (setq tail (cdr tail)))))

(defun tl-aldor--mangled-def (id)
  "Return the mangled name for a reserved-name definition Id ID.
A resolved call site carries the definition's source position on its
syme; a definition's own name carries it directly on the Id."
  (let* ((syme (tl-abn-id-syme id))
         (key (or (and syme (cdr (assq 'srcpos syme)))
                  (and id (tl-abn-id-srcpos id)))))
    (cdr (assoc key tl-aldor--define-mangle))))

(defun tl-aldor-program-path ()
  "Return the Aldor compiler executable path."
  (or tl-aldor-program
      (executable-find "aldor")
      (let ((fallback (expand-file-name "~/.local/bin/aldor")))
        (and (file-executable-p fallback) fallback))
      (signal 'termlisp-aldor-error '("aldor executable not found"))))

(defun tl-aldor-fricas-algebra-dir ()
  "Return the FriCAS algebra directory used for -Y and -I."
  (expand-file-name "algebra" tl-aldor-fricas-dir))

(defun tl-aldor-available-p ()
  "Return non-nil if the Aldor toolchain looks usable."
  (and (ignore-errors (tl-aldor-program-path) t)
       (file-directory-p (tl-aldor-fricas-algebra-dir))))

;;;###autoload
(defun tl-aldor-compile-file (as-file &rest opts)
  "Compile Aldor AS-FILE to Emacs Lisp.
Options plist:
  :output FILE       write the generated source to FILE
  :byte-compile     also byte-compile the output (requires :output)
Return the generated Emacs Lisp source string."
  (let ((output (plist-get opts :output))
        (byte-compile (plist-get opts :byte-compile)))
    (when (and byte-compile (not output))
      (signal 'termlisp-aldor-error
              '(":byte-compile requires :output")))
    (let ((abn-file (make-temp-file "termlisp-aldor-" nil ".abn")))
      (unwind-protect
          (progn
            (tl-aldor--run-compiler as-file abn-file)
            (let ((source (tl-aldor-source
                           (tl-aldor-lower-abn-file abn-file))))
              (when output
                (with-temp-file output
                  (insert source))
                (when byte-compile
                  (byte-compile-file output)))
              source))
        (when (file-exists-p abn-file)
          (delete-file abn-file))))))

(defun tl-aldor--run-compiler (as-file abn-file)
  "Run the Aldor compiler on AS-FILE, producing ABN-FILE."
  (let ((algebra (tl-aldor-fricas-algebra-dir))
        (as-file (expand-file-name as-file)))
    (unless (file-directory-p algebra)
      (signal 'termlisp-aldor-error
              (list (format "FriCAS algebra directory missing: %s" algebra))))
    (unless (file-exists-p as-file)
      (signal 'termlisp-aldor-error
              (list (format "No such file: %s" as-file))))
    (let ((default-directory (file-name-directory (expand-file-name abn-file))))
      (with-temp-buffer
        (let ((status (call-process (tl-aldor-program-path) nil t nil
                                    "-O"
                                    (format "-Fabn=%s" abn-file)
                                    "-lfricas"
                                    "-Y" algebra "-I" algebra
                                    as-file)))
          (when tl-aldor-verbose
            (message "%s" (buffer-string)))
          (unless (eq status 0)
            (signal 'termlisp-aldor-error
                    (list (format "aldor exited with %d:\n%s"
                                  status (buffer-string)))))
          (unless (file-exists-p abn-file)
            (signal 'termlisp-aldor-error
                    (list "aldor produced no .abn output"))))))))

(defun tl-aldor-lower-abn-file (file)
  "Read ABN FILE and lower it to a list of termlisp forms."
  (tl-aldor-lower (tl-abn-read-file file)))

(defun tl-aldor-lower (abn)
  "Lower ABN, a `tl-abn' struct, into a list of termlisp forms."
  (let ((tl-aldor--user-functions nil)
        (tl-aldor--define-mangle nil)
        (tl-aldor--tuple-fns nil)
        (tl-aldor--local-fn-results nil)
        (tl-aldor--reserved-def-params (make-hash-table :test #'eq)))
    (tl-aldor--scan-defines abn (tl-abn-tree abn))
    (nreverse (tl-aldor--lower-top abn (tl-abn-tree abn) nil))))

(declare-function tl-emit-program "termlisp-emit" (forms))

(defun tl-aldor-source (forms)
  "Render termlisp FORMS as Emacs Lisp source."
  (concat ";;; -*- lexical-binding: t -*-\n"
          "(require 'cl-lib)\n"
          (mapconcat (lambda (form) (pp-to-string form))
                     (tl-emit-program forms)
                     "")))

(defun tl-aldor--lower-top (abn node acc)
  "Lower top-level NODE onto ACC, returning the new accumulator.
Top-level statements are lowered left to right with a substitution
frame threaded across siblings, so `pok := ...' before a later use
substitutes.  Declarative nodes (imports, category/domain bodies) are
skipped or descended into for their inner defines; everything else
lowers as an expression statement."
  (cond ((not (consp node)) acc)
        ((eq (car node) 'Define)
         (append (tl-aldor--lower-define abn node) acc))
        ((memq (car node)
               '(Import Inline Declare Export Local
                 ForeignImport ForeignExport))
         acc)
        ((eq (car node) 'Sequence)
         (let ((frame nil)
               (kids (cdr node)))
           (while kids
             (let ((child (car kids)))
               (setq kids (cdr kids))
               (pcase (car-safe child)
                 ;; Flatten nested statement sequences and the bodies
                 ;; of extend/with blocks into this statement list.
                 ('Sequence
                  (setq kids (append (cdr child) kids)))
                 ((or 'Add 'With 'Extend)
                  (let ((body (nth 2 child)))
                    (when (tl-abn-node-p body 'Sequence)
                      (setq kids (append (cdr body) kids)))))
                  ('Define
                   (setq acc (append (tl-aldor--lower-define abn child)
                                     acc)))
                  ('Local
                   (let ((inner (nth 1 child)))
                     (cond
                      ;; `local cons ... == ...' wraps its define.
                      ((tl-abn-node-p inner 'Define)
                       (setq acc (append (tl-aldor--lower-define
                                          abn inner)
                                         acc)))
                      ((tl-abn-node-p inner 'Sequence)
                       (dolist (sub (cdr inner))
                         (when (tl-abn-node-p sub 'Define)
                           (setq acc (append (tl-aldor--lower-define
                                              abn sub)
                                             acc)))))
                      ((and (tl-abn-node-p inner 'Assign)
                            (tl-abn-node-p (nth 1 inner) 'Declare))
                       (let* ((decl (nth 1 inner))
                              (name (tl-abn-id-name (nth 1 decl)))
                              (rhs-node (nth 2 inner))
                              (rhs (if (tl-aldor--type-expr-p rhs-node)
                                       (tl-aldor--type-value)
                                     (tl-aldor--lower-expr
                                      abn rhs-node frame))))
                         (when name
                           (push (cons name rhs) frame)))))))
                ('Assign
                 (let ((res (tl-aldor--lower-top-assign abn child frame)))
                   (setq frame (car res))
                   (dolist (form (cdr res))
                     (push form acc))))
                  ((or 'nil 'Import 'Inline 'Declare 'Export
                       'ForeignImport 'ForeignExport 'Default)
                   nil)
                 (_
                  (push (tl-aldor--lower-expr abn child frame) acc)))))
           acc))
        (t
         (cons (tl-aldor--lower-expr abn node nil) acc))))

(defun tl-aldor--lower-top-assign (abn node frame)
  "Lower top-level assignment NODE in FRAME.
Returns a cons (NEW-FRAME . FORMS).  A simple assignment to a
substitutable value needs no emitted form: a later statement reads
the bound value by substitution, and NEW-FRAME shadows FRAME.  A
tuple assignment evaluates its right-hand side once, setqs a
temporary, and setqs each target from the tuple vector; NEW-FRAME
maps every target to itself so later statements read those
variables."
  (let* ((lhs (nth 1 node))
         (rhs-node (nth 2 node))
         (rhs (if (tl-aldor--type-expr-p rhs-node)
                  (tl-aldor--type-value)
                (tl-aldor--lower-expr abn rhs-node frame))))
    (cond
     ((tl-abn-node-p lhs 'Declare)
      (let ((name (tl-aldor--decl-name lhs)))
        (cons (cons (cons name
                          (tl-aldor--wrap-array-literal
                           abn lhs rhs-node rhs))
                    frame)
              nil)))
     ((tl-abn-node-p lhs 'Id)
      (let ((name (tl-abn-id-name lhs)))
        (if name
            (cons (cons (cons name rhs) frame) nil)
          (cons frame nil))))
     ((tl-abn-node-p lhs 'Comma)
      (let ((names (mapcar #'tl-abn-id-name (cdr lhs))))
        (if (or (memq nil names) (not rhs))
            (cons frame nil)
          (let ((tv (intern "%%tt")))
            (cons (append (mapcar (lambda (n) (cons n n)) names) frame)
                  (list
                   `(Seq (Setq ,tv ,rhs)
                         ,@(cl-loop for n in names
                                    for i from 0
                                    collect
                                    `(Setq ,n (ArrayRef ,tv ,i))))))))))
     (t (cons frame nil)))))

(defun tl-aldor--lower-define (abn node)
  "Lower a |Define| NODE into an accumulator-style list of forms.
Macro defines (an Id declaration) emit nothing.  Domain and category
definitions (`add'/`with' values, optionally label-wrapped) emit no
form of their own: the body is lowered as a top-level block so its
operation defines are collected.  Ordinary functions and constants
yield a single form."
  (let ((decl (nth 1 node))
        (value (nth 2 node)))
    (cond
     ;; `Rep ==> Integer'-style macro: compile-time only.
     ((tl-abn-node-p decl 'Id)
      nil)
     ((not (tl-abn-node-p decl 'Declare))
      (signal 'termlisp-aldor-error
              (list (format "define without declaration: %S" (car decl)))))
     (t
      (let ((name (tl-aldor--decl-name decl)))
        (cond
         ((tl-aldor--type-node-p value)
          (let ((body (tl-aldor--type-body value)))
            (when body
              (tl-aldor--lower-top abn body nil))))
         ((tl-abn-node-p value 'Lambda)
          (let* ((body (car (last (cdr value))))
                 ;; A curried type constructor `C(I)(n) == add {...}'
                 ;; nests lambdas around the real body; the innermost
                 ;; body decides whether this define is type-level.
                 (tail body))
            (while (tl-abn-node-p tail 'Lambda)
              (setq tail (car (last (cdr tail)))))
            (if (tl-aldor--type-node-p tail)
                (let ((inner (tl-aldor--type-body tail)))
                  (when inner
                    (tl-aldor--lower-top abn inner nil)))
              (let* ((names (tl-aldor--param-names (nth 1 value)))
                     (pre (cl-remove-if
                           (lambda (n) (memq n names))
                           (delete-dups
                            (tl-aldor--expr-assign-names body))))
                     (env (append (mapcar (lambda (n) (cons n n)) names)
                                  (mapcar (lambda (n) (cons n n)) pre)))
                     (tests (tl-aldor--param-guard-tests abn (nth 1 value))))
                (push name tl-aldor--user-functions)
                 (let* ((inner (tl-aldor--wrap-return
                               body
                               (tl-aldor--lower-expr abn body env)))
                        (inner (tl-aldor--prebind-let pre inner))
                        (inner (if tests
                                   `(%guard (and ,@tests) ,inner)
                                 inner)))
                   (list `(define (,name ,@names) ,inner)))))))
         (t
          (push name tl-aldor--user-functions)
          (list `(define ,name
                   ,(tl-aldor--wrap-return
                     value
                     (tl-aldor--lower-expr abn value nil)))))))))))

(defun tl-aldor--lower-expr-assign (abn expr env)
  "Lower expression-position assignment EXPR given ENV.
Only assignment to an actual variable -- a parameter or a
loop-promoted local -- is supported.  The right-hand side is bound to
a temporary, the variable is written, and the temporary is the value
of the expression."
  (let ((lhs (nth 1 expr)))
    (unless (tl-abn-node-p lhs 'Id)
      (signal 'termlisp-aldor-error
              '("Unsupported assignment target")))
    (let* ((name (tl-abn-id-name lhs))
           (hit (and name (assq name env))))
      (unless (and hit (eq (cdr hit) name))
        (signal 'termlisp-aldor-error
                (list (format "Expression assignment to non-variable |%s|"
                              name))))
      (let ((rhs (tl-aldor--lower-expr abn (nth 2 expr) env)))
        `(Let ((tl-assign-tmp ,rhs))
              (Seq (Setq ,name tl-assign-tmp) tl-assign-tmp))))))

(defun tl-aldor--type-node-p (node)
  "Non-nil when NODE is an `add'/`with' value, label-wrapped or not."
  (let ((n node))
    (while (tl-abn-node-p n 'Label)
      (setq n (nth 2 n)))
    (memq (car-safe n) '(Add With))))

(defun tl-aldor--type-body (node)
  "Return NODE's block body when it is a type-level `add'/`with' value.
LABEL wrappers are stripped first.  Only a Sequence or Define body
qualifies: base types, signatures, and empty blocks yield nil."
  (let ((n node))
    (while (tl-abn-node-p n 'Label)
      (setq n (nth 2 n)))
    (let ((body (and (memq (car-safe n) '(Add With)) (nth 2 n))))
      (cond ((tl-abn-node-p body 'Sequence) body)
            ((tl-abn-node-p body 'Define) body)
            (t nil)))))

(defun tl-aldor--type-expr-p (expr)
  "Non-nil when EXPR is a type-level value rather than a runtime value.
Heuristic: an arrow application, an `add'/`with' block, or a label
around either.  Tuples (bare `Comma') are runtime values and do not
count."
  (let ((found nil))
    (cl-labels ((walk (x)
                  (when (and (consp x) (not found))
                    (cond
                     ((memq (car x) '(Add With)) (setq found t))
                     ((and (eq (car x) 'Apply)
                           (tl-abn-node-p (nth 1 x) 'Id)
                           (memq (tl-abn-id-name (nth 1 x)) '(-> +->)))
                      (setq found t))
                     (t (walk (car x))
                        (when (consp (cdr x)) (walk (cdr x))))))))
      (walk expr))
    found))

(defun tl-aldor--type-value ()
  "Substitution value for a binding with no runtime content."
  '(quote tl-type-value))

(defun tl-aldor--decl-name (decl)
  "Return the name symbol of the identifier declared by DECL.
A reserved-name definition gets its per-site mangled name."
  (let* ((id (nth 1 decl))
         (name (tl-abn-id-name id)))
    (unless name
      (signal 'termlisp-aldor-error
              (list (format "declaration without a name: %S" decl))))
    (or (and (memq name tl-aldor--reserved-fns) (tl-aldor--mangled-def id))
        name)))

(defun tl-aldor--param-names (params)
  "Return the parameter name symbols of a Lambda PARAMS node."
  (let ((items (cond ((null params) nil)
                     ((tl-abn-node-p params 'Comma) (cdr params))
                     (t (list params)))))
    (mapcar
     (lambda (p)
       (let ((name (cond ((tl-abn-node-p p 'Declare)
                          (tl-abn-id-name (nth 1 p)))
                         ((tl-abn-node-p p 'Id)
                          (tl-abn-id-name p))
                         (t nil))))
         (unless name
           (signal 'termlisp-aldor-error
                   (list (format "Unsupported parameter: %S" p))))
         name))
     items)))

(defun tl-aldor--guard-test-for (head ph)
  "Runtime test for a value of static type HEAD, written over PH.
Only heads with a distinct runtime representation get a test -- these
are what same-arity overloads must be told apart by.  Other types
(collections of the same representation, numbers) fall through to
source-order dispatch."
  (pcase head
    ((or 'Tuple 'Record 'Union) `(vectorp ,ph))
    ('Generator `(or (eq ,ph 'Nil) (consp ,ph)))
    ('String `(stringp ,ph))
    ('Boolean `(booleanp ,ph))
    (_ nil)))

(defun tl-aldor--param-guard-tests (abn params)
  "Dispatch tests for Lambda PARAMS, one per guarded parameter.
Each test is written over the placeholder symbol %p<i>, where i is
the parameter's position; unguarded parameters contribute nothing."
  (let ((items (cond ((null params) nil)
                     ((tl-abn-node-p params 'Comma) (cdr params))
                     (t (list params))))
        (i -1)
        (tests nil))
    (dolist (p items)
      (setq i (1+ i))
      (when (tl-abn-node-p p 'Declare)
        (let* ((head (tl-aldor--sefo-head-name abn (nth 2 p)))
               (test (tl-aldor--guard-test-for
                      head (intern (format "%%p%d" i)))))
          (when test (push test tests)))))
    (nreverse tests)))

(defvar tl-aldor--yield-var nil
  "Dynamically bound to the accumulator variable while lowering a
generator body.  A nil value means the current scope is not one.")

(defvar tl-aldor--generating nil
  "Non-nil while lowering a generator body lazily.
Then `yield' lowers to a suspension node rather than an accumulator
update.")

(defvar tl-aldor--collect-as-generator nil
  "Non-nil when a Collect is lowered where a Generator is expected.")

(defvar tl-aldor--gen-counter 0
  "Counter for fresh state-machine labels and pull variables.")

(defun tl-aldor--gen-fresh (prefix)
  "Return a fresh interned symbol named PREFIX plus a counter."
  (intern (format "%s%d" prefix (cl-incf tl-aldor--gen-counter))))

(defun tl-aldor--expr-assign-names (node)
  "Return the names assigned by expression-position assignments in NODE.
Statement-position assignments -- direct Sequence children and Local
wrappers -- are the sequence lowering's business and are skipped, but
their right-hand sides are still searched.  Nested lambdas collect
their own."
  (let ((names nil))
    (cl-labels ((walk (n statement-p)
                  (when (consp n)
                    (cond
                     ((eq (car n) 'Lambda) nil)
                     ((and (eq (car n) 'Assign)
                           (tl-abn-node-p (nth 1 n) 'Id))
                      (unless statement-p
                        (let ((nm (tl-abn-id-name (nth 1 n))))
                          (when nm (push nm names))))
                      (walk (nth 2 n) nil))
                     ((eq (car n) 'Sequence)
                      (dolist (c (cdr n)) (walk c t)))
                     ((eq (car n) 'Local)
                      (walk (nth 1 n) t))
                     ;; Descend safely: dotted annotation pairs inside
                     ;; the tree must not be treated as child lists.
                     (t (walk (car n) nil)
                        (when (consp (cdr n))
                          (walk (cdr n) nil)))))))
      (walk node nil))
    (nreverse names)))

(defun tl-aldor--prebind-let (names form)
  "Wrap FORM in a Let binding each of NAMES to nil, or return FORM.
Expression-position assignments introduce scratch locals the
sequence-level substitution model cannot see; the enclosing function
binds them as real variables."
  (if names
      `(Let ,(mapcar (lambda (n) (list n nil)) names) ,form)
    form))

(defun tl-aldor--lower-expr (abn expr env)
  "Lower expression EXPR to a termlisp form.
ABN is the enclosing `tl-abn'; ENV is an alist mapping names in scope
to their lowered substitution forms (parameters map to themselves)."
  (unless (consp expr)
    (signal 'termlisp-aldor-error
            (list (format "Not an expression: %S" expr))))
  (pcase (car expr)
    ('Id (tl-aldor--lower-id expr env))
    ('LitInteger (string-to-number (nth 1 expr)))
    ('LitFloat (string-to-number (nth 1 expr)))
    ('LitString (nth 1 expr))
    ;; Boolean connectives, wrapped or bare.
    ('Test (tl-aldor--lower-expr abn (nth 1 expr) env))
    ('Not (list 'not (tl-aldor--lower-expr abn (nth 1 expr) env)))
    ('And (cons 'and (mapcar (lambda (e) (tl-aldor--lower-expr abn e env))
                             (cdr expr))))
    ('Or (cons 'or (mapcar (lambda (e) (tl-aldor--lower-expr abn e env))
                           (cdr expr))))
    ('If (tl-aldor--lower-if abn expr env))
    ('Apply (tl-aldor--lower-apply abn expr env))
    ('Lambda (tl-aldor--lower-lambda abn expr env))
    ('Label (tl-aldor--lower-expr abn (nth 2 expr) env))
    ;; `x$T', `x::T', `x@T', `x pretend T': representation-preserving
    ;; selection and coercion evaluate the value itself.
    ((or 'Qualify 'CoerceTo 'RestrictTo 'PretendTo)
     (tl-aldor--lower-expr abn (nth 1 expr) env))
    ('Assign (tl-aldor--lower-expr-assign abn expr env))
    ('Sequence (tl-aldor--lower-sequence abn expr env))
    ('Repeat (tl-aldor--lower-expr-repeat abn expr env))
    ('Generate (tl-aldor--lower-generate abn expr env))
    ;; `yield e' inside generate conses onto the accumulator; outside
    ;; one there is no generator to feed.
    ('Yield
     (cond (tl-aldor--generating
            (list 'Yield (tl-aldor--lower-expr abn (nth 1 expr) env)))
           ((not tl-aldor--yield-var)
            (signal 'termlisp-aldor-error '("yield outside a generator")))
           (t
            (list 'Setq tl-aldor--yield-var
                  (list 'Cons (tl-aldor--lower-expr abn (nth 1 expr) env)
                        tl-aldor--yield-var)))))
    ('Collect (tl-aldor--lower-collect abn expr env))
    ('Break (tl-aldor--lower-jump 'Break))
    ('Iterate (tl-aldor--lower-jump 'Iterate))
    ;; A tuple value `(a, b, c)' builds a record-shaped vector, the
    ;; same runtime representation records use.
    ('Comma (cons 'Record
                  (mapcar (lambda (e) (tl-aldor--lower-expr abn e env))
                          (cdr expr))))
    ;; `T has C' is a static test the type checker already discharged.
    ('Has 'True)
    ;; `expr where defs' binds the local defines around the expression.
    ('Where (tl-aldor--lower-where abn expr env))
    ;; `assert c' checks at runtime.
    ('Assert `(if ,(tl-aldor--lower-expr abn (nth 1 expr) env)
                  nil
                (error "assertion failed")))
    ;; `goto L' arms the enclosing labeled dispatch and jumps.
    ('Goto (let ((target (tl-abn-id-name (nth 1 expr))))
             (unless target
               (signal 'termlisp-aldor-error '("goto without a target")))
             `(Seq (Setq %pc (quote ,target))
                   (Throw tl-seq-next nil))))
    ;; `return e' throws to the enclosing function's catch, which the
    ;; define/lambda lowering installs when the body contains return.
    ('Return (list 'Throw 'tl-fn-return
                   (if (nth 1 expr)
                       (tl-aldor--lower-expr abn (nth 1 expr) env)
                     nil)))
    ;; `ref e' is a one-slot mutable cell (a Ref value); dereference and
    ;; assignment go through the cell.
    ('Reference (list 'NewRef (tl-aldor--lower-expr abn (nth 1 expr) env)))
    (_ (signal 'termlisp-aldor-error
               (list (format "Unsupported expression node |%s|" (car expr)))))))

(defun tl-aldor--lower-id (id env)
  "Lower Id ID given environment ENV."
  (let ((cell (tl-abn-id-name-cell id)))
    (unless cell
      (signal 'termlisp-aldor-error
              (list (format "Identifier without a name: %S" id))))
    (let* ((name (cdr cell))
           (hit (and name (assq name env))))
      (cond (hit (cdr hit))
            ;; A prelude domain/category used as a value.
            ((tl-aldor--domain-id-p id) (list 'quote name))
            ;; A reserved prelude operator: a definition of it is
            ;; renamed per site, every other use is the prelude one.
            ((eq name '<<)
             (or (tl-aldor--mangled-def id) 'tl-output-<<))
            ((memq name '(empty? first rest))
             (or (tl-aldor--mangled-def id)
                 (cdr (assq name '((empty? . ListEmpty)
                                   (first . ListFirst)
                                   (rest . ListRest))))))
            ;; `S empty' (an imported prelude value, no source position)
            ;; is the empty List; a program's own `empty' keeps its name.
            ((eq name 'empty)
             (let ((syme (tl-abn-id-syme id)))
               (if (and syme (not (assq 'srcpos syme))) 'Nil 'empty)))
            ((and (memq name '(stdout newline space eof stdin))
                  (not (memq name tl-aldor--user-functions)))
             (cdr (assq name '((stdout . tl-stdout) (newline . tl-newline)
                               (space . tl-space) (eof . tl-eof)
                               (stdin . tl-stdin)))))
            ((string-match-p "\\`[0-9]+\\'" (symbol-name name))
             (string-to-number (symbol-name name)))
            (t (tl-aldor--op-name name))))))

(defun tl-aldor--domain-id-p (id)
  "Non-nil when Id ID names a prelude domain or category.
Such an id is a type used as a runtime value; it is represented by
its name symbol."
  (let ((syme (tl-abn-id-syme id)))
    (and syme
         (not (assq 'type syme))
         (not (assq 'srcpos syme))
         (let ((exp (assq 'exporter syme)))
           (and exp (assq 'lib (cdr exp)))))))

(defun tl-aldor--type-data (abn node)
  "Render type expression NODE as quoted data."
  (cond ((tl-abn-node-p node 'Id) (tl-abn-id-name node))
        ((tl-abn-node-p node 'Apply)
         (cons (tl-aldor--type-data abn (nth 1 node))
               (mapcar (lambda (a) (tl-aldor--type-data abn a))
                       (cddr node))))
        (t (car-safe node))))

(defun tl-aldor--op-name (name)
  "Map Aldor operator NAME to its termlisp name.
A name the current program defines itself is kept unchanged."
  (if (memq name tl-aldor--user-functions)
      name
    (let ((mapped (assoc (symbol-name name) tl-aldor--ops)))
      (if mapped (cdr mapped) name))))

;;; Type-directed Record/Union support.  Syme annotations in the tree
;;; are spliced; symes inside the sefo table carry raw (ref . N) cells.

(defun tl-aldor--syme-ref-cell (syme key)
  "Return SYME's KEY annotation cell when it is a (ref . N) cell."
  (let ((cell (cdr (assq key syme))))
    (and (consp cell) (eq (car cell) 'ref) cell)))

(defun tl-aldor--raw-id-syme (abn id)
  "Return the syme alist of Id ID inside an unresolved sefo of ABN.
Tree ids carry an already-spliced syme; sefo ids carry (syme ref . N)."
  (let ((ann (assq 'syme (cdr id))))
    (when (consp ann)
      (if (and (consp (cdr ann)) (eq (cadr ann) 'ref) (integerp (cddr ann)))
          (aref (tl-abn-symes abn) (cddr ann))
        (cdr ann)))))

(defun tl-aldor--unwrap-type (node)
  "Strip Define/Label/Declare wrappers from type NODE, recursively."
  (while (memq (car-safe node) '(Define Label Declare))
    (setq node (nth 2 node)))
  node)

(defun tl-aldor--sefo-head-name (abn sefo)
  "Return the head symbol name of type SEFO, or nil.
An Apply's head Id names the constructor; a bare Id names the type
itself.  Ids inside a sefo may carry an unresolved (syme ref . N)
annotation, which is followed through ABN's syme table."
  (setq sefo (tl-aldor--unwrap-type sefo))
  (cond
   ((tl-abn-node-p sefo 'Apply)
    (let ((head (nth 1 sefo)))
      (when (tl-abn-node-p head 'Id)
        (let ((syme (tl-aldor--raw-id-syme abn head)))
          (or (and syme (tl-abn-syme-name syme))
              (tl-abn-id-name head))))))
   ((tl-abn-node-p sefo 'Id)
    (let ((syme (tl-aldor--raw-id-syme abn sefo)))
      (or (and syme (tl-abn-syme-name syme))
          (tl-abn-id-name sefo))))))

(defun tl-aldor--sefo-declares (sefo)
  "Return the field Declare children of a Record/Union type SEFO."
  (setq sefo (tl-aldor--unwrap-type sefo))
  (when (tl-abn-node-p sefo 'Apply)
    (cl-remove-if-not (lambda (x) (tl-abn-node-p x 'Declare)) (cddr sefo))))

(defun tl-aldor--array-type-p (abn id)
  "Non-nil when resolved Id ID has an array type."
  (let* ((ty (tl-aldor--id-type-sefo abn id))
         (name (and ty (tl-aldor--sefo-head-name abn ty))))
    (and (memq name tl-aldor--array-type-names) name)))

(defun tl-aldor--sefo-to-type (abn sefo)
  "Convert an ABN type sefo to a graph type node (constructor names only)."
  (setq sefo (tl-aldor--unwrap-type sefo))
  (cond
   ((tl-abn-node-p sefo 'Apply)
    (let ((h (tl-aldor--sefo-head-name abn sefo)))
      (tl-tcon (or h 'Unknown)
               (mapcar (lambda (a) (tl-aldor--sefo-to-type abn a))
                       (cddr sefo)))))
   ((tl-abn-node-p sefo 'Id)
    (tl-tcon (or (tl-aldor--sefo-head-name abn sefo) 'Unknown) nil))
   (t (tl-tcon 'Unknown nil))))

(defun tl-aldor--prelude-overload-scheme (name)
  "Return the prelude scheme whose parameter distinguishes overload NAME."
  (let ((a (tl-fresh-tvar)) (w (tl-fresh-tvar)))
    (pcase name
      ('empty? (tl-tscheme (list a)
                           (tl-tarrow (tl-tcon 'List (list a)) (tl-tbool))))
      ('first (tl-tscheme (list a)
                          (tl-tarrow (tl-tcon 'List (list a)) a)))
      ('rest (tl-tscheme (list a)
                         (tl-tarrow (tl-tcon 'List (list a))
                                    (tl-tcon 'List (list a)))))
      ('<< (tl-tscheme (list w a)
                       (tl-tarrow w (tl-tarrow a w)))))))

(defun tl-aldor--prelude-overload-target (name)
  "The runtime/inlined target for the prelude overload NAME."
  (cdr (assq name '((<< . tl-output-<<) (empty? . ListEmpty)
                    (first . ListFirst) (rest . ListRest)))))

(defun tl-aldor--overload-operand-index (name)
  "Which argument of NAME distinguishes the overload (the value operand)."
  (if (eq name '<<) 1 0))

(defun tl-aldor--array-index-ir (arr-ty index-ir)
  "Return INDEX-IR adjusted for zero-based Lisp indexing of ARR-TY.
Aldor's Array is 1-based; PrimitiveArray, String and Vector are
0-based, so only Array indexes are shifted."
  (if (eq arr-ty 'Array)
      (list '- index-ir 1)
    index-ir))

(defun tl-aldor--tuple-valued-p (abn node)
  "Non-nil when NODE yields a tuple (multiple) value."
  (or (tl-abn-node-p node 'Comma)
      (let ((ty (tl-aldor--expr-type-sefo abn node)))
        (and ty
             (or (tl-abn-node-p (tl-aldor--unwrap-type ty) 'Comma)
                 (eq (tl-aldor--sefo-head-name abn ty) 'Comma))))
      (and (tl-abn-node-p node 'Apply)
           (let ((h (nth 1 node)))
             (and (tl-abn-node-p h 'Id)
                  (memq (tl-abn-id-name h) tl-aldor--tuple-fns))))))

(defun tl-aldor--bracket-p (node)
  "Non-nil when NODE is an Aldor bracket expression.
Brackets parse as an application of the head `bracket', both for
literals `[a, b]' and comprehensions `[x for i in r]'."
  (and (tl-abn-node-p node 'Apply)
       (tl-abn-node-p (nth 1 node) 'Id)
       (eq (cdr (tl-abn-id-name-cell (nth 1 node))) 'bracket)))

(defun tl-aldor--wrap-array-literal (abn decl rhs-node rhs)
  "Wrap lowered RHS in ListToVector when DECL declares an Array literal.
A bracket expression lowers to a Cons chain, but Aldor's Array is a
mutable vector, so an Array-typed literal is converted once built."
  (if (and (tl-abn-node-p decl 'Declare)
           (eq (tl-aldor--sefo-head-name abn (nth 2 decl)) 'Array)
           (tl-aldor--bracket-p rhs-node))
      (list 'ListToVector rhs)
    rhs))

(defun tl-aldor--sefo-id-name (abn id)
  "Return the declared name of Id ID inside a sefo of ABN."
  (let ((syme (tl-aldor--raw-id-syme abn id)))
    (or (and syme (tl-abn-syme-name syme))
        (tl-abn-id-name id))))

(defun tl-aldor--decl-index (abn declares name)
  "Return the 0-based index of field NAME among DECLARES, or nil."
  (cl-position name declares
               :key (lambda (d) (tl-aldor--sefo-id-name abn (nth 1 d)))))

(defun tl-aldor--fun-param-names (abn sefo)
  "Return the parameter names of arrow type SEFO."
  (when (eq (tl-aldor--sefo-head-name abn sefo) '->)
    (let ((params (nth 2 sefo)))
      (when (tl-abn-node-p params 'Comma)
        (setq params (cdr params)))
      (when (tl-abn-node-p params 'Declare)
        (setq params (list params)))
      (mapcar (lambda (d) (tl-aldor--sefo-id-name abn (nth 1 d)))
              (cl-remove-if-not (lambda (d) (tl-abn-node-p d 'Declare))
                                params)))))

(defun tl-aldor--fun-param-types (abn sefo)
  "Return the declared parameter type sefos of arrow type SEFO."
  (when (eq (tl-aldor--sefo-head-name abn sefo) '->)
    (let ((params (nth 2 sefo)))
      (when (tl-abn-node-p params 'Comma)
        (setq params (cdr params)))
      (when (tl-abn-node-p params 'Declare)
        (setq params (list params)))
      (mapcar (lambda (d) (nth 2 d))
              (cl-remove-if-not (lambda (d) (tl-abn-node-p d 'Declare))
                                params)))))

(defun tl-aldor--arrow-branch-index (abn syme declares)
  "Return the index in DECLARES matching SYME's first parameter type.
SYME's arrow type is monomorphized at the call site, so its first
parameter type names the branch the payload belongs to even when the
payload expression itself (a literal, say) carries no type."
  (let* ((ty (and syme (tl-abn-syme-type abn syme)))
         (ptypes (and ty (tl-aldor--fun-param-types abn ty)))
         (pname (and ptypes (car ptypes)
                     (tl-aldor--sefo-head-name abn (car ptypes)))))
    (and pname
         (cl-position pname declares
                      :key (lambda (d)
                             (tl-aldor--sefo-head-name abn (nth 2 d)))))))

(defun tl-aldor--syme-owner-sefo (abn syme)
  "Return the type sefo of the domain exporting SYME, or nil."
  (let ((cell (tl-aldor--syme-ref-cell syme 'exporter)))
    (and cell (aref (tl-abn-sefos abn) (cdr cell)))))

(defun tl-aldor--id-type-sefo (abn id)
  "Return the type sefo of resolved Id ID, or nil."
  (let ((syme (tl-abn-id-syme id)))
    (and syme (tl-abn-syme-type abn syme))))

(defun tl-aldor--resolve-type-alias (abn ty)
  "Follow Id type aliases in TY until a structural type is reached."
  (let ((n 0))
    (while (and (< n 8) (tl-abn-node-p ty 'Id))
      (let ((next (tl-aldor--id-type-sefo abn ty)))
        (if (and next (not (equal next ty)))
            (setq ty next
                  n (1+ n))
          (setq n 8))))
    ty))

(defun tl-aldor--recv-var-name (recv)
  "Return the variable name a receiver chain RECV bottoms out in.
Coercion wrappers (`rep(s)', `s pretend T') and array projections
(`f(i)' inside `f(i)(j) := v') are stripped to the innermost Id,
which names the variable holding the value.  Returns nil when the
receiver is not built around a plain identifier."
  (let ((n recv))
    (while (and (consp n)
                (memq (car n) '(PretendTo RestrictTo CoerceTo Qualify
                                     Apply))
                (consp (cdr n)))
      (setq n (nth 1 n)))
    (and (tl-abn-node-p n 'Id) (tl-abn-id-name n))))

(defun tl-aldor--expr-type-sefo (abn node)
  "Return the static type sefo of expression NODE when recoverable.
Head-first applications take the result type of the head's arrow
type; recv-first projections take the selected field's declared
type; coercions pass through to the target; other nodes qualify
only when they carry a resolved identifier."
  (cond
   ((tl-abn-node-p node 'Id) (tl-aldor--id-type-sefo abn node))
   ((memq (car node) '(PretendTo RestrictTo CoerceTo Qualify))
    (tl-aldor--expr-type-sefo abn (nth 2 node)))
    ((tl-abn-node-p node 'Apply)
     (let* ((head (cadr node))
            (syme (and (tl-abn-node-p head 'Id) (tl-abn-id-syme head)))
            (ty (and syme (tl-abn-syme-type abn syme)))
            (local-res (and (tl-abn-node-p head 'Id)
                            (cdr (assq (tl-abn-id-name head)
                                       tl-aldor--local-fn-results))))
            (owner (tl-aldor--expr-type-sefo abn head)))
       (cond
        (local-res local-res)
        ((and ty (eq (tl-aldor--sefo-head-name abn ty) '->))
         (nth 3 ty))
        ;; A computed function value of arrow type: take its result.
        ((and owner (eq (tl-aldor--sefo-head-name abn owner) '->))
         (nth 3 owner))
        ;; Array indexing `a(i)' takes the element type of the array.
        ((and owner
              (tl-abn-node-p owner 'Apply)
              (memq (tl-aldor--sefo-head-name abn owner)
                    tl-aldor--array-type-names))
         (nth 2 owner))
        ((and (= (length node) 3)
              (tl-abn-node-p (nth 2 node) 'Id))
         (let* ((declares (and owner (tl-aldor--sefo-declares owner)))
                (idx (and declares
                          (tl-aldor--decl-index
                           abn declares
                           (tl-abn-id-name (nth 2 node))))))
           (and idx (tl-aldor--unwrap-type (nth 2 (nth idx declares)))))))))))

(defun tl-aldor--union-owner-sefo (abn)
  "Return the Union sefo a syme named `union' is exported by, or nil.
The `union' special can appear at a use site without a resolved syme;
a file-level syme of the same name with an exporter cell still points
at the union type it belongs to.  Ambiguity yields nil."
  (let ((symes (tl-abn-symes abn))
        owners)
    (dotimes (i (length symes))
      (let ((s (aref symes i)))
        (when (eq (cdr (assq 'name s)) 'union)
          (let ((owner (tl-aldor--syme-owner-sefo abn s)))
            (when (and owner (not (member owner owners)))
              (push owner owners))))))
    (when (and (consp owners) (null (cdr owners)))
      (car owners))))

(defun tl-aldor--union-payload-index (abn declares payload)
  "Return the branch index of DECLARES that holds PAYLOAD's value.
Aldor picks the branch from the payload's static type; when that type
is unavailable, an identifier named like a tag selects it directly."
  (let* ((ptype (tl-aldor--expr-type-sefo abn payload))
         (pname (and ptype (tl-aldor--sefo-head-name abn ptype))))
    (or (and pname
             (cl-position pname declares
                          :key (lambda (d)
                                 (tl-aldor--sefo-head-name
                                  abn (nth 2 d)))))
        ;; The `nil' literal reads as a nameless identifier, matching
        ;; the nil-named tag exactly.
        (and (tl-abn-node-p payload 'Id)
             (tl-aldor--decl-index abn declares
                                   (tl-abn-id-name payload))))))

(defun tl-aldor--union-bracket-tag (abn syme owner)
  "Return the branch tag name of a union bracket head SYME.
SYM is exported by the union type OWNER; the branch is the name of the
first parameter of the bracket function's original (per-branch) type."
  (let* ((orig-cell (tl-aldor--syme-ref-cell syme 'original))
         (orig (and orig-cell (aref (tl-abn-symes abn) (cdr orig-cell))))
         (orig-type (and orig (tl-abn-syme-type abn orig)))
         (tag (car (tl-aldor--fun-param-names abn orig-type))))
    (unless (and tag (tl-aldor--sefo-declares owner))
      (signal 'termlisp-aldor-error
              '("union bracket without an identifiable branch")))
    tag))

(defun tl-aldor--try-projection (abn node env)
  "Lower receiver.tag APPLY NODE if it is a Record/Union projection.
Return the lowered form, or nil when NODE is an ordinary application.
The receiver may be any expression: its static type supplies the
owner, and a nested projection receiver is handled recursively."
  (let ((kids (cdr node)))
    (when (and (= (length kids) 2)
               (tl-abn-node-p (cadr kids) 'Id))
      (let* ((recv (car kids))
             (tag (cadr kids))
             (ty (tl-aldor--resolve-type-alias
                  abn (tl-aldor--expr-type-sefo abn recv)))
             (ty-name (and ty (tl-aldor--sefo-head-name abn ty))))
        (when (memq ty-name '(Record Union))
          (let* ((tag-name (tl-abn-id-name tag))
                 (idx (and ty
                           (tl-aldor--decl-index
                            abn (tl-aldor--sefo-declares ty) tag-name))))
            (unless idx
              (signal 'termlisp-aldor-error
                      (list (format "No field |%s| in %s type"
                                    tag-name ty-name))))
            ;; Record fields sit at their declaration index; a union
            ;; value is [tag payload], so its payload is at slot 1.
            `(Field ,(tl-aldor--lower-expr abn recv env)
                    ,(if (eq ty-name 'Union) 1 idx))))))))

(defun tl-aldor--lower-if (abn node env)
  "Lower |If| NODE given environment ENV.
A missing or nil else branch -- Aldor's `if c then b;' -- lowers to
a literal nil."
  (let ((kids (cdr node)))
    (unless (memq (length kids) '(2 3))
      (signal 'termlisp-aldor-error
              (list (format "Malformed if: %d branches" (length kids)))))
    (let* ((cond-node (car kids))
           (condition (if (tl-abn-node-p cond-node 'Test)
                          (nth 1 cond-node)
                        cond-node))
           (then (nth 1 kids))
           (else (nth 2 kids)))
      `(if ,(tl-aldor--lower-expr abn condition env)
           ,(if then (tl-aldor--lower-expr abn then env) nil)
         ,(if else (tl-aldor--lower-expr abn else env) nil)))))

(defun tl-aldor--lower-apply (abn node env)
  "Lower |Apply| NODE given environment ENV."
  (let ((kids (cdr node)))
    (when (null kids)
      (signal 'termlisp-aldor-error '("apply without a function")))
    (let* ((head (car kids))
           (args (cdr kids))
           (head-id-p (tl-abn-node-p head 'Id))
           (head-name (and head-id-p (cdr (tl-abn-id-name-cell head))))
           (head-syme (and head-id-p (tl-abn-id-syme head)))
           (owner (and head-syme (tl-aldor--syme-owner-sefo abn head-syme)))
           (owner-name (and owner (tl-aldor--sefo-head-name abn owner)))
           (head-ty (tl-aldor--expr-type-sefo abn head))
           (head-ty-name (and head-ty
                              (tl-aldor--sefo-head-name abn head-ty)))
           (projection (tl-aldor--try-projection abn node env)))
        (cond
         ;; `<<$String tr' reads the rest of the line as a String.
         ((and (tl-abn-node-p head 'Qualify)
               (= (length args) 1)
               (let ((b (nth 1 head)) (q (nth 2 head)))
                 (and (tl-abn-node-p b 'Id) (eq (tl-abn-id-name b) '<<)
                      (tl-abn-node-p q 'Id)
                      (eq (tl-abn-id-name q) 'String))))
          `(tl-read-line ,(tl-aldor--lower-expr abn (car args) env)))
         ;; An overloaded reserved operator the program redefines:
         ;; choose the method vs the prelude operator by unifying the
         ;; operand type with each signature (type-driven, not by name).
         ((and head-id-p
               tl-aldor--reserved-def-params
               (memq head-name tl-aldor--reserved-fns)
               (gethash head-name tl-aldor--reserved-def-params))
          (let* ((idx (tl-aldor--overload-operand-index head-name))
                 (operand (nth idx args))
                 (opnd-sefo (and operand (tl-aldor--expr-type-sefo abn operand)))
                 (opnd-head (and opnd-sefo
                                 (tl-aldor--sefo-head-name abn opnd-sefo)))
                 (opnd-ty (and opnd-sefo (tl-aldor--sefo-to-type abn opnd-sefo)))
                 ;; A Character operand (notably `newline') prints as a
                 ;; character, whether or not its syme is resolved.
                 (char-p (and (eq head-name '<<)
                              (or (eq opnd-head 'Character)
                                  (eq (and operand
                                           (tl-aldor--lower-expr abn operand env))
                                      'tl-newline))))
                 (prog-cands (mapcar (lambda (ps) (cons 'program (nth idx ps)))
                                     (gethash head-name
                                              tl-aldor--reserved-def-params)))
                 (prel (tl-aldor--prelude-overload-scheme head-name))
                 (res (and opnd-ty prel
                           (tl-resolve-overload-params
                            opnd-ty
                            (append prog-cands
                                    (list (cons 'prelude
                                                (tl-scheme-nth-param prel idx))))))))
            (cons (cond
                   ((eq res 'program)
                    (or (tl-aldor--mangled-def head) head-name))
                   (char-p 'tl-output-char)
                   (res (tl-aldor--prelude-overload-target head-name))
                   (t
                    ;; Unresolved (missing type info): keep the existing
                    ;; source-position-based decision.
                    (tl-aldor--lower-expr abn head env)))
                  (mapcar (lambda (a) (tl-aldor--lower-expr abn a env)) args))))
         ;; A prelude type application used as a value, e.g. `List I'.
         ((and head-id-p (tl-aldor--domain-id-p head))
          `(quote ,(tl-aldor--type-data abn node)))
        ;; Record construction: bracket exported by a Record type.
        ((and (eq head-name 'bracket) (eq owner-name 'Record))
        (cons 'Record
              (mapcar (lambda (arg) (tl-aldor--lower-expr abn arg env))
                      args)))
       ;; Union construction: bracket exported by a Union type.  The
       ;; branch tag identifies which component the value belongs to.
       ((and (eq head-name 'bracket) (eq owner-name 'Union))
        (let ((idx (tl-aldor--decl-index
                    abn (tl-aldor--sefo-declares owner)
                    (tl-aldor--union-bracket-tag abn head-syme owner))))
          (unless idx
            (signal 'termlisp-aldor-error '("union branch not in type")))
          (unless (= (length args) 1)
            (signal 'termlisp-aldor-error
                    '("union construction expects one argument")))
          `(Union ,idx ,(tl-aldor--lower-expr abn (car args) env))))
        ;; union v: wrap the payload in the branch picked by its
        ;; static type; the tag is inferred by the compiler.
        ((eq head-name 'union)
         (unless (= (length args) 1)
           (signal 'termlisp-aldor-error
                   '("union expects one argument")))
         (let* ((owner (or (and head-syme
                                (tl-aldor--syme-owner-sefo abn head-syme))
                           (tl-aldor--union-owner-sefo abn)))
                (declares (and owner (tl-aldor--sefo-declares owner)))
                (idx (or (tl-aldor--arrow-branch-index
                          abn head-syme declares)
                         (and declares
                              (tl-aldor--union-payload-index
                               abn declares (car args))))))
           (unless (and owner idx)
             (signal 'termlisp-aldor-error
                     '("union without an identifiable branch")))
           `(Union ,idx ,(tl-aldor--lower-expr abn (car args) env))))
        ;; [a, b, c] parses as bracket(a, b, c): fold into Cons chains.
        ;; A single comprehension argument is already the list.
        ((eq head-name 'bracket)
         (cond
          ;; A single comprehension argument is already the list.
          ((and (= (length args) 1)
                (tl-abn-node-p (car args) 'Collect))
           (tl-aldor--lower-expr abn (car args) env))
          ;; `[g]' over a generator is that generator's elements,
          ;; collected, not a one-element list.
          ((and (= (length args) 1)
                (eq (tl-aldor--sefo-head-name
                     abn (tl-aldor--expr-type-sefo abn (car args)))
                    'Generator))
           (tl-aldor--lower-generator-to-list abn (car args) env))
          (t
           (let ((form 'Nil))
             (dolist (arg (reverse args))
               (setq form (list 'Cons
                                (tl-aldor--lower-expr abn arg env)
                                form)))
             form))))
        ;; Union case test: case(u, tag).
        ((eq head-name 'case)
         (unless (and (eq owner-name 'Union) (= (length args) 2))
           (signal 'termlisp-aldor-error
                   '("case is only supported on unions")))
         (let* ((tag-arg (cadr args))
                ;; The branch tag may legitimately be named `nil',
                ;; so presence is decided by the name cell, not by
                ;; the name itself.
                (tag-cell (and (tl-abn-node-p tag-arg 'Id)
                               (tl-abn-id-name-cell tag-arg)))
                (idx (and tag-cell
                          (tl-aldor--decl-index
                           abn (tl-aldor--sefo-declares owner)
                           (cdr tag-cell)))))
           (unless idx
             (signal 'termlisp-aldor-error
                     (list (format "No union branch |%s|"
                                   (and tag-cell (cdr tag-cell))))))
           `(UnionCase ,(tl-aldor--lower-expr abn (car args) env) ,idx)))
       ;; Record/Union field projection: recv.tag.
       (projection)
        ;; Unary minus: -x.
        ((and (eq head-name '-) (= (length args) 1))
         (list '- (tl-aldor--lower-expr abn (car args) env)))
        ;; String constructor: new(n) is n spaces.
        ((and (eq head-name 'new) (= (length args) 1)
              (eq (tl-aldor--sefo-head-name
                   abn (tl-aldor--expr-type-sefo abn node))
                  'String))
         `(tl-new-string ,(tl-aldor--lower-expr abn (car args) env)
                         tl-space))
        ;; Array/String constructor: new(n, fill).
        ((and (eq head-name 'new) (= (length args) 2))
         (if (eq (tl-aldor--sefo-head-name
                  abn (tl-aldor--expr-type-sefo abn node))
                 'String)
             `(tl-new-string ,(tl-aldor--lower-expr abn (car args) env)
                             ,(tl-aldor--lower-expr abn (cadr args) env))
           `(NewArray ,(tl-aldor--lower-expr abn (car args) env)
                      ,(tl-aldor--lower-expr abn (cadr args) env))))
        ;; Array element read: arr(i).  The receiver may itself be
        ;; an application (`a(i)(j)'), so array-ness is taken from
        ;; the head expression's type; Array indexes are shifted to
        ;; the zero-based Lisp vector.
        ((and (= (length args) 1)
              (memq head-ty-name tl-aldor--array-type-names))
         `(ArrayRef ,(tl-aldor--lower-expr abn head env)
                    ,(tl-aldor--array-index-ir
                      head-ty-name
                      (tl-aldor--lower-expr abn (car args) env))))
        ;; Applying a function to a tuple expands it into the
        ;; function's argument list: `f (a, b, c)'.
        ((and (= (length args) 1)
              (tl-aldor--tuple-valued-p abn (car args)))
         `(ApplyTuple ,(tl-aldor--lower-expr abn head env)
                      ,(tl-aldor--lower-expr abn (car args) env)))
         ;; Unary `<< x' formats x as a String.
         ((and (eq head-name '<<) (= (length args) 1)
               (eq (tl-aldor--lower-id head env) 'tl-output-<<))
          `(tl-format ,(tl-aldor--lower-expr abn (car args) env)))
         ;; Prelude output: a Character operand prints as a character
         ;; (so `<< newline' emits a newline), everything else as text.
         ((and (eq head-name '<<) (= (length args) 2)
               (eq (tl-aldor--lower-id head env) 'tl-output-<<))
          (let* ((opnd (cadr args))
                 (ty (tl-aldor--sefo-head-name
                      abn (tl-aldor--expr-type-sefo abn opnd)))
                 (w (tl-aldor--lower-expr abn (car args) env))
                 (v (tl-aldor--lower-expr abn opnd env)))
            ;; A Character operand prints as a character; `newline' is
            ;; such a value even when its syme is not resolved.
            (if (or (eq ty 'Character) (eq v 'tl-newline))
                `(tl-output-char ,w ,v)
              `(tl-output-<< ,w ,v))))
         (t
          (let ((ptypes (and head-ty
                             (tl-aldor--fun-param-types abn head-ty))))
           (cons (tl-aldor--lower-expr abn head env)
                 (cl-loop for arg in args
                          for i from 0
                          for pt = (nth i ptypes)
                          collect
                          (if (and pt
                                   (eq (tl-aldor--sefo-head-name abn pt)
                                       'Generator))
                              (tl-aldor--lower-expr-gen abn arg env)
                            (tl-aldor--lower-expr abn arg env))))))))))

(defun tl-aldor--lower-lambda (abn lambda env)
  "Lower expression LAMBDA given environment ENV."
  (let* ((params (nth 1 lambda))
         (body (car (last (cdr lambda))))
         (names (tl-aldor--param-names params))
         (pre (cl-remove-if
               (lambda (n) (memq n names))
               (delete-dups (tl-aldor--expr-assign-names body))))
         (env1 (append (mapcar (lambda (n) (cons n n)) names)
                       (mapcar (lambda (n) (cons n n)) pre)
                       env)))
    `(lambda (,@names)
       ,(tl-aldor--prebind-let
         pre
         (tl-aldor--wrap-return
          body
          (tl-aldor--lower-expr abn body env1))))))

(defun tl-aldor--lower-where (abn node env)
  "Lower Where NODE given environment ENV.
Every child but the last is a local define; the last child is the
expression.  The defines become let bindings in source order, so a
later define may call an earlier one, and the expression lowers with
the names in scope."
  (let* ((kids (cdr node))
         (body (car (last kids)))
         (env1 env)
         (binds nil))
    (dolist (def (butlast kids))
      (unless (tl-abn-node-p def 'Define)
        (signal 'termlisp-aldor-error
                (list (format "Unsupported where element |%s|"
                              (car-safe def)))))
      (let ((decl (nth 1 def))
            (value (nth 2 def)))
        (unless (tl-abn-node-p decl 'Declare)
          (signal 'termlisp-aldor-error
                  '("where define without declaration")))
        (let ((name (tl-aldor--decl-name decl)))
          (push (list name
                      (if (tl-abn-node-p value 'Lambda)
                          (tl-aldor--lower-lambda abn value env1)
                        (tl-aldor--lower-expr abn value env1)))
                binds)
          (setq env1 (cons (cons name name) env1)))))
    `(Let ,(nreverse binds)
          ,(tl-aldor--lower-expr abn body env1))))

;;; Loop support.
;;;
;;; A `Repeat' breaks the substitution model: its body runs many
;;; times, so locals assigned inside must become real variables.
;;; Lowering scans the raw body for assignment targets already bound,
;;; closes that set over value dependencies, and binds the entry
;;; values in a Let that covers the loop and the rest of the
;;; sequence.  Inside the loop those names read and write the
;;; variable; the loop machinery itself (iterator variable, segment
;;; bounds, list walk) is bound by a second Let inside the core.
;;; Break and iterate compile to throws caught by fixed tags; the
;;; innermost catch of a nested loop wins.

(defvar tl-aldor--loop-depth 0
  "Number of Repeat nodes currently being lowered.
Break and iterate are only valid while this is positive.")

(defvar tl-aldor--goto-region nil
  "Non-nil while lowering a labeled region (a sequence with gotos.
Names the region assigns are pre-bound as variables at the region top,
and nested sequences must not re-enter labeled lowering.")

(defun tl-aldor--goto-prebind-names (node)
  "Return the names a labeled (goto) region around NODE must pre-bind.
Jumps skip and repeat statements, so substitution bindings would read
stale values; every name the region introduces becomes a top-level
variable instead.  Nested lambdas keep their own scope."
  (let ((names nil))
    (cl-labels ((add (n) (when (and n (symbolp n)) (push n names)))
                (walk (n)
                  (when (consp n)
                    (cond
                     ((eq (car n) 'Lambda) nil)
                     ((eq (car n) 'Sequence)
                      (dolist (c (cdr n)) (walk c)))
                     ((eq (car n) 'Local)
                      (let ((inner (nth 1 n)))
                        (when (tl-abn-node-p inner 'Declare)
                          (let ((name-node (nth 1 inner)))
                            (if (tl-abn-node-p name-node 'Comma)
                                (dolist (id (cdr name-node))
                                  (when (tl-abn-node-p id 'Id)
                                    (add (tl-abn-id-name id))))
                              (when (tl-abn-node-p name-node 'Id)
                                (add (tl-abn-id-name name-node))))))
                        (walk inner)))
                     ((and (eq (car n) 'Assign)
                           (tl-abn-node-p (nth 1 n) 'Id))
                      (add (tl-abn-id-name (nth 1 n)))
                      (walk (nth 2 n)))
                     ((and (eq (car n) 'Assign)
                           (tl-abn-node-p (nth 1 n) 'Declare))
                      (add (tl-aldor--decl-name (nth 1 n)))
                      (walk (nth 2 n)))
                     ((eq (car n) 'Declare) nil)
                     (t (walk (car n))
                        (when (consp (cdr n))
                          (walk (cdr n))))))))
      (walk node))
    (delete-dups (nreverse names))))

(defun tl-aldor--split-labels (elems)
  "Split ELEMS into labeled segments ((BOUND . SEG-ELEMS) ...).
BOUND is the label that starts the segment: `start' for elements
leading before any Label, then each Label's name.  The Label
elements themselves are consumed as boundaries."
  (let ((segs nil)
        (cur nil)
        (bound 'start))
    (dolist (e elems)
      (if (tl-abn-node-p e 'Label)
          (let ((name (and (tl-abn-node-p (nth 1 e) 'Id)
                           (tl-abn-id-name (nth 1 e)))))
            (unless name
              (signal 'termlisp-aldor-error '("label without a name")))
            (push (cons bound (nreverse cur)) segs)
            (setq bound name
                  cur nil)
            ;; The labeled statement opens the new segment.
            (when (nth 2 e)
              (push (nth 2 e) cur)))
        (push e cur)))
    (push (cons bound (nreverse cur)) segs)
    (nreverse segs)))

(defun tl-aldor--lower-jump (kind)
  "Lower a break/iterate of KIND when inside a loop."
  (unless (> tl-aldor--loop-depth 0)
    (signal 'termlisp-aldor-error
            (list (format "%s outside of a loop"
                          (if (eq kind 'Break) "break" "iterate")))))
  (list kind))

(defconst tl-aldor--stable-ops
  '(+
    - * / quo mod ^ gcd min max
    = ~= < <= > >= and or not
    cons first rest empty? nil?
    ListFirst ListRest ListEmpty
    zero? even? odd?
    char substring concat rightTrim length)
  "Operators whose application is a stable (pure, immutable) value.
Substituting such an expression at each use is sound.  Constructors that
allocate mutable objects (`bracket', `new', `Record', `Union') are NOT
stable: each evaluation must be bound once so aliases share the object.")

(defconst tl-aldor--value-type-heads
  '(AldorInteger Integer SingleInteger MachineInteger DoubleFloat Float
    Boolean Character String List Generator Unit ->)
  "Type head names whose values are immutable (safe to substitute).
Anything else -- Record, Union, Array, File, a domain -- is a handle.")

(defun tl-aldor--handle-type-head-p (head)
  "Non-nil when type-head name HEAD denotes a mutable/handle type."
  (and head (not (memq head tl-aldor--value-type-heads))))

(defun tl-aldor--stable-rhs-p (node)
  "Non-nil when re-evaluating NODE is observationally equivalent.
A literal, identifier, lambda, or tuple of stable values is stable, as
is a pure operator applied to stable arguments.  Calls to user-defined
or effectful functions, allocation (`new'), generators and comprehensions
are not: they may allocate, mutate, or have effects, so their result must
be bound to a variable exactly once rather than substituted."
  (cond
   ((tl-abn-node-p node 'Id) t)
   ((tl-abn-node-p node 'LitInteger) t)
   ((tl-abn-node-p node 'LitFloat) t)
   ((tl-abn-node-p node 'LitString) t)
   ((tl-abn-node-p node 'LitChar) t)
   ((tl-abn-node-p node 'Lambda) t)
   ((tl-abn-node-p node 'Comma)
    (cl-every #'tl-aldor--stable-rhs-p (cdr node)))
   ((tl-abn-node-p node 'Apply)
    (let ((h (nth 1 node)))
      (and (tl-abn-node-p h 'Id)
           (memq (tl-abn-id-name h) tl-aldor--stable-ops)
           (cl-every #'tl-aldor--stable-rhs-p (cddr node)))))
   (t nil)))

(defun tl-aldor--contains (node tag)
  "Return non-nil when raw ABN NODE contains a node headed by TAG.
Dotted annotation pairs inside the tree are traversed safely."
  (cond ((not (consp node)) nil)
        ((eq (car node) tag) t)
        (t (or (tl-aldor--contains (car node) tag)
               (and (consp (cdr node))
                    (tl-aldor--contains (cdr node) tag))))))

(defun tl-aldor--assigned-names (node)
  "Return the names assigned by raw ABN NODE, left to right.
Lambda bodies are not traversed."
  (let (names)
    (cl-labels
        ((walk (x)
           (when (consp x)
             (cond
              ((eq (car x) 'Lambda) nil)
              ((eq (car x) 'Assign)
               (let ((lhs (nth 1 x)))
                 (cond
                  ((tl-abn-node-p lhs 'Id)
                   (let ((name (tl-abn-id-name lhs)))
                     (when name (push name names))))
                  ;; r.tag := v mutates the receiver too.
                  ((tl-abn-node-p lhs 'Apply)
                   (let ((recv (nth 1 lhs)))
                     (when (tl-abn-node-p recv 'Id)
                       (let ((name (tl-abn-id-name recv)))
                         (when name (push name names))))))))
                (walk (nth 1 x))
                (walk (nth 2 x)))
              ;; A `for v in ...' reuses an existing V, so it counts as
              ;; an assignment to it.
              ((eq (car x) 'For)
               (let ((name (tl-aldor--iter-name (nth 1 x))))
                 (when name (push name names)))
               (walk (nth 2 x))
               (walk (nth 3 x)))
              (t (let ((rest x))
                   (while (consp rest)
                     (walk (car rest))
                     (setq rest (cdr rest)))))))))
      (walk node))
    (nreverse names)))

(defun tl-aldor--refs-p (form names)
  "Return non-nil when FORM mentions one of NAMES as a variable.
Quoted data and function cells are not variable references, and
lambda parameters shadow the names they bind."
  (cond ((symbolp form) (memq form names))
        ((not (consp form)) nil)
        ((memq (car form) '(quote function)) nil)
        ((and (eq (car form) 'lambda) (listp (nth 1 form)))
         (tl-aldor--refs-p (cddr form)
                           (cl-remove-if (lambda (n) (memq n (nth 1 form)))
                                         names)))
        (t (or (tl-aldor--refs-p (car form) names)
               (tl-aldor--refs-p (cdr form) names)))))

(defun tl-aldor--promotion-closure (frame mutable)
  "Extend MUTABLE with FRAME entries whose values mention it.
A substitution value that reads a mutated name would otherwise
observe later updates, so such entries must be captured (rebound to
their entry value) together with the mutated names."
  (let ((result mutable) (changed t))
    (while changed
      (setq changed nil)
      (dolist (entry frame)
        (when (and (consp entry)
                   (not (memq (car entry) result))
                   (tl-aldor--refs-p (cdr entry) result))
          (push (car entry) result)
          (setq changed t))))
    result))

(defun tl-aldor--prepare-repeat (abn node frame locals)
  "Promote mutated locals and lower Repeat NODE.
Return a list (FRAME1 LOCALS1 BINDS CORE) where FRAME1 maps every
promoted name to itself, LOCALS1 extends the assignable names, BINDS
are the Let bindings capturing entry values, and CORE is the lowered
loop."
  (let* ((mutable (delete-dups
                   (tl-aldor--promotion-closure
                    frame (tl-aldor--assigned-names node))))
         (binds (mapcar (lambda (m) (list m (cdr (assq m frame)))) mutable))
         (frame1 (append (mapcar (lambda (m) (cons m m)) mutable)
                         (cl-remove-if (lambda (e) (memq (car e) mutable))
                                       frame)))
         (locals1 (append mutable locals))
         (core (tl-aldor--lower-repeat abn node frame1 locals1)))
    (list frame1 locals1 binds core)))

(defun tl-aldor--lower-expr-repeat (abn node frame)
  "Lower standalone Repeat NODE with no continuation expression."
  (pcase-let ((`(,_frame ,_locals ,binds ,core)
               (tl-aldor--prepare-repeat abn node frame nil)))
    (if binds `(Let ,binds ,core) core)))

(defvar tl-aldor--gen-blocks nil
  "Accumulator of (LABEL . CODE) states while flattening a generator.")

(defun tl-aldor--gen-vars (ir acc)
  "Collect variable names bound inside IR into ACC."
  (cond
   ((not (consp ir)) acc)
   ((memq (car ir) '(quote function)) acc)
   ((eq (car ir) 'Let)
    (dolist (b (nth 1 ir))
      (unless (memq (car b) acc) (push (car b) acc))
      (setq acc (tl-aldor--gen-vars (cadr b) acc)))
    (dolist (e (cddr ir)) (setq acc (tl-aldor--gen-vars e acc)))
    acc)
   ((eq (car ir) 'Setq)
    (unless (memq (nth 1 ir) acc) (push (nth 1 ir) acc))
    (tl-aldor--gen-vars (nth 2 ir) acc))
   (t (dolist (e (cdr ir)) (setq acc (tl-aldor--gen-vars e acc)))
      acc)))

(defun tl-aldor--gen-advance (k)
  "IR to jump to state K through the dispatch loop."
  `(Seq (Setq %pc (quote ,k)) (Throw tl-seq-next nil)))

(defun tl-aldor--gen-block (code)
  "Record a state running CODE and return its label."
  (let ((l (tl-aldor--gen-fresh "%gl")))
    (push (cons l code) tl-aldor--gen-blocks)
    l))

(defun tl-aldor--gen-seq (forms k)
  "Flatten FORMS so control continues at state K; return entry label."
  (if (null forms)
      k
    (tl-aldor--gen-flat (car forms) (tl-aldor--gen-seq (cdr forms) k))))

(defun tl-aldor--gen-flat (ir k)
  "Flatten IR into states, continuing at K; return the entry label.
Loops, conditionals and `Yield' become labelled states so a `yield'
can suspend and later resume at the right point."
  (pcase (car-safe ir)
    ('nil k)
    ('Seq (tl-aldor--gen-seq (cdr ir) k))
    ('Let
     (let ((setqs (mapcar (lambda (b) (list 'Setq (car b) (cadr b)))
                          (nth 1 ir))))
       (tl-aldor--gen-seq (append setqs (cddr ir)) k)))
    ('While
     (let* ((lstart (tl-aldor--gen-fresh "%gl"))
            (entry (tl-aldor--gen-seq (cddr ir) lstart)))
       (push (cons lstart
                   `(if ,(nth 1 ir)
                        ,(tl-aldor--gen-advance entry)
                      ,(tl-aldor--gen-advance k)))
             tl-aldor--gen-blocks)
       lstart))
    ('if
     (let* ((lt (tl-aldor--gen-flat (nth 2 ir) k))
            (le (tl-aldor--gen-flat (nth 3 ir) k))
            (l (tl-aldor--gen-fresh "%gl")))
       (push (cons l
                   `(if ,(nth 1 ir)
                        ,(tl-aldor--gen-advance lt)
                      ,(tl-aldor--gen-advance le)))
             tl-aldor--gen-blocks)
       l))
    ('Yield
     (tl-aldor--gen-block
      `(Seq (Setq %pc (quote ,k)) (Throw tl-gen-yield ,(nth 1 ir)))))
    (_
     (tl-aldor--gen-block `(Seq ,ir ,(tl-aldor--gen-advance k))))))

(defun tl-aldor--gen-peel-lets (ir binds)
  "Peel a leading Let chain from IR, returning (BINDS . REST).
The bindings initialize once when the generator is created."
  (if (and (consp ir) (eq (car ir) 'Let))
      (let ((body (cddr ir)))
        (tl-aldor--gen-peel-lets
         (if (cdr body) (cons 'Seq body) (car body))
         (append binds (nth 1 ir))))
    (list binds ir)))

(defun tl-aldor--lower-expr-gen (abn node env)
  "Lower NODE in a position where a Generator value is expected.
A comprehension `e for v in g' is a Generator here, not a list."
  (if (tl-abn-node-p node 'Collect)
      (let ((tl-aldor--collect-as-generator t))
        (tl-aldor--lower-expr abn node env))
    (tl-aldor--lower-expr abn node env)))

(defun tl-aldor--ir-to-generator (core)
  "Wrap resumable body IR CORE in a state-machine generator closure."
  (let* ((peel (tl-aldor--gen-peel-lets core nil))
         (binds (car peel))
         (rest (cadr peel))
         (vars (cl-remove-if (lambda (v) (assq v binds))
                             (tl-aldor--gen-vars rest nil)))
         (tl-aldor--gen-blocks nil)
         (entry (tl-aldor--gen-flat rest 'done))
         (chain nil))
    (push (cons 'done '(Throw tl-gen-done (quote tl-gen-done)))
          tl-aldor--gen-blocks)
    (setq chain '(error "invalid generator state"))
    (dolist (b tl-aldor--gen-blocks)
      (setq chain `(if (eq %pc (quote ,(car b))) ,(cdr b) ,chain)))
    `(Let ((%pc (quote ,entry))
           ,@binds
           ,@(mapcar (lambda (v) (list v nil)) vars))
       (lambda ()
         (Catch tl-gen-yield
           (Catch tl-gen-done
             (While True
               (Catch tl-seq-next
                 ,chain))))))))

(defun tl-aldor--lower-generate-lazy (abn body env)
  "Lower Generate BODY to a resumable state-machine closure."
  (let* ((tl-aldor--generating t)
         (core (if (tl-abn-node-p body 'Repeat)
                   (tl-aldor--lower-expr-repeat abn body env)
                 (tl-aldor--lower-expr abn body env))))
    (tl-aldor--ir-to-generator core)))

(defun tl-aldor--lower-generate (abn expr env)
  "Lower Generate NODE to a generator value.
The value is a zero-argument closure; each call resumes the body and
returns the next yielded value, or the symbol `tl-gen-done' when the
body finishes.  Bodies with break/iterate/goto keep the eager list
lowering, which cannot suspend."
  (let ((body (if (nth 2 expr) (nth 2 expr) (nth 1 expr))))
    (if (or (tl-aldor--contains body 'Break)
            (tl-aldor--contains body 'Iterate)
            (tl-aldor--contains body 'Goto))
        (let* ((tl-aldor--yield-var '%yield)
               (core (if (tl-abn-node-p body 'Repeat)
                         (tl-aldor--lower-expr-repeat abn body env)
                       (tl-aldor--lower-expr abn body env))))
          `(Let ((%yield Nil)) ,core ,(tl-aldor--ir-reverse '%yield)))
      (tl-aldor--lower-generate-lazy abn body env))))

(defun tl-aldor--iter-name (lhs)
  "Return the variable name of a for-loop target LHS, or nil."
  (let ((l (if (tl-abn-node-p lhs 'Free) (nth 1 lhs) lhs)))
    (and (tl-abn-node-p l 'Id) (tl-abn-id-name l))))

(defun tl-aldor--iter-parts (abn iter frame)
  "Return (VAR LETBINDS PRE BIND COND STEP) for one lockstep loop ITER.
LETBINDS bind fresh names before the loop; PRE runs once before the
loop (assigning an already-promoted loop variable); BIND runs each
iteration.  COND advances a pull-based generator and tests for
exhaustion.  Returns nil when ITER is unsupported."
  (cond
   ((eq (car iter) 'While)
    (let* ((cond-node (nth 1 iter))
           (condition (if (tl-abn-node-p cond-node 'Test)
                          (nth 1 cond-node)
                        cond-node)))
      (list nil nil nil nil (tl-aldor--lower-expr abn condition frame) nil nil)))
   ((eq (car iter) 'For)
    (let ((var (tl-aldor--iter-name (nth 1 iter)))
          (gen (nth 2 iter)))
      (when var
        (let* ((promoted (and (assq var frame)
                              (eq (cdr (assq var frame)) var)))
               (segment (tl-aldor--segment-of gen)))
          (cond
           (segment
            (let ((lo (tl-aldor--lower-expr abn (nth 0 segment) frame))
                  (hi (tl-aldor--lower-expr abn (nth 1 segment) frame))
                  (st (if (nth 2 segment)
                          (tl-aldor--lower-expr abn (nth 2 segment) frame)
                        1))
                  (hisym (tl-aldor--gen-fresh "%hi"))
                  (stsym (tl-aldor--gen-fresh "%st"))
                  (sgn (tl-aldor--gen-fresh "%sgn")))
              ;; The loop variable advances before each body run, so
              ;; it holds the last iterated value after the loop.
              (list var
                    (list (list hisym hi) (list stsym st)
                          (list sgn `(if (< ,stsym 0) -1 1))
                          (unless promoted (list var `(- ,lo ,st))))
                    (when promoted (list `(Setq ,var (- ,lo ,st))))
                    `(Setq ,var (+ ,var ,stsym))
                    `(<= (* ,sgn (- (+ ,var ,stsym) ,hisym)) 0)
                    nil
                    nil)))
           ((eq (tl-aldor--sefo-head-name
                 abn (tl-aldor--expr-type-sefo abn gen)) 'Generator)
            (let ((genv (tl-aldor--gen-fresh "%gen"))
                  (elt (tl-aldor--gen-fresh "%ge")))
              (list var
                    (list (list genv (tl-aldor--lower-expr-gen abn gen frame))
                          (list elt nil)
                          (unless promoted (list var nil)))
                    nil
                    `(Setq ,var ,elt)
                    `(Seq (Setq ,elt (funcall ,genv))
                          (not (eq ,elt (quote tl-gen-done))))
                    nil
                    nil)))
           (t
            (let ((walk (tl-aldor--gen-fresh "%walk")))
              (list var
                    (list (list walk (tl-aldor--lower-expr abn gen frame))
                          (unless promoted (list var nil)))
                    nil
                    `(Setq ,var (ListFirst ,walk))
                    `(not (ListEmpty ,walk))
                    `(Setq ,walk (ListRest ,walk))
                    nil))))))))))

(defun tl-aldor--lower-repeat (abn node frame locals)
  "Lower Repeat NODE given FRAME and LOCALS.
FRAME already maps every mutated name to its variable."
  (let* ((kids (cdr node))
         (body (car kids))
         (iters (cdr kids))
         (tl-aldor--loop-depth (1+ tl-aldor--loop-depth)))
    (unless body
      (signal 'termlisp-aldor-error '("repeat without a body")))
    (cond
     ;; repeat { ... } with no iterator: loop forever.
     ((null iters)
      (tl-aldor--wrap-break
       body
       `(While True
          ,(tl-aldor--wrap-iterate
            body
            (tl-aldor--lower-loop-body abn body frame locals)))))
     ;; Several iterators advance in lockstep: `for a in xs, b in ys'.
     ;; Pull-based iterators advance together, so an infinite inner
     ;; generator is bounded by a finite outer one.
      ((cdr iters)
       (let ((parts (mapcar (lambda (it)
                             (tl-aldor--iter-parts abn it frame))
                           iters)))
        (if (cl-every #'identity parts)
            (let* ((vars (delq nil (mapcar #'car parts)))
                   (frame1 (append (mapcar (lambda (v) (cons v v)) vars)
                                   frame))
                   (body-ir (tl-aldor--lower-loop-body abn body frame1 locals))
                   (body-ir (let ((acc body-ir))
                              (dolist (it iters acc)
                                (setq acc (tl-aldor--filter-wrap
                                           abn (nth 3 it) acc frame1)))))
                   (inits (delq nil (apply #'append
                                           (mapcar #'cadr parts))))
                   (pres (delq nil (apply #'append
                                          (mapcar (lambda (p) (nth 2 p)) parts))))
                   (binds (delq nil (mapcar (lambda (p) (nth 3 p)) parts)))
                   (conds (mapcar (lambda (p) (nth 4 p)) parts))
                   (steps (delq nil (mapcar (lambda (p) (nth 5 p)) parts)))
                   (posts (delq nil (apply #'append
                                           (mapcar (lambda (p) (nth 6 p)) parts))))
                   (loop `(While ,(if (cdr conds) (cons 'and conds) (car conds))
                             ,@binds
                             ,body-ir
                             ,@steps)))
               (tl-aldor--wrap-break
                body
                `(Let ,inits
                   ,(if (or pres posts)
                        (cons 'Seq (append pres (list loop) posts))
                      loop))))
           (tl-aldor--lower-repeat
           abn
           (cons 'Repeat
                 (cons (cons 'Repeat (cons body (cdr iters)))
                       (list (car iters))))
           frame locals))))
     (t
      (let ((iter (car iters)))
        (pcase (car iter)
          ('While
           (let* ((cond-node (nth 1 iter))
                  (condition (if (tl-abn-node-p cond-node 'Test)
                                 (nth 1 cond-node)
                               cond-node))
                  (test-ir (tl-aldor--lower-expr abn condition frame))
                  (body-ir (tl-aldor--wrap-iterate
                            body
                            (tl-aldor--lower-loop-body abn body
                                                       frame locals))))
             (tl-aldor--wrap-break body `(While ,test-ir ,body-ir))))
          ('For (tl-aldor--lower-for abn body iter frame locals))
          (_ (signal 'termlisp-aldor-error
                     (list (format "Unsupported loop iterator |%s|"
                                   (car iter)))))))))))

(defun tl-aldor--wrap-iterate (body-raw body-ir)
  "Wrap BODY-IR in an iterate catch when BODY-RAW contains iterate."
  (if (tl-aldor--contains body-raw 'Iterate)
      `(Catch tl-loop-next ,body-ir)
    body-ir))

(defun tl-aldor--wrap-break (body-raw loop-ir)
  "Wrap LOOP-IR in a break catch when BODY-RAW contains break."
  (if (tl-aldor--contains body-raw 'Break)
      `(Catch tl-loop-break ,loop-ir)
    loop-ir))

(defun tl-aldor--wrap-return (body-raw body-ir)
  "Wrap BODY-IR in a function-return catch when BODY-RAW contains return."
  (if (tl-aldor--contains body-raw 'Return)
      `(Catch tl-fn-return ,body-ir)
    body-ir))

(defun tl-aldor--lower-loop-body (abn body frame locals)
  "Lower loop BODY given FRAME and LOCALS as a sequence.
A single-statement body is wrapped in a Sequence first."
  (if (tl-abn-node-p body 'Sequence)
      (tl-aldor--lower-sequence abn body frame locals)
    (tl-aldor--lower-sequence abn (list 'Sequence body) frame locals)))

(defun tl-aldor--filter-wrap (abn filter body-ir frame)
  "Wrap BODY-IR in a filter test when FILTER (a raw Test) is present."
  (if (null filter)
      body-ir
    (let ((condition (if (tl-abn-node-p filter 'Test)
                         (nth 1 filter)
                       filter)))
      `(if ,(tl-aldor--lower-expr abn condition frame) ,body-ir nil))))

(defun tl-aldor--segment-of (gen)
  "Return (LO HI STEP) for segment generator GEN, or nil.
STEP is the raw step expression, or nil for the default +1.  GEN is
raw ABN: `lo..hi' parses as Apply(`..', lo, hi) and `lo..hi by s' as
Apply(`by', seg, s)."
  (when (tl-abn-node-p gen 'Apply)
    (let* ((head (nth 1 gen))
           (head-name (and (tl-abn-node-p head 'Id) (tl-abn-id-name head))))
      (cond
       ((eq head-name '..)
        (when (and (nth 2 gen) (nth 3 gen))
          (list (nth 2 gen) (nth 3 gen) nil)))
       ((eq head-name 'by)
        (let* ((seg (nth 2 gen))
               (shead (nth 1 seg))
               (sname (and (tl-abn-node-p seg 'Apply)
                           (tl-abn-node-p shead 'Id)
                           (tl-abn-id-name shead))))
          (unless (eq sname '..)
            (signal 'termlisp-aldor-error
                    '("by without a segment generator")))
          (unless (and (nth 2 seg) (nth 3 seg) (nth 3 gen))
            (signal 'termlisp-aldor-error
                    '("malformed segment generator")))
          (list (nth 2 seg) (nth 3 seg) (nth 3 gen))))))))

(defun tl-aldor--lower-for (abn body iter frame locals)
  "Lower For ITER with loop BODY given FRAME and LOCALS."
  (let* ((lhs0 (nth 1 iter))
         ;; `for free i in ...' wraps the variable in a Free node.
         (lhs (if (tl-abn-node-p lhs0 'Free) (nth 1 lhs0) lhs0))
         (gen (nth 2 iter))
         (filter (nth 3 iter)))
    (unless (tl-abn-node-p lhs 'Id)
      (signal 'termlisp-aldor-error '("unsupported for-loop target")))
    (let ((var (tl-abn-id-name lhs))
          (segment (tl-aldor--segment-of gen)))
      (unless var
        (signal 'termlisp-aldor-error '("for-loop without a variable")))
      (if segment
          (tl-aldor--lower-for-segment abn body var segment filter
                                       frame locals)
        (tl-aldor--lower-for-list abn body var gen filter frame locals)))))

(defun tl-aldor--lower-for-segment (abn body var segment filter frame
                                        locals)
  "Lower an integer segment loop over SEGMENT (LO HI STEP-RAW).
The direction is taken from the step's runtime sign so that `by'
generators of either direction work; the default step is +1."
  (let* ((lo-ir (tl-aldor--lower-expr abn (nth 0 segment) frame))
         (hi-ir (tl-aldor--lower-expr abn (nth 1 segment) frame))
         (st-ir (if (nth 2 segment)
                    (tl-aldor--lower-expr abn (nth 2 segment) frame)
                  1))
         (frame1 (cons (cons var var) frame))
         (body-ir (tl-aldor--lower-loop-body abn body frame1 locals))
         (body-ir (tl-aldor--filter-wrap abn filter body-ir frame1))
         (body-ir (tl-aldor--wrap-iterate body body-ir))
         (while-form
          `(While (<= (* %sgn (- ,var %hi)) 0)
             ,body-ir
             (Setq ,var (+ ,var %st)))))
    `(Let ((,var ,lo-ir)
           (%hi ,hi-ir)
           (%st ,st-ir)
           (%sgn (if (< %st 0) -1 1)))
       ,(tl-aldor--wrap-break body while-form))))

(defun tl-aldor--list-walk-ops (abn gen)
  "Return (FIRST REST EMPTY) operation names for walking GEN.
A List-typed expression uses the internal always-inlined names; any
other expression keeps `first'/`rest'/`empty?', which the emitter
inlines over Cons data or leaves to the program's own definitions."
  (let ((head (tl-aldor--sefo-head-name
               abn (tl-aldor--expr-type-sefo abn gen))))
    (if (eq head 'List)
        '(ListFirst ListRest ListEmpty)
      '(first rest empty?))))

(defun tl-aldor--lower-for-list (abn body var gen filter frame locals)
  "Lower a generator loop: bind VAR to each element of GEN.
A Generator-typed GEN is pulled one element per iteration; anything
else is walked as a termlisp Cons list."
  (let* ((gen-head (tl-aldor--sefo-head-name
                    abn (tl-aldor--expr-type-sefo abn gen)))
         (gen-ir (tl-aldor--lower-expr-gen abn gen frame))
         (frame1 (cons (cons var var) frame))
         (body-ir (tl-aldor--lower-loop-body abn body frame1 locals))
         (body-ir (tl-aldor--filter-wrap abn filter body-ir frame1))
         (body-ir (tl-aldor--wrap-iterate body body-ir)))
    (cond
     ((eq gen-head 'String)
      (let ((strv (tl-aldor--gen-fresh "%str"))
            (idx (tl-aldor--gen-fresh "%gi")))
        `(Let ((,strv ,gen-ir) (,idx 0) (,var nil))
           ,(tl-aldor--wrap-break
             body
             `(While (< ,idx (length ,strv))
                (Setq ,var (aref ,strv ,idx))
                ,body-ir
                (Setq ,idx (1+ ,idx)))))))
     ((eq gen-head 'Generator)
      (let ((genv (tl-aldor--gen-fresh "%gen"))
            (elt (tl-aldor--gen-fresh "%ge")))
        `(Let ((,genv ,gen-ir) (,elt nil) (,var nil))
           ,(tl-aldor--wrap-break
             body
             `(While (Seq (Setq ,elt (funcall ,genv))
                          (not (eq ,elt (quote tl-gen-done))))
                (Setq ,var ,elt)
                ,body-ir)))))
     (t
      (let ((ops (tl-aldor--list-walk-ops abn gen)))
        `(Let ((%walk (tl-elements ,gen-ir)) (,var nil))
           ,(tl-aldor--wrap-break
             body
             `(While (not (,(nth 2 ops) %walk))
                (Setq ,var (,(nth 0 ops) %walk))
                ,body-ir
                (Setq %walk (,(nth 1 ops) %walk))))))))))

(defun tl-aldor--lower-generator-to-list (abn gen env)
  "Collect the generator GEN into a termlisp Cons list."
  (let ((genv (tl-aldor--gen-fresh "%gen"))
        (elt (tl-aldor--gen-fresh "%ge")))
    `(Let ((%collect Nil) (,genv ,(tl-aldor--lower-expr abn gen env))
           (,elt nil))
       (While (Seq (Setq ,elt (funcall ,genv))
                   (not (eq ,elt (quote tl-gen-done))))
         (Setq %collect (Cons ,elt %collect)))
       ,(tl-aldor--ir-reverse '%collect))))

(defun tl-aldor--ir-reverse (list-ir)
  "IR to reverse the tagged list LIST-IR, front-consing onto an accumulator."
  `(Let ((%rv Nil) (%rl ,list-ir))
        (While (not (ListEmpty %rl))
               (Setq %rv (Cons (ListFirst %rl) %rv))
               (Setq %rl (ListRest %rl)))
        %rv))

(defun tl-aldor--lower-collect (abn expr env)
  "Lower `[e for v in gen | filt]' (a Collect EXPR) to a list build.
The elements are produced in generator order."
  (let ((value (nth 1 expr))
        (for (nth 2 expr)))
    (unless (tl-abn-node-p for 'For)
      (signal 'termlisp-aldor-error
              '("collect without a for generator")))
    (let* ((lhs (nth 1 for))
           (gen (nth 2 for))
           (filter (nth 3 for))
           (var (and (tl-abn-node-p lhs 'Id) (tl-abn-id-name lhs))))
      (unless var
        (signal 'termlisp-aldor-error
                '("collect without a variable")))
      (let* ((frame1 (cons (cons var var) env))
             (value-ir (tl-aldor--lower-expr abn value frame1))
             (gen-p tl-aldor--collect-as-generator)
             (str-p (and (not gen-p)
                         (eq (tl-aldor--sefo-head-name
                              abn (tl-aldor--expr-type-sefo abn value))
                             'Character)))
             (step-ir (cond (gen-p `(Yield ,value-ir))
                            (str-p `(Setq %collect
                                          (concat %collect (string ,value-ir))))
                            (t `(Setq %collect (Cons ,value-ir %collect)))))
             (step-ir (tl-aldor--filter-wrap abn filter step-ir frame1))
             (segment (tl-aldor--segment-of gen))
             (loop
              (if segment
                  (let* ((lo-ir (tl-aldor--lower-expr abn (nth 0 segment) frame1))
                         (hi-ir (tl-aldor--lower-expr abn (nth 1 segment) frame1))
                         (st-ir (if (nth 2 segment)
                                    (tl-aldor--lower-expr abn (nth 2 segment) frame1)
                                  1)))
                    `(Let ((,var ,lo-ir) (%hi ,hi-ir) (%st ,st-ir)
                           (%sgn (if (< %st 0) -1 1)))
                       (While (<= (* %sgn (- ,var %hi)) 0)
                         ,step-ir
                         (Setq ,var (+ ,var %st)))))
                (let* ((gen-ir (tl-aldor--lower-expr-gen abn gen frame1))
                       (gen-head (tl-aldor--sefo-head-name
                                  abn (tl-aldor--expr-type-sefo abn gen))))
                   (cond
                    ((eq gen-head 'String)
                     (let ((strv (tl-aldor--gen-fresh "%str"))
                           (idx (tl-aldor--gen-fresh "%gi")))
                       `(Let ((,strv ,gen-ir) (,idx 0) (,var nil))
                          (While (< ,idx (length ,strv))
                            (Setq ,var (aref ,strv ,idx))
                            ,step-ir
                            (Setq ,idx (1+ ,idx))))))
                    ((eq gen-head 'Generator)
                     (let ((genv (tl-aldor--gen-fresh "%gen"))
                           (elt (tl-aldor--gen-fresh "%ge")))
                       `(Let ((,genv ,gen-ir) (,elt nil) (,var nil))
                          (While (Seq (Setq ,elt (funcall ,genv))
                                      (not (eq ,elt (quote tl-gen-done))))
                            (Setq ,var ,elt)
                            ,step-ir))))
                    (t
                     (let ((ops (tl-aldor--list-walk-ops abn gen)))
                       `(Let ((%walk (tl-elements ,gen-ir)) (,var nil))
                          (While (not (,(nth 2 ops) %walk))
                            (Setq ,var (,(nth 0 ops) %walk))
                            ,step-ir
                            (Setq %walk (,(nth 1 ops) %walk)))))))))))
        (if gen-p
            (tl-aldor--ir-to-generator loop)
          `(Let ((%collect ,(if str-p "" 'Nil)))
             ,loop
             ,(if str-p '%collect (tl-aldor--ir-reverse '%collect))))))))

(defun tl-aldor--lower-sequence (abn node env &optional locals)
  "Lower |Sequence| NODE given environment ENV and LOCALS.
Elements are processed left to right.  Local declarations and
assignments are lowered by substitution: the environment maps each
local to its current lowered value.  An (Exit (Test COND) VALUE)
element -- Aldor's `cond => value' -- becomes a nested if, with the
remaining elements as the else branch.  A Repeat element promotes the
locals it mutates into variables (see `tl-aldor--prepare-repeat') and
wraps itself and the remaining elements in a Let; statement-position
If/break/iterate lower to a Seq so their effects run before the rest.
Assignment writes the variable of a parameter or loop-promoted local,
rebinds a substitution local, or introduces an implicit local, as in
Aldor.  Non-final elements outside the supported statement forms are
rejected."
  (cl-labels
      ((lower (frame expr) (tl-aldor--lower-expr abn expr frame))
       (run (elems frame locals)
         (unless elems
           (signal 'termlisp-aldor-error
                   '("Sequence without a final value")))
         (let ((elem (car elems))
               (rest (cdr elems)))
           (cond
             ((tl-abn-node-p elem 'Local)
              (let ((inner (nth 1 elem)))
                (cond
                 ;; `local m: T;' -- a bare declaration introduces a
                 ;; real variable covering the rest of the sequence.
                  ((tl-abn-node-p inner 'Declare)
                   (if tl-aldor--goto-region
                       ;; Pre-bound at the region top: a jump may skip
                       ;; this declaration entirely.
                       (run rest frame locals)
                     (let ((name-node (nth 1 inner)))
                       (if (tl-abn-node-p name-node 'Comma)
                         ;; `local a, b: T;' -- every comma name gets a
                         ;; variable covering the rest of the sequence.
                         (let ((names (mapcar #'tl-abn-id-name
                                              (cdr name-node))))
                           (when (memq nil names)
                             (signal 'termlisp-aldor-error
                                     '("Local without a name")))
                           (when rest
                             `(Let ,(mapcar (lambda (n) (list n nil)) names)
                                ,(run rest
                                      (append (mapcar (lambda (n)
                                                        (cons n n))
                                                      names)
                                              frame)
                                      (append names locals)))))
                       (let ((name (tl-abn-id-name name-node)))
                         (unless name
                           (signal 'termlisp-aldor-error
                                   (list (format "Local without a name: %S"
                                                 inner))))
                          (when rest
                            `(Let ((,name nil))
                               ,(run rest (cons (cons name name) frame)
                                     (cons name locals)))))))))
                  ((not (tl-abn-node-p inner 'Assign))
                  (signal 'termlisp-aldor-error
                          (list (format "Malformed local: %S" inner))))
                  (t
                   (let ((assign inner))
                 (let ((decl (nth 1 assign)))
                   (unless (tl-abn-node-p decl 'Declare)
                     (signal 'termlisp-aldor-error
                             (list (format "Local without declaration: %S"
                                           decl))))
                   (let ((name (tl-abn-id-name (nth 1 decl))))
                     (unless name
                       (signal 'termlisp-aldor-error
                               (list (format "Local without a name: %S"
                                             decl))))
                     (let ((rhs-node (nth 2 assign)))
                        (if tl-aldor--goto-region
                            ;; Pre-bound as a variable at the region top:
                            ;; writes must survive jumps.
                            (let ((rhs (tl-aldor--wrap-array-literal
                                        abn decl rhs-node
                                        (if (tl-aldor--type-expr-p rhs-node)
                                            (tl-aldor--type-value)
                                          (lower frame rhs-node)))))
                              (if rest
                                  `(Seq (Setq ,name ,rhs)
                                        ,(run rest frame locals))
                                `(Setq ,name ,rhs)))
                           (run rest
                                (cons (cons name
                                            (tl-aldor--wrap-array-literal
                                             abn decl rhs-node
                                             (if (tl-aldor--type-expr-p rhs-node)
                                                 (tl-aldor--type-value)
                                               (lower frame rhs-node))))
                                      frame)
                                (cons name locals)))))))))))
             ((tl-abn-node-p elem 'Assign)
              (let ((lhs (nth 1 elem)))
                (cond
                  ;; `name: T := v' declares an implicit local.
                  ((tl-abn-node-p lhs 'Declare)
                   (let* ((name (tl-aldor--decl-name lhs))
                          (rhs-node (nth 2 elem))
                          (rhs (tl-aldor--wrap-array-literal
                                abn lhs rhs-node
                                (if (tl-aldor--type-expr-p rhs-node)
                                    (tl-aldor--type-value)
                                  (lower frame rhs-node)))))
                     (if tl-aldor--goto-region
                         ;; Pre-bound as a variable at the region top.
                         (if rest
                             `(Seq (Setq ,name ,rhs)
                                   ,(run rest frame locals))
                           `(Setq ,name ,rhs))
                       (if rest
                           (if (and (tl-aldor--stable-rhs-p rhs-node)
                                    (not (tl-aldor--handle-type-head-p
                                          (tl-aldor--sefo-head-name
                                           abn (nth 2 lhs)))))
                               (run rest
                                    (cons (cons name rhs) frame)
                                    (cons name locals))
                             ;; A handle/mutable value, allocation, or
                             ;; effectful call: bind a real variable so
                             ;; it is evaluated once, in order, and
                             ;; every reference is the same object.
                             `(Let ((,name ,rhs))
                                ,(run rest
                                      (cons (cons name name) frame)
                                      (cons name locals))))
                         rhs))))
                 ((tl-abn-node-p lhs 'Id)
                  (let* ((name (tl-abn-id-name lhs))
                         (rhs (lower frame (nth 2 elem)))
                         (hit (and name (assq name frame))))
                    (cond
                     ((null name)
                      (signal 'termlisp-aldor-error
                              '("Assignment without a name")))
                     ;; A real variable (parameter or loop-promoted
                     ;; local): write it.
                     ((and hit (eq (cdr hit) name))
                      (if rest
                          `(Seq (Setq ,name ,rhs)
                                ,(run rest frame locals))
                        `(Setq ,name ,rhs)))
                     ;; A call whose result must be evaluated once, in
                     ;; order, becomes a real variable.
                     ((and rest (not (tl-aldor--stable-rhs-p (nth 2 elem))))
                      `(Let ((,name ,rhs))
                         ,(run rest (cons (cons name name) frame)
                               (cons name locals))))
                     ;; Substitution local: rebind.  An unknown name
                     ;; becomes an implicit local, as in Aldor.
                     (rest
                      (run rest (cons (cons name rhs) frame)
                           (if hit locals (cons name locals))))
                     ;; A final assignment evaluates to the value.
                     (t rhs))))
                 ;; r.tag := v on a Record/Union rebinds r to a record
                 ;; with the slot replaced, keeping substitution pure;
                 ;; a loop-promoted receiver is updated as a variable.
                 ;; a(i) := v on an array mutates in place, so a
                 ;; substitution-bound receiver is promoted to a
                 ;; variable covering the rest of the sequence.
                  ((tl-abn-node-p lhs 'Apply)
                   (let* ((kids (cdr lhs))
                          (recv (car kids)))
                     (unless (= (length kids) 2)
                       (signal 'termlisp-aldor-error
                               '("Unsupported assignment target")))
                     (let* ((rname (or (and (tl-abn-node-p recv 'Id)
                                            (tl-abn-id-name recv))
                                       (tl-aldor--recv-var-name recv)))
                            (ty (tl-aldor--expr-type-sefo abn recv))
                            (ty-name (and ty
                                          (tl-aldor--sefo-head-name
                                           abn ty)))
                            (hit (and rname (assq rname frame)))
                            (field-p (memq ty-name '(Record Union)))
                            (array-p (memq ty-name
                                           tl-aldor--array-type-names)))
                       (unless (and rname hit (or field-p array-p))
                         (signal 'termlisp-aldor-error
                                 (list (format
                                        "Unsupported assignment target %S (rname %S hit %S type %S)"
                                        recv rname hit ty-name))))
                       (let* ((rhs (lower frame (nth 2 elem)))
                             (identity (eq (cdr hit) rname)))
                        (if field-p
                            (let* ((tag (cadr kids))
                                   (tag-name (and (tl-abn-node-p tag 'Id)
                                                  (tl-abn-id-name tag)))
                                   (idx (and tag-name
                                             (tl-aldor--decl-index
                                              abn
                                              (tl-aldor--sefo-declares ty)
                                              tag-name))))
                              (unless idx
                                (signal 'termlisp-aldor-error
                                        '("Unsupported assignment target")))
                              (let* ((slot (if (eq ty-name 'Union) 1 idx))
                                     (recv-ir (lower frame recv))
                                     (write `(FieldSet ,recv-ir ,slot ,rhs)))
                                (cond
                                 (identity
                                  (if rest
                                      `(Seq (Setq ,rname ,write)
                                            ,(run rest frame locals))
                                    `(Setq ,rname ,write)))
                                 (rest
                                  (run rest
                                       (cons (cons rname write) frame)
                                       locals))
                                 (t write))))
                           ;; Array element: mutate the value in place.
                           ;; A nested receiver (`f(i)(j) := v') lowers
                           ;; the target array expression directly; a
                           ;; plain variable that was substitution-bound
                           ;; is promoted to a real variable.
                           (let* ((plain (tl-abn-node-p recv 'Id))
                                  (arr-ir (if plain
                                              rname
                                            (lower frame recv)))
                                   (write `(ArraySet ,arr-ir
                                                    ,(tl-aldor--array-index-ir
                                                      ty-name
                                                      (lower frame (cadr kids)))
                                                    ,rhs)))
                             (cond
                              ((or identity (not plain))
                               (if rest
                                   `(Seq ,write ,(run rest frame locals))
                                 write))
                              (rest
                               `(Let ((,rname ,(cdr hit))) ,write
                                  ,(run rest
                                        (cons (cons rname rname) frame)
                                        (cons rname locals))))
                              (t `(Let ((,rname ,(cdr hit))) ,write)))))))))
                 ;; Multiple assignment `(a, b) := (e1, e2)': every
                 ;; right-hand side is evaluated against the old
                 ;; bindings, then real variables are written and
                 ;; substitution locals rebound in one step.
                 ((tl-abn-node-p lhs 'Comma)
                  (let* ((targets (cdr lhs))
                         (rhs (nth 2 elem))
                         (rhs-tuple-p (tl-abn-node-p rhs 'Comma)))
                    (unless (and targets
                                 (cl-every (lambda (n)
                                             (tl-abn-node-p n 'Id))
                                           targets)
                                 (or rhs-tuple-p (consp rhs))
                                 (or (not rhs-tuple-p)
                                     (= (length targets)
                                        (length (cdr rhs)))))
                      (signal 'termlisp-aldor-error
                              '("Unsupported assignment target")))
                    (let* ((names (mapcar #'tl-abn-id-name targets))
                           (temps (cl-loop for i from 0
                                           below (length targets)
                                           collect
                                           (intern (format "%%ta%d" i)))))
                      (when (memq nil names)
                        (signal 'termlisp-aldor-error
                                '("Assignment without a name")))
                      (let ((frame1 frame)
                            (locals1 locals)
                            (setqs nil))
                        (cl-loop for name in names
                                 for temp in temps
                                 for hit = (assq name frame)
                                 do (if (and hit (eq (cdr hit) name))
                                        (push (list 'Setq name temp)
                                              setqs)
                                      (setq frame1
                                            (cons (cons name temp)
                                                  frame1))
                                      (unless hit
                                        (setq locals1
                                              (cons name locals1)))))
                        (if rhs-tuple-p
                            ;; Syntactic tuple: every right-hand side is
                            ;; evaluated against the old bindings.
                            (let ((vals (mapcar (lambda (n)
                                                  (lower frame n))
                                                (cdr rhs))))
                              `(Let ,(cl-mapcar #'list temps vals)
                                     ,@(nreverse setqs)
                                     ,(if rest
                                          (run rest frame1 locals1)
                                        (car (last temps)))))
                          ;; The right-hand side evaluates to a tuple
                          ;; vector (a call returning multiple values);
                          ;; evaluate it once, then destructure it.
                          (let ((vec (intern "%%tt")))
                            `(Let ((,vec ,(lower frame rhs)))
                               (Let ,(cl-mapcar
                                      #'list temps
                                      (cl-loop for i from 0
                                               below (length temps)
                                               collect
                                               (list 'ArrayRef vec i)))
                                     ,@(nreverse setqs)
                                     ,(if rest
                                          (run rest frame1 locals1)
                                        (car (last temps)))))))))))
                  (t (signal 'termlisp-aldor-error
                             (list (format
                                    "Unsupported assignment target %S"
                                    lhs)))))))
              ;; A function or constant define nested in a sequence
              ;; binds a name for the rest of the sequence.
              ((tl-abn-node-p elem 'Define)
               (let ((decl (nth 1 elem))
                     (value (nth 2 elem)))
                 (cond
                  ;; `MACRO ==> expr' is compile-time only.
                  ((tl-abn-node-p decl 'Id)
                   (run rest frame locals))
                  ((not (tl-abn-node-p decl 'Declare))
                   (signal 'termlisp-aldor-error
                           (list (format
                                  "Unsupported sequence element |%s|"
                                  (car elem)))))
                  (t
                   (let ((name (tl-aldor--decl-name decl)))
                     (cond
                      ((tl-abn-node-p value 'Lambda)
                       (let ((ir (tl-aldor--lower-lambda abn value frame)))
                         (if rest
                             `(Let ((,name ,ir))
                                ,(run rest
                                      (cons (cons name name) frame)
                                      (cons name locals)))
                           `(Let ((,name ,ir)) nil))))
                      ((tl-aldor--type-expr-p value)
                       (run rest
                            (cons (cons name (tl-aldor--type-value)) frame)
                            locals))
                       (t
                        (let ((rhs (lower frame value)))
                          (if rest
                              `(Let ((,name ,rhs))
                                 ,(run rest (cons (cons name rhs) frame)
                                   (cons name locals)))
                            rhs)))))))))
               ;; Empty elements carry no runtime meaning.
              ((null elem)
              (run rest frame locals))
             ;; `return e' throws to the function catch; anything
             ;; after it is unreachable.
             ((tl-abn-node-p elem 'Return)
              (lower frame elem))
             ;; Nested sequences flatten into this one; an interior
             ;; import or bare declaration binds nothing at runtime.
             ((tl-abn-node-p elem 'Sequence)
              (run (append (cdr elem) rest) frame locals))
              ((memq (car elem) '(Import Inline Declare Export
                                  ForeignImport ForeignExport Default))
               (run rest frame locals))
             ((tl-abn-node-p elem 'Exit)
              (let* ((test-node (nth 1 elem))
                     (condition (if (tl-abn-node-p test-node 'Test)
                                    (nth 1 test-node)
                                  test-node)))
                `(if ,(lower frame condition)
                     ,(if (nth 2 elem)
                          (lower frame (nth 2 elem))
                        nil)
                   ,(if rest
                        (run rest frame locals)
                      nil))))
            ((tl-abn-node-p elem 'Repeat)
             (pcase-let ((`(,frame1 ,locals1 ,binds ,core)
                          (tl-aldor--prepare-repeat abn elem frame
                                                    locals)))
               (cond ((and binds rest)
                      `(Let ,binds ,core ,(run rest frame1 locals1)))
                     (binds `(Let ,binds ,core))
                     (rest `(Seq ,core ,(run rest frame1 locals1)))
                     (t core))))
            ;; Statement-position control flow and effectful calls: the
            ;; lowered form runs for its effects, then the rest.  A
            ;; yield runs for its cons; a generate for its list build.
             ((and rest (memq (car elem)
                              '(If Break Iterate Apply Yield Generate
                                  Where Assert Goto)))
              `(Seq ,(lower frame elem) ,(run rest frame locals)))
            (t
             (when rest
               (signal 'termlisp-aldor-error
                       (list (format "Unsupported sequence element |%s|"
                                     (car elem)))))
             (lower frame elem))))))
       ;; A sequence with gotos becomes a labeled dispatch: statements
       ;; lower into segments, each guarded by a program counter, with
       ;; every name the region writes pre-bound as a variable at the
       ;; top so jumps cannot read a stale substitution.
       (if (and (not tl-aldor--goto-region)
                (tl-aldor--contains node 'Goto))
           (let* ((pre (tl-aldor--goto-prebind-names node))
                  (frame1 (append (mapcar (lambda (n) (cons n n)) pre)
                                  env))
                  (locals1 (append pre locals))
                  (segs (tl-aldor--split-labels (cdr node)))
                  (tl-aldor--goto-region t)
                  (branches nil)
                  (nsegs (length segs))
                  (i 0))
             (dolist (seg segs)
               (let* ((bound (car seg))
                      (elems (cdr seg))
                      (lastp (= i (1- nsegs)))
                      (body (cond ((null elems) nil)
                                  (t (run elems frame1 locals1))))
                      (next (unless lastp (car (nth (1+ i) segs))))
                      (advance (if lastp
                                   `(Throw tl-seq-done nil)
                                 `(Setq %pc (quote ,next)))))
                 (push `(if (eq %pc (quote ,bound))
                            (Seq (Setq %seqv ,body)
                                 ,advance))
                       branches)
                 (setq i (1+ i))))
             (let ((chain '(error "invalid goto target")))
               (dolist (b branches)
                 (setq chain (append b (list chain))))
               `(Let ((%pc (quote start))
                      (%seqv nil)
                      ,@(mapcar (lambda (n) (list n nil)) pre))
                  (Catch tl-seq-done
                    (While True
                      (Catch tl-seq-next
                        ,chain)))
                  %seqv)))
         (run (cdr node) env locals))))

(provide 'termlisp-aldor)
;;; termlisp-aldor.el ends here
