;;; termlisp-types.el --- HM type inference -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Hindley-Milner inference over the *term graph* (`termlisp-graph').
;; A type is a graph node: a constructor application `(C a b)' is a
;; compound node, a bare constructor `Int' is a leaf, and a type variable
;; is a variable node (see `termlisp-graph-unify').  `tl-tcon' and its
;; accessors are the surface interface over nodes.  Unification is in
;; place (union-find), so the `bindings' threaded through the API are
;; vestigial.  Generalization quantifies free variable nodes; instantiation
;; copies the graph with fresh variables.  As in Coalton the occurs check
;; is off by default, so recursive (equirecursive) types are representable;
;; the graph traversals (`tl-map-type', `tl-canonical-key', unification)
;; are cycle-safe accordingly.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-graph-unify)
(require 'termlisp-reader)

(declare-function tl-eval-datatype "termlisp-eval" (env form))
(declare-function tl-eval-datatype-extension "termlisp-eval" (env form))
(declare-function tl-desugar-do "termlisp-eval" (form))

;;; Representation: a type is a `tl-node' from `termlisp-graph'.
;;; A constructor application `(C a b)' is a compound node, a bare
;;; constructor `Int' is a leaf node, and a type variable is a variable
;;; node.  Unification is *in place* (union-find), so the `bindings'
;;; threaded through the API below are vestigial -- kept only so the
;;; inference code's shape is unchanged.  Following Coalton the occurs
;;; check is off by default (equirecursive types).

(cl-defstruct (tl-tscheme (:constructor tl-tscheme (vars type &optional constraints)))
  vars type (constraints nil))
(cl-defstruct (tl-constraint (:constructor tl-constraint (class type))) class type)
(cl-defstruct (tl-cclass (:constructor tl-cclass (name params supers methods))) name params supers methods)
(cl-defstruct (tl-instance (:constructor tl-instance (class head context methods &optional dict)))
  class head context methods dict)

(defun tl-type-deref (x)
  "Follow X to its representative when it is a type node."
  (if (tl-node-p x) (tl-gnode-deref x) x))

(defun tl-tcon (name args)
  "Build a type: a compound node when ARGS is non-empty, else a leaf."
  (if args (tl-make-node name args t) (tl-make-node name)))

(defun tl-tcon-p (x)
  "Non-nil when X is a (deref'd) non-variable type node."
  (let ((d (tl-type-deref x)))
    (and (tl-node-p d) (not (tl-node-var d)))))

(defun tl-tcon-name (x)
  (tl-node-head (tl-type-deref x)))

(defun tl-tcon-args (x)
  (tl-node-children (tl-type-deref x)))

(defun tl-tvar-p (x)
  "Non-nil when X is a (deref'd) type-variable node."
  (let ((d (tl-type-deref x)))
    (and (tl-node-p d) (tl-node-var d))))

(defun tl-type-p (x) (tl-node-p x))

(defun tl-fresh-tvar (&optional _level)
  "Return a fresh type variable node."
  (tl-make-var-node (gensym "t")))

(defun tl-tarrow (a b) (tl-tcon '-> (list a b)))
(defun tl-tint () (tl-tcon 'Int nil))
(defun tl-tstring () (tl-tcon 'String nil))
(defun tl-tbool () (tl-tcon 'Bool nil))

(defun tl-tfun-args (ty)
  "If TY is `(-> a b)', return (a b), else nil."
  (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
    (tl-tcon-args ty)))

(defun tl-unify-types (a b bindings)
  "Unify types A and B in place under BINDINGS.  Return `(ok . bindings)'.
On failure returns `(nil . nil)'; failed attempts are rolled back."
  (if (tl-gnode-unify a b)
      (cons t bindings)
    (cons nil nil)))

(defun tl-apply-bindings (type bindings)
  "Fully zonk TYPE, dereferencing every variable.  BINDINGS is ignored
because unification is in place."
  (ignore bindings)
  (tl-map-type #'identity type))

(defun tl-compose-bindings (bindings _new)
  "Bindings are vestigial under in-place unification; return BINDINGS."
  bindings)

(defvar tl-type-parse-vars nil
  "Alist of type-variable symbols to type variables, bound during parsing.")

(defun tl-type-var-symbol-p (sym)
  "Return non-nil if SYM is a type variable (lowercase-initial)."
  (and (symbolp sym)
       (not (memq sym '(nil t)))
       (> (length (symbol-name sym)) 0)
       (let ((case-fold-search nil))
         (string-match-p "\\`[a-z]" (symbol-name sym)))))

(defun tl-split-arrow (sexp)
  "Split SEXP on `->' into its component type expressions."
  (let ((parts nil) (cur nil))
    (dolist (x sexp)
      (if (eq x '->)
          (progn
            (unless (consp cur)
              (signal 'termlisp-type-error
                      (list (format "Malformed arrow type: %S" sexp))))
            (push (nreverse cur) parts)
            (setq cur nil))
        (push x cur)))
    (unless (consp cur)
      (signal 'termlisp-type-error
              (list (format "Malformed arrow type: %S" sexp))))
    (push (nreverse cur) parts)
    (nreverse parts)))

(defun tl-type-head (sym)
  "Resolve head symbol SYM through `tl-type-parse-vars' if it is bound.
Bound class/datatype parameters become their shared type variable, so
an application such as `(f a)' stores the variable in the `tl-tcon'
name slot."
  (let ((cell (and (symbolp sym) (assq sym tl-type-parse-vars))))
    (if cell (cdr cell) sym)))

(defun tl-type-parse-segment (segment)
  "Parse SEGMENT, one arrow operand's token list, into a type.
A single-token SEGMENT is that token; otherwise it is a constructor
application."
  (if (cdr segment)
      (tl-tcon (tl-type-head (car segment))
               (mapcar #'tl-type-parse* (cdr segment)))
    (tl-type-parse* (car segment))))

(defun tl-type-parse-arrow (parts)
  "Parse PARTS as a right-associative arrow chain."
  (if (null (cdr parts))
      (tl-type-parse-segment (car parts))
    (tl-tarrow (tl-type-parse-segment (car parts))
               (tl-type-parse-arrow (cdr parts)))))

(defun tl-type-parse* (sexp)
  "Parse SEXP, sharing type variables via `tl-type-parse-vars'."
  (cond
   ((tl-type-var-symbol-p sexp)
    (let ((cell (assq sexp tl-type-parse-vars)))
      (if cell (cdr cell)
        (let ((tv (tl-fresh-tvar)))
          (push (cons sexp tv) tl-type-parse-vars)
          tv))))
   ((symbolp sexp) (tl-tcon sexp nil))
   ((and (consp sexp) (eq (car sexp) '->))
    (if (cdr (cdr sexp))
        (tl-type-parse-arrow (mapcar #'list (cdr sexp)))
      (signal 'termlisp-type-error
              (list (format "Malformed arrow type: %S" sexp)))))
   ((and (consp sexp) (memq '-> sexp))
    (tl-type-parse-arrow (tl-split-arrow sexp)))
   ((consp sexp)
    (tl-tcon (tl-type-head (car sexp)) (mapcar #'tl-type-parse* (cdr sexp))))
   (t (signal 'termlisp-type-error (list (format "Bad type: %S" sexp))))))

(defun tl-type-parse (sexp)
  "Parse surface type expression SEXP into a type."
  (let ((tl-type-parse-vars nil))
    (tl-type-parse* sexp)))

(defun tl-type-fold (leaf-fn node-fn type)
  "Fold over the `tl-decompose' structure of TYPE.
For a leaf (a node with no decomposition) return `(funcall LEAF-FN TYPE)'.
Otherwise, with decomposition D, fold the head `(car D)' first, then the
children `(cdr D)' left to right, and return
`(funcall NODE-FN (car D) HEAD-RESULT CHILDREN-RESULTS)'."
  (let ((d (tl-decompose type)))
    (if (null d)
        (funcall leaf-fn type)
      (let* ((head (tl-type-fold leaf-fn node-fn (car d)))
             (children (mapcar (lambda (child)
                                 (tl-type-fold leaf-fn node-fn child))
                               (cdr d))))
        (funcall node-fn (car d) head children)))))

(defun tl-free-tvars (type)
  "Return the list of unbound type variables occurring in TYPE."
  (tl-gtype-free-vars type))

(defun tl-canonical-key (type)
  "Return a variable-rename-invariant string key for TYPE.
Type variables are numbered in order of first appearance, so
alpha-equivalent types (e.g. `(a -> a)' and `(b -> b)') share a key.
Equirecursive cycles are rendered as back-references `#N'.
The key is an over-approximation: callers that need exact equality
confirm within the bucket (see `tl-remove-duplicates-by-key')."
  (let ((index nil) (counter 0) (seen (make-hash-table :test #'eq)) (n 0))
    (cl-labels ((go (node)
                  (let ((node (tl-type-deref node)))
                    (cond
                     ((tl-tvar-p node)
                      (let ((cell (assq node index)))
                        (if cell (cdr cell)
                          (let ((key (format "?%d" counter)))
                            (setq counter (1+ counter))
                            (push (cons node key) index)
                            key))))
                     ((tl-tcon-p node)
                      (let ((args (tl-tcon-args node)))
                        (if (null args)
                            (format "%S" (tl-tcon-name node))
                          (let ((hit (gethash node seen)))
                            (if hit
                                (format "#%d" hit)
                              (puthash node n seen)
                              (setq n (1+ n))
                              (format "(%s%s)"
                                      (tl-tcon-name node)
                                      (mapconcat (lambda (c) (concat " " (go c)))
                                                 args "")))))))
                     (t (format "%S" node))))))
      (go type))))

(defun tl-constraint-canonical-key (c)
  "Return a variable-rename-invariant string key for constraint C."
  (format "%S:%s" (tl-constraint-class c)
          (tl-canonical-key (tl-constraint-type c))))

(defun tl-remove-duplicates-by-key (items key-fn eq-fn)
  "Remove duplicates from ITEMS, keeping the last of each equivalence.
Behaves like `cl-remove-duplicates' with `:test EQ-FN', but buckets by
KEY-FN first.  KEY-FN must be an over-approximation (EQ-FN true implies
equal keys); the result is identical to the unbucketed dedup.  Borrowed
from clover's `remove-duplicates-by-key'."
  (let* ((keyed (cl-loop for x in items
                         collect (cons (funcall key-fn x) x)))
         (buckets (make-hash-table :test #'equal)))
    (cl-loop for kc in keyed for i from 0
             do (push (cons i (cdr kc)) (gethash (car kc) buckets)))
    (cl-loop for kc in keyed for i from 0
             unless (cl-some (lambda (p)
                               (and (> (car p) i)
                                    (funcall eq-fn (cdr kc) (cdr p))))
                             (gethash (car kc) buckets))
             collect (cdr kc))))

(defun tl-type-parse-scheme (sexp)
  "Parse SEXP into a type scheme, quantifying its free variables."
  (let ((ty (tl-type-parse sexp)))
    (tl-tscheme (tl-free-tvars ty) ty)))

(defun tl-map-type (f type)
  "Apply F to each type variable in TYPE, rebuilding the node graph.
F is applied to a variable node wherever it occurs; its result is
inserted without further traversal.  Cycle-safe (equirecursive types)."
  (let ((memo (make-hash-table :test #'eq)))
    (cl-labels ((go (node)
                  (let ((node (tl-type-deref node)))
                    (cond
                     ((tl-tvar-p node) (funcall f node))
                     ((tl-tcon-p node)
                      (let ((args (tl-tcon-args node)))
                        (if (null args)
                            node
                          (or (gethash node memo)
                              (let ((new (tl-make-node (tl-tcon-name node)
                                                       nil t)))
                                (puthash node new memo)
                                (setf (tl-node-children new)
                                      (mapcar #'go args))
                                new)))))
                     (t node)))))
      (go type))))

(defun tl-type-subst (type sub)
  "Apply substitution SUB (alist var-node -> type) to TYPE."
  (tl-map-type
   (lambda (tv) (let ((cell (assq tv sub))) (if cell (cdr cell) tv)))
   type))

(defun tl-generalized-vars (type env-tvars)
  "Return the type variables of TYPE that are not in ENV-TVARS."
  (cl-remove-if (lambda (v) (memq v env-tvars)) (tl-free-tvars type)))

(defun tl-constraint-eq (a b)
  "Structural equality of two predicates (after zonking)."
  (and (eq (tl-constraint-class a) (tl-constraint-class b))
       (equal (tl-apply-bindings (tl-constraint-type a) nil)
              (tl-apply-bindings (tl-constraint-type b) nil))))

(defun tl-gnode-match (pattern node)
  "One-way, non-destructive match of PATTERN against NODE.
Pattern variable nodes are rigid; the result `(t . SUB)' maps each to
the node it matched, or nil on failure.  The graph is never mutated."
  (let ((p (tl-type-deref pattern))
        (n (tl-type-deref node)))
    (cond
     ((tl-tvar-p p) (cons t (list (cons p n))))
     ((and (tl-tcon-p p) (tl-tcon-p n)
           (eq (tl-tcon-name p) (tl-tcon-name n))
           (= (length (tl-tcon-args p)) (length (tl-tcon-args n))))
      (let ((ps (tl-tcon-args p)) (ns (tl-tcon-args n)) (sub nil) (ok t))
        (while (and ps ok)
          (let ((r (tl-gnode-match (car ps) (car ns))))
            (if r (setq sub (append sub (cdr r))) (setq ok nil)))
          (setq ps (cdr ps) ns (cdr ns)))
        (and ok (cons t sub))))
     ((equal p n) (cons t nil))
     (t nil))))

(defun tl-match-instance (head ty)
  "Match instance HEAD against type TY, one-way.  Return `(t . SUB)' or nil."
  (tl-gnode-match head ty))

(defun tl-entail-by-inst (env pred)
  "Non-nil when PRED is satisfied by an instance whose context is entailed."
  (let ((insts (gethash (tl-constraint-class pred) (tl-env-instance-env env))))
    (catch 'ok
      (dolist (inst insts)
        (let ((m (tl-match-instance (tl-instance-head inst)
                                    (tl-constraint-type pred))))
          (when (car m)
            (let ((sub (cdr m)))
              (when (cl-every
                     (lambda (c2)
                       (tl-entail-by-inst
                        env
                        (tl-constraint (tl-constraint-class c2)
                                       (tl-type-subst
                                        (tl-constraint-type c2) sub))))
                     (tl-instance-context inst))
                (throw 'ok t))))))
      nil)))

(defun tl-entail-by-super (env preds pred)
  "Non-nil when a predicate in PREDS entails PRED by a superclass.
If PREDS holds `(C t)' and C has superclass D, then `(D t)' is entailed."
  (cl-some
   (lambda (p)
     (let ((c (gethash (tl-constraint-class p) (tl-env-class-env env))))
       (and c
            (cl-some (lambda (sc)
                       (and (eq (tl-constraint-class sc) (tl-constraint-class pred))
                            (tl-constraint-eq
                             (tl-constraint (tl-constraint-class pred)
                                            (tl-constraint-type p))
                             pred)))
                     (tl-cclass-supers c)))))
   preds))

(defun tl-entail (env preds pred)
  "Non-nil when PREDS entail PRED by membership, superclass, or instance."
  (or (cl-some (lambda (p) (tl-constraint-eq p pred)) preds)
      (tl-entail-by-super env preds pred)
      (tl-entail-by-inst env pred)))

(defun tl-solve-constraint (env c bindings)
  "Resolve constraint C in ENV.  Return `(ok . bindings)'.
Resolution is graph-native: an instance matches when its head matches
C's type (non-destructively) and its context is recursively entailed."
  (cons (if (tl-entail-by-inst env c) t nil) bindings))

(defconst tl-default-class-defaults
  '((Num . Int) (Integral . Int) (Fractional . DoubleFloat)
    (Eq . Int) (Ord . Int))
  "Default type constructor for the parameter of a class when it is
ambiguous (mirrors Coalton/Haskell numeric defaulting).")

(defun tl-split-context (_env gen-vars preds)
  "Split PREDS into (RETAINED DEFERRED).
A predicate is RETAINED when its type mentions a GEN-VARS variable (so
it is generalized with the scheme); otherwise it is DEFERRED and must be
solved or defaulted at the use site."
  (let (retained deferred)
    (dolist (c preds)
      (if (cl-intersection gen-vars (tl-free-tvars (tl-constraint-type c)))
          (push c retained)
        (push c deferred)))
    (list (nreverse retained) (nreverse deferred))))

(defun tl-ambiguities (_env env-vars preds)
  "Return the predicates of PREDS whose variables are not determined.
A variable is determined when it is in ENV-VARS or is the variable of a
predicate whose own variables are already determined (so fundep-style
determination is captured; plain HM has none and this reduces to
\"unchanged variables\")."
  (let ((det (copy-sequence env-vars)) (changed t))
    (while changed
      (setq changed nil)
      (dolist (c preds)
        (let ((vs (tl-free-tvars (tl-constraint-type c))))
          (when (cl-every (lambda (v) (memq v det)) vs)
            (dolist (v vs)
              (unless (memq v det) (push v det) (setq changed t)))))))
    (cl-remove-if
     (lambda (c)
       (cl-every (lambda (v) (memq v det))
                 (tl-free-tvars (tl-constraint-type c))))
     preds)))

(defun tl-default-subs (_env preds)
  "Return an alist var-node -> default type for the ambiguous PREDS.
Uses `tl-default-class-defaults'; a predicate whose class has no default
contributes nothing."
  (let (subs)
    (dolist (c preds)
      (let ((def (cdr (assq (tl-constraint-class c) tl-default-class-defaults))))
        (when def
          (dolist (v (tl-free-tvars (tl-constraint-type c)))
            (unless (assq v subs)
              (push (cons v (tl-tcon def nil)) subs))))))
    subs))

(defun tl-close-constraints (env gen-vars constraints bindings &optional reject-ambiguous)
  "Zonk CONSTRAINTS, retain the generalizable ones, solve or default the rest.
GEN-VARS are the type variables being generalized; a constraint whose
type mentions one is retained.  The deferred constraints are defaulted
\(see `tl-default-subs') and solved; an unsolved ground constraint -- or,
with REJECT-AMBIGUOUS, one still mentioning free type variables -- is
rejected with `termlisp-type-error'."
  (let* ((zonked (mapcar
                  (lambda (c)
                    (tl-constraint (tl-constraint-class c)
                                   (tl-apply-bindings (tl-constraint-type c) bindings)))
                  constraints))
         (split (tl-split-context env gen-vars zonked))
         (retained (car split))
         (deferred (cadr split))
         (defaults (tl-default-subs env deferred))
         (deferred (mapcar (lambda (c)
                             (tl-constraint (tl-constraint-class c)
                                            (tl-type-subst (tl-constraint-type c)
                                                           defaults)))
                           deferred)))
    (dolist (c deferred)
      (unless (tl-entail env retained c)
        (let ((free (tl-free-tvars (tl-constraint-type c))))
          (when (or reject-ambiguous (null free))
            (signal 'termlisp-type-error
                    (list (if free
                              (format "Ambiguous constraint: no instance for %S %S"
                                      (tl-constraint-class c) (tl-constraint-type c))
                            (format "No instance for %S %S"
                                    (tl-constraint-class c) (tl-constraint-type c)))))))))
    (tl-remove-duplicates-by-key (nreverse retained)
                                 #'tl-constraint-canonical-key #'tl-constraint-eq)))

(defun tl-generalize (type env-tvars &optional constraints)
  "Generalize TYPE, quantifying tvars not in ENV-TVARS, keeping CONSTRAINTS
whose type mentions a quantified variable."
  (let* ((vars (tl-generalized-vars type env-tvars))
         (kept (cl-remove-if-not
                (lambda (c)
                  (cl-intersection vars (tl-free-tvars (tl-constraint-type c))))
                constraints)))
    (tl-tscheme vars (tl-map-type #'identity type)
                (tl-remove-duplicates-by-key kept
                                             #'tl-constraint-canonical-key #'equal))))

(defun tl-env-free-tvars (env)
  "Free type variables of the type environment of ENV."
  (let ((acc nil))
    (maphash (lambda (_name sc)
               (let ((vars (tl-tscheme-vars sc)))
                 (dolist (v (tl-free-tvars (tl-tscheme-type sc)))
                   (unless (memq v vars)
                     (cl-pushnew v acc :test #'eq)))))
             (tl-env-type-env env))
    acc))

(defvar tl-infer-constraints nil
  "Dynamically bound list of constraints collected during inference.
Each element is a `tl-constraint'.  Entry points rebind this to nil so
that constraints do not leak between top-level forms.")

(defvar tl-elab-active nil
  "Non-nil while inference should record class-method call sites.
Bound by the elaborator (see `termlisp-elaborate.el').")

(defvar tl-elab-sites nil
  "Class-method call sites recorded during inference.
Each element is `(FORM . CONSTRAINT)', where FORM is the application
cons cell and CONSTRAINT is the `tl-constraint' emitted for the method.
Only populated while `tl-elab-active' is non-nil.")

(defvar tl-elab-bindings nil
  "Final substitution of the most recent inference, for elaboration.
Set by the define/constant entry points so the elaborator can zonk the
recorded method-call constraints.")

(defun tl-emit-constraint (c)
  "Record constraint C in the current `tl-infer-constraints'."
  (push c tl-infer-constraints))

(defun tl-instantiate-scheme (scheme)
  "Instantiate SCHEME with fresh type variables.
Return `(TYPE . CONSTRAINTS)', freshening the type and any constraints
with the same substitution.  A non-scheme is returned as
`(SCHEME . nil)'."
  (if (tl-tscheme-p scheme)
      (let ((sub (mapcar (lambda (v) (cons v (tl-fresh-tvar)))
                         (tl-tscheme-vars scheme))))
        (cons (tl-type-subst (tl-tscheme-type scheme) sub)
              (mapcar (lambda (c)
                        (tl-constraint (tl-constraint-class c)
                                       (tl-type-subst (tl-constraint-type c) sub)))
                      (tl-tscheme-constraints scheme))))
    (cons scheme nil)))

(defun tl-instantiate (scheme)
  "Instantiate SCHEME, returning only the instantiated type."
  (car (tl-instantiate-scheme scheme)))

(defun tl-instantiate-constraints (scheme)
  "Return SCHEME's constraints instantiated with fresh type variables.
Callers that also need the instantiated type must use
`tl-instantiate-scheme' so both share one substitution."
  (cdr (tl-instantiate-scheme scheme)))

(defun tl-skolemize-scheme (scheme)
  "Replace SCHEME's quantified variables with rigid type constants."
  (tl-type-subst (tl-tscheme-type scheme)
                 (mapcar (lambda (v) (cons v (tl-tcon (gensym "sk") nil)))
                         (tl-tscheme-vars scheme))))

(defvar tl-builtin-types (make-hash-table :test #'eq)
  "Type schemes for builtin functions.")

(defun tl-register-builtin-type (name scheme)
  "Register type SCHEME for builtin NAME."
  (puthash name scheme tl-builtin-types))

(let ((a (tl-fresh-tvar)))
  (tl-register-builtin-type
   'eq (tl-tscheme (list a) (tl-tarrow a (tl-tarrow a (tl-tbool))))))
(tl-register-builtin-type
 '+
 (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tint)))))
(tl-register-builtin-type
 '-
 (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tint)))))
(tl-register-builtin-type
 '*
 (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tint)))))
(tl-register-builtin-type
 '<
 (tl-tscheme nil (tl-tarrow (tl-tint) (tl-tarrow (tl-tint) (tl-tbool)))))

(cl-defun tl-register-datatype-types (env name ctors
                                          &optional (param-syms nil param-syms-p))
  "Register constructor type schemes for datatype NAME with CTORS.
PARAM-SYMS, if non-nil, are the datatype's declared type parameters
\(reused for extensions).  Returns the datatype's parameter symbols.
When PARAM-SYMS is explicitly supplied (even nil), CTORS are an
extension and any type parameter not declared by the datatype is an
error."
  (let* ((tl-type-parse-vars
          (mapcar (lambda (s) (cons s (tl-fresh-tvar))) param-syms))
         (ctor-args (mapcar (lambda (ctor)
                              (cons (car ctor) (mapcar #'tl-type-parse* (cdr ctor))))
                            ctors))
         (syms (or param-syms (mapcar #'car (reverse tl-type-parse-vars)))))
    (when param-syms-p
      (dolist (cell tl-type-parse-vars)
        (unless (memq (car cell) param-syms)
          (signal 'termlisp-type-error
                  (list (format "Undeclared type parameter %S in extension of %S"
                                (car cell) name))))))
    (let ((params (mapcar (lambda (s) (cdr (assq s tl-type-parse-vars))) syms))
          (result (tl-tcon name (mapcar (lambda (s) (cdr (assq s tl-type-parse-vars))) syms))))
      ;; A datatype's kind is its number of type parameters.
      (puthash name (length syms) (tl-env-kind-env env))
      (dolist (ca ctor-args)
        (let ((ty result))
          (dolist (argty (reverse (cdr ca)))
            (setq ty (tl-tarrow argty ty)))
          (puthash (car ca) (tl-tscheme params ty)
                   (tl-env-type-env env))))
      syms)))

(defun tl-tenv-locals (env) (if (consp env) (car env) nil))

(defun tl-tenv-base (env)
  "Return the underlying `tl-env' of ENV (nil if none)."
  (cond ((null env) nil)
        ((tl-env-p env) env)
        ((consp env) (tl-tenv-base (cdr env)))
        (t env)))

(defun tl-tenv-extend (env bindings)
  "Return ENV with BINDINGS prepended to its local bindings."
  (cons (append bindings (tl-tenv-locals env)) (tl-tenv-base env)))

(defun tl-zonk-env (env bindings)
  "Apply BINDINGS to the local types in ENV."
  (cons (mapcar (lambda (cell)
                  (cons (car cell) (tl-apply-bindings (cdr cell) bindings)))
                (tl-tenv-locals env))
        (tl-tenv-base env)))

(defvar tl-infer-ir-heads (make-hash-table :test #'eq)
  "Special forms of the lowering IR, mapped to their inference functions.
Each handler is called as (HANDLER ENV EXPR) and returns (TYPE . BINDINGS).
Populated by `termlisp-ir-types' so the generic inferencer can type the
statement and data forms the Aldor lowering emits.")

(defun tl-infer (env expr)
  "Infer the type of EXPR in ENV.  Return `(type . bindings)'."
  (cond
   ((numberp expr) (cons (tl-tint) nil))
   ((stringp expr) (cons (tl-tstring) nil))
   ((symbolp expr) (tl-infer-symbol env expr))
   ((and (consp expr) (eq (car expr) 'lambda))
    (tl-infer-lambda env (cadr expr) (caddr expr)))
   ((and (consp expr) (eq (car expr) 'do))
    (tl-infer env (tl-desugar-do expr)))
   ((and (consp expr) (gethash (car-safe expr) tl-infer-ir-heads))
    (funcall (gethash (car-safe expr) tl-infer-ir-heads) env expr))
   ((consp expr) (tl-infer-application env expr))
   (t (signal 'termlisp-type-error (list (format "Cannot infer: %S" expr))))))

(defun tl-infer-symbol (env sym)
  "Infer the type of a bare symbol SYM."
  (let ((cell (assq sym (tl-tenv-locals env)))
        (base (tl-tenv-base env)))
    (cond
     (cell (cons (cdr cell) nil))
     ((and base (gethash sym (tl-env-type-env base)))
      (let ((r (tl-instantiate-scheme (gethash sym (tl-env-type-env base)))))
        (dolist (c (cdr r)) (tl-emit-constraint c))
        (cons (car r) nil)))
     ((and base (gethash sym (tl-env-method-env base)))
      (let ((r (tl-instantiate-scheme (gethash sym (tl-env-method-env base)))))
        (dolist (c (cdr r)) (tl-emit-constraint c))
        (cons (car r) nil)))
     ((gethash sym tl-builtin-types)
      (cons (tl-instantiate (gethash sym tl-builtin-types)) nil))
     (t (cons (tl-fresh-tvar) nil)))))

(defun tl-infer-lambda (env params body)
  "Infer `(lambda PARAMS BODY)'."
  (let ((ptypes nil)
        (pbinds nil))
    (dolist (p params)
      (let ((tv (tl-fresh-tvar)))
        (push (cons p tv) pbinds)
        (push tv ptypes)))
    (setq ptypes (nreverse ptypes))
    (let* ((env2 (tl-tenv-extend env (nreverse pbinds)))
           (r (tl-infer env2 body))
           (ty (car r)))
      (dolist (pt (reverse ptypes))
        (setq ty (tl-tarrow pt ty)))
      (cons ty (cdr r)))))

(defun tl-method-scheme-for (env sym)
  "Return the class-method scheme for SYM in ENV, or nil if not a method.
A local binding or an ordinary type binding shadows the method."
  (let ((base (tl-tenv-base env)))
    (and base
         (not (assq sym (tl-tenv-locals env)))
         (gethash sym (tl-env-method-env base)))))

(defun tl-infer-application (env expr)
  "Infer a function application EXPR = (F A1 ... AN)."
  (let* ((head (car expr))
         (args (cdr expr))
         (msc (and (symbolp head) (tl-method-scheme-for env head)))
         (rh (if msc
                 (let ((r (tl-instantiate-scheme msc)))
                   (dolist (c (cdr r))
                     (tl-emit-constraint c)
                     (when tl-elab-active (push (cons expr c) tl-elab-sites)))
                   (cons (car r) nil))
               (tl-infer env head)))
         (ftype (car rh))
         (bindings (cdr rh)))
    (dolist (arg args)
      (let* ((ra (tl-infer (tl-zonk-env env bindings) arg))
             (aty (car ra))
             (res (tl-fresh-tvar)))
        (setq bindings (tl-compose-bindings bindings (cdr ra)))
        (setq ftype (tl-apply-bindings ftype bindings))
        (setq aty (tl-apply-bindings aty bindings))
        (let ((u (tl-unify-types ftype (tl-tarrow aty res) bindings)))
          (cond ((car u)
                 (setq bindings (cdr u))
                 (setq ftype (tl-apply-bindings res bindings)))
                (tl-type-lenient
                 (setq ftype res))
                (t
                 (signal 'termlisp-type-error
                         (list (format "Cannot apply %S to %S" head arg))))))))
    (cons (tl-apply-bindings ftype bindings) bindings)))

(defun tl-infer-arg-types-of-constructor (cty n)
  "Return the first N argument types of constructor type CTY."
  (let ((acc nil))
    (dotimes (_ n)
      (let ((args (tl-tfun-args cty)))
        (unless args
          (signal 'termlisp-type-error
                  '("Too many arguments in constructor pattern")))
        (push (nth 0 args) acc)
        (setq cty (nth 1 args))))
    (nreverse acc)))

(defun tl-infer-result-of-constructor (cty n)
  "Return the result type of constructor type CTY applied to N args."
  (dotimes (_ n)
    (let ((args (tl-tfun-args cty)))
      (unless args
        (signal 'termlisp-type-error
                '("Too many arguments in constructor pattern")))
      (setq cty (nth 1 args))))
  cty)

(defun tl-constructor-name-p (env name)
  "Return non-nil if NAME is a registered constructor."
  (let ((base (tl-tenv-base env)))
    (and base (gethash name (tl-env-constructors base)))))

(defun tl-infer-pattern (env pat expected)
  "Infer bindings of PAT at type EXPECTED.
Return `(LOCAL-BINDINGS . SUBST)'."
  (cond
   ((eq pat '_) (cons nil nil))
   ((symbolp pat)
    (if (tl-constructor-name-p env pat)
        (let ((sc (gethash pat (tl-env-type-env (tl-tenv-base env)))))
          (let ((u (tl-unify-types (tl-instantiate sc) expected nil)))
            (unless (car u)
              (signal 'termlisp-type-error
                      (list (format "Constructor %S mismatches expected type" pat))))
            (cons nil (cdr u))))
      (cons (list (cons pat expected)) nil)))
   ((and (consp pat) (eq (car pat) :literal))
    (let* ((r (tl-infer env (cadr pat)))
           (bs (cdr r))
           (u (tl-unify-types (tl-apply-bindings (car r) bs) expected bs)))
      (unless (car u)
        (signal 'termlisp-type-error (list (format "Literal pattern %S mismatches" pat))))
      (cons nil (cdr u))))
   ((and (consp pat) (eq (car pat) :list))
    ;; List types are deferred; the bound variable is left unconstrained.
    (cons (list (cons (cadr pat) (tl-fresh-tvar))) nil))
   ((and (consp pat) (eq (car pat) :lambda))
    (cons (list (cons (cadr pat) expected)) nil))
   ((and (consp pat) (eq (car pat) 'guard))
    (let* ((sub (tl-infer-pattern env (cadr pat) expected))
           (env2 (tl-tenv-extend env (car sub)))
           (g (tl-infer env2 (caddr pat)))
           (bs (tl-compose-bindings (cdr sub) (cdr g)))
           (u (tl-unify-types (tl-apply-bindings (car g) bs) (tl-tbool) bs)))
      (unless (car u)
        (signal 'termlisp-type-error (list "Guard expression is not Bool")))
      (cons (car sub) (cdr u))))
   ((and (consp pat) (eq (car pat) 'or))
    (let ((first-binds nil) (first t) (bs nil))
      (dolist (p (cdr pat))
        (let* ((env-z (tl-zonk-env env bs))
               (r (tl-infer-pattern env-z p expected))
               (rbs (tl-compose-bindings bs (cdr r)))
               (binds (mapcar (lambda (cell)
                                (cons (car cell) (tl-apply-bindings (cdr cell) rbs)))
                              (car r))))
          (if first
              (setq first nil first-binds binds bs rbs)
            (dolist (cell binds)
              (let ((other (assq (car cell) first-binds)))
                (unless other
                  (signal 'termlisp-type-error
                          (list "or-pattern alternatives bind different variables")))
                (let ((u (tl-unify-types (cdr other) (cdr cell) rbs)))
                  (unless (car u)
                    (signal 'termlisp-type-error
                            (list "or-pattern alternatives bind incompatible types")))
                  (setq rbs (cdr u)))))
            (setq bs rbs))))
      (cons first-binds bs)))

   ((and (consp pat) (eq (car pat) 'and))
    (let ((binds nil) (bs nil))
      (dolist (p (cdr pat))
        (let* ((env-z (tl-tenv-extend (tl-zonk-env env bs) binds))
               (r (tl-infer-pattern env-z p expected)))
          (setq binds (append (car r) binds)
                bs (tl-compose-bindings bs (cdr r)))))
      (cons binds bs)))
   ((consp pat)
    (let* ((ctor (car pat))
           (subs (cdr pat))
           (base (tl-tenv-base env))
           (sc (and base (gethash ctor (tl-env-type-env base)))))
      (unless sc
        (signal 'termlisp-type-error
                (list (format "Unknown constructor in pattern: %S" ctor))))
      (let* ((cty (tl-instantiate sc))
             (result-type (tl-infer-result-of-constructor cty (length subs)))
             (u (tl-unify-types result-type expected nil)))
        (unless (car u)
          (signal 'termlisp-type-error
                  (list (format "Constructor %S mismatches expected type" ctor))))
        (let ((arg-types (tl-infer-arg-types-of-constructor cty (length subs)))
              (bs (cdr u))
              (binds nil))
          (while subs
            (let ((r (tl-infer-pattern env (car subs) (car arg-types))))
              (setq binds (append (car r) binds)
                    bs (tl-compose-bindings bs (cdr r))))
            (setq subs (cdr subs) arg-types (cdr arg-types)))
          (cons binds bs)))))
   (t (signal 'termlisp-type-error (list (format "Bad pattern: %S" pat))))))

(defvar tl-type-lenient-clauses nil
  "When non-nil, clauses of a definition that do not share one type are
treated as an overloaded name with an unconstrained scheme rather than
an error.  The lowering IR is full of overloaded primitives, and for a
type oracle a lenient scheme is more useful than a hard failure.")

(defvar tl-type-lenient nil
  "When non-nil, unification failures are tolerated (the oracle mode).
Used when typing the lowering IR, whose higher-order/tuple/overload
shapes are broader than the HM core; a lenient result is preferred to
a hard failure.")

(defun tl-infer-define-clauses (env name clauses)
  "Infer NAME from CLAUSES (list of `(PARAMS . BODY)'); register a scheme."
  (let* ((placeholder (tl-fresh-tvar))
         (tl-infer-constraints nil)
         (tyenv (tl-env-type-env env))
         (sig (and (gethash name (tl-env-sig-env env))
                   (gethash name tyenv))))
    (puthash name (tl-tscheme nil placeholder) tyenv)
    (let ((bindings nil))
      (if (catch 'tl-clause-inconsistent
            (dolist (clause clauses)
              (let* ((params (car clause))
                     (body (cdr clause))
                     (ptypes (mapcar (lambda (_) (tl-fresh-tvar)) params))
                     (binds nil)
                     (ps params)
                     (pts ptypes))
                (while ps
                  (let ((r (tl-infer-pattern
                            (tl-zonk-env (cons nil env) bindings)
                            (car ps) (car pts))))
                    (setq binds (append (car r) binds)
                          bindings (tl-compose-bindings bindings (cdr r)))
                    (setq ps (cdr ps) pts (cdr pts))))
                (let* ((binds-z (mapcar (lambda (cell)
                                          (cons (car cell)
                                                (tl-apply-bindings
                                                 (cdr cell) bindings)))
                                        binds))
                       (env2 (tl-tenv-extend (cons nil env) binds-z))
                       (rb (tl-infer (tl-zonk-env env2 bindings) body)))
                  (setq bindings (tl-compose-bindings bindings (cdr rb)))
                  (let ((ctype (tl-apply-bindings (car rb) bindings)))
                    (dolist (pt (reverse (mapcar (lambda (p)
                                                   (tl-apply-bindings
                                                    p bindings))
                                                 ptypes)))
                      (setq ctype (tl-tarrow pt ctype)))
                    (let ((u (tl-unify-types placeholder ctype bindings)))
                      (unless (car u)
                        (if (or tl-type-lenient tl-type-lenient-clauses)
                            (throw 'tl-clause-inconsistent t)
                          (signal 'termlisp-type-error
                                  (list (format
                                         "Clause of %S has inconsistent type"
                                         name)))))
                      (setq bindings (cdr u)))))))
            nil)
          (puthash name (tl-tscheme nil (tl-fresh-tvar)) tyenv)
        (let* ((final (tl-apply-bindings placeholder bindings))
               (env-tvars (tl-env-free-tvars env))
               (gen-vars (tl-generalized-vars final env-tvars)))
          (if sig
              (let* ((u (tl-unify-types final (tl-skolemize-scheme sig) nil))
                     (fb (tl-compose-bindings bindings (cdr u))))
                (unless (car u)
                  (signal 'termlisp-type-error
                          (list (format "Definition of %S does not match its signature" name))))
                (setq tl-elab-bindings fb)
                (tl-close-constraints env nil tl-infer-constraints fb)
                (puthash name sig tyenv))
            (setq tl-elab-bindings bindings)
            (let ((kept (tl-close-constraints env gen-vars tl-infer-constraints bindings)))
              (puthash name (tl-generalize final env-tvars kept) tyenv))))))))

(defun tl-syntactic-value-p (expr)
  "Return non-nil if EXPR is a syntactic value (value restriction)."
  (or (atom expr)
      (and (consp expr) (eq (car expr) 'lambda))))

(defun tl-infer-constant (env name expr)
  "Infer a constant binding NAME = EXPR."
  (let* ((tl-infer-constraints nil)
         (r (tl-infer (cons nil env) expr)))
    (let* ((ty (tl-apply-bindings (car r) (cdr r)))
           (bindings (cdr r))
           (env-tvars (tl-env-free-tvars env)))
      (setq tl-elab-bindings bindings)
      (if (gethash name (tl-env-sig-env env))
          (let* ((sig (gethash name (tl-env-type-env env)))
                 (u (tl-unify-types ty (tl-skolemize-scheme sig) nil))
                 (fb (tl-compose-bindings bindings (cdr u))))
            (unless (car u)
              (signal 'termlisp-type-error
                      (list (format "Definition of %S does not match its signature" name))))
            (setq tl-elab-bindings fb)
            (tl-close-constraints env nil tl-infer-constraints fb)
            (puthash name sig (tl-env-type-env env))
            ty)
        (if (tl-syntactic-value-p expr)
            (let* ((gen-vars (tl-generalized-vars ty env-tvars))
                   (kept (tl-close-constraints env gen-vars tl-infer-constraints bindings)))
              (puthash name (tl-generalize ty env-tvars kept) (tl-env-type-env env)))
          (tl-close-constraints env nil tl-infer-constraints bindings)
          (puthash name (tl-tscheme nil ty) (tl-env-type-env env)))
        ty))))

(defun tl-register-signature (env form)
  "Register a `(: NAME TYPE)' signature in ENV."
  (let ((name (cadr form))
        (sc (tl-type-parse-scheme (caddr form))))
    (when (fboundp 'tl-kind-check-scheme)
      (tl-kind-check-scheme env sc))
    (puthash name sc (tl-env-type-env env))
    (puthash name t (tl-env-sig-env env))
    name))

(defun tl-typecheck-define (env form)
  "Typecheck a `define' FORM, registering it in ENV.
A definition whose name is a class method is skipped: its signature
comes from the class declaration (registered in `tl-env-method-env'),
and instance implementations are checked against that signature."
  (let ((target (cadr form)))
    (cond
     ((and (consp target) (gethash (car target) (tl-env-method-env env)))
      (car target))
     ((consp target)
      (let* ((name (car target))
             (params (cdr target))
             (body (caddr form))
             (clauses (append (gethash name (tl-env-clauses env))
                              (list (cons params body)))))
        (puthash name clauses (tl-env-clauses env))
        (tl-infer-define-clauses env name clauses)))
     (t (tl-infer-constant env target (caddr form))))))

(defun tl-register-class (env form)
  "Register `(class NAME (PARAM) SUPERS METHOD-DECL...)' in ENV."
  (let* ((name (nth 1 form))
         (param (car (nth 2 form)))
         (super-forms (nth 3 form))
         (method-decls (nthcdr 4 form))
         (param-var (tl-fresh-tvar))
         (methods nil)
         (supers nil))
    (dolist (sf super-forms)
      (let ((tl-type-parse-vars (list (cons param param-var))))
        (push (tl-constraint (car sf) (tl-type-parse* (cadr sf))) supers)))
    (setq supers (nreverse supers))
    (dolist (md method-decls)
      (let* ((mname (car md))
             (tl-type-parse-vars (list (cons param param-var)))
             (ty (tl-type-parse* (cadr md))))
        (push (cons mname
                    (tl-tscheme (tl-free-tvars ty)
                                ty
                                (list (tl-constraint name param-var))))
              methods)))
    (setq methods (nreverse methods))
    (puthash name (tl-cclass name (list param) supers methods)
             (tl-env-class-env env))
    (dolist (m methods)
      (puthash (car m) (cdr m) (tl-env-method-env env)))
    name))

(defun tl-register-instance (env form)
  "Register `(instance (CLASS TYPE) [DICT])' in ENV.
The optional DICT is the runtime dictionary value the elaborator inserts
as the first argument of overloaded method calls."
  (let* ((head (nth 1 form))
         (cname (car head))
         (ty (tl-type-parse (cadr head)))
         (dict (nth 2 form))
         (inst (tl-instance cname ty nil nil dict)))
    (puthash cname (append (gethash cname (tl-env-instance-env env)) (list inst))
             (tl-env-instance-env env))
    cname))

(defun tl-typecheck-form (env form)
  "Typecheck one top-level FORM in ENV."
  (let ((tl-infer-constraints nil))
    (cond
     ((and (consp form) (eq (car form) 'datatype)) (tl-eval-datatype env form))
     ((and (consp form) (eq (car form) 'datatype-extension))
      (tl-eval-datatype-extension env form))
     ((and (consp form) (eq (car form) ':)) (tl-register-signature env form))
     ((and (consp form) (eq (car form) 'define)) (tl-typecheck-define env form))
     ((and (consp form) (eq (car form) 'class)) (tl-register-class env form))
     ((and (consp form) (eq (car form) 'instance)) (tl-register-instance env form))
     (t (let ((r (tl-infer (cons nil env) form)))
          (tl-close-constraints env nil tl-infer-constraints (cdr r) t)
          (car r))))))

(defun termlisp-typecheck-def (env string)
  "Typecheck all top-level forms in STRING into ENV.  Return ENV."
  (dolist (form (termlisp-parse string) env)
    (tl-typecheck-form env form)))

(defun termlisp-typecheck (string &optional env)
  "Typecheck STRING in ENV (fresh if nil).  Return ENV; signal on error."
  (let ((env (or env (termlisp-make-env))))
    (termlisp-typecheck-def env string)))

(defun termlisp-typecheck-file (file &optional env)
  "Typecheck the contents of FILE in ENV."
  (termlisp-typecheck
   (with-temp-buffer (insert-file-contents file) (buffer-string))
   env))

(provide 'termlisp-types)
;;; termlisp-types.el ends here
