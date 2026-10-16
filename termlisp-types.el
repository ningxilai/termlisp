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
;;
;; Higher-kinded heads: an application node's head may itself be a
;; variable (`(f a)').  `tl-map-type' canonicalises and substitutes such a
;; head, and graph unification unifies a variable head with the other head,
;; so class parameters (`Functor f') work.  `tl-unify-types' sets the
;; dynamic `tl-occurrence-check' (from the `:occurs-check' env option) and
;; reports an infinite type or a kind clash as a `termlisp-type-error'.
;;
;; Type classes: predicates are `tl-constraint's; `tl-entail' resolves by
;; membership, superclass or instance; `tl-improve-constraints' applies
;; functional dependencies; `tl-split-context'/`tl-close-constraints'
;; reduce a context to retained (generalized) and deferred predicates,
;; defaulting ambiguous numerics.  Kinds are checked by `termlisp-kinds'.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-graph-unify)
(require 'termlisp-free-vars)
(require 'termlisp-reader)

(declare-function tl-eval-datatype "termlisp-eval" (env form))
(declare-function tl-eval-datatype-extension "termlisp-eval" (env form))
(declare-function tl-desugar-do "termlisp-eval" (form))
(declare-function tl-desugar-let "termlisp-eval" (form))
(declare-function tl-let-check-form "termlisp-eval" (form))
(declare-function tl-desugar-list "termlisp-eval" (form))
(declare-function tl-rewrite-desugar "termlisp-eval" (env form))
;; Defined by termlisp-nbe, which loads after this file because it
;; requires it: declared here so `tl-preserve-check' can bind it
;; around the comparison it makes, with the same reduction a checked
;; program's own comparisons run under.
(defvar tl-nbe-reduce-env)

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
(cl-defstruct (tl-cclass (:constructor tl-cclass (name params supers methods &optional fundeps kinds)))
  name params supers methods fundeps kinds)
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
  "Return the head symbol of the compound type X.
X is dereferenced first, so a variable bound to a compound type reads
off that type's head."
  (tl-node-head (tl-type-deref x)))

(defun tl-tcon-args (x)
  "Return the argument types of the compound type X, or nil for a leaf.
X is dereferenced first, so a variable bound to a compound type reads
off that type's arguments."
  (tl-node-children (tl-type-deref x)))

(defun tl-tvar-p (x)
  "Non-nil when X is a (deref'd) type-variable node."
  (let ((d (tl-type-deref x)))
    (and (tl-node-p d) (tl-node-var d))))

(defvar tl-current-level 1
  "The generalization scope currently being inferred.
Entering a function body raises it, and it is back down again once that
body is done.  A type variable records the level it was introduced at
\(see `tl-node-level'), which decides two things about it.  An enclosing
generalization point quantifies it, because a deeper level means it was
created inside the body being generalized.  And nothing shall bind it to
a term naming a variable from a still deeper scope, which would let an
inner variable escape outwards into a place that outlives it.")

(defun tl-fresh-tvar (&optional level)
  "Return a fresh type variable node introduced at LEVEL.
LEVEL defaults to `tl-current-level', the scope being inferred.  That
default is what makes the variable generalizable by every enclosing
`let', and by no scope outside the one that introduced it."
  (let ((node (tl-make-var-node (gensym "t"))))
    (setf (tl-node-level node) (or level tl-current-level))
    node))

(defun tl-tarrow (a b)
  "Return the function type from A to B."
  (tl-tcon '-> (list a b)))
(defun tl-tint ()
  "Return the type of integers."
  (tl-tcon 'Int nil))
(defun tl-tstring ()
  "Return the type of strings."
  (tl-tcon 'String nil))
(defun tl-tbool ()
  "Return the type of booleans."
  (tl-tcon 'Bool nil))

(defun tl-tfun-args (ty)
  "If TY is `(-> a b)', return (a b), else nil."
  (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
    (tl-tcon-args ty)))

(defvar tl-occurrence-check nil
  "When non-nil, unification performs the occurs check.
A cyclic (infinite) type is then rejected with a `termlisp-type-error'
naming it.  Off by default: equirecursive types (as in Coalton) are
allowed.")

(defun tl-type-to-datum (type)
  "Render TYPE as a readable, cycle-safe s-expression datum.
Type variables become `?N' symbols; an equirecursive cycle is rendered
with an `!N' back-reference, so the result is always finite."
  (let ((names (make-hash-table :test #'eq))
        (n 0))
    (cl-labels ((go (node)
                  (let ((node (tl-type-deref node)))
                    (cond
                     ;; A `Pi' binder renders under its own name, not as
                     ;; `?N': the whole point of a dependent function
                     ;; type is that the reader can see what it binds.
                     ((and (tl-node-var-p node) (tl-node-rigid node))
                      (or (gethash node names)
                          (let ((s (tl-node-head node)))
                            (puthash node s names) s)))
                     ((tl-tvar-p node)
                      (or (gethash node names)
                          (let ((s (intern (format "?%d" (cl-incf n)))))
                            (puthash node s names) s)))
                     ((and (tl-tcon-p node) (eq (tl-node-head node) 'Pi)
                           (= (length (tl-tcon-args node)) 3))
                      (let ((a (tl-tcon-args node)))
                        (list (list (go (nth 0 a)) ': (go (nth 1 a)))
                              '-> (go (nth 2 a)))))
                     ((and (tl-tcon-p node) (eq (tl-node-head node) 'lambda)
                           (= (length (tl-tcon-args node)) 2))
                      (let ((a (tl-tcon-args node)))
                        (list 'lambda (list (go (nth 0 a))) (go (nth 1 a)))))
                     ((tl-tcon-p node)
                      (let ((head (tl-type-deref (tl-tcon-name node))))
                        (if (gethash node names)
                            (gethash node names)
                          (puthash node (intern (format "!%d" (cl-incf n))) names)
                          (let ((args (tl-tcon-args node)))
                            (if (null args)
                                (if (tl-node-var-p head) (go head) head)
                              (cons (if (tl-node-var-p head) (go head) head)
                                    (mapcar #'go args)))))))
                     (t node)))))
      (go type))))

(defun tl-unify-types (a b bindings)
  "Unify types A and B in place under BINDINGS.  Return `(ok . bindings)'.
On failure returns `(nil . nil)'; failed attempts are rolled back.  When
`tl-occurrence-check' is non-nil, a cyclic binding signals a
`termlisp-type-error' describing the infinite type."
  (let ((tl-gnode--fail-reason nil))
    (if (tl-gnode-unify a b tl-occurrence-check)
        (cons t bindings)
      (cond
       ((eq tl-gnode--fail-reason 'infinite-type)
        (signal 'termlisp-type-error
                (list (format "Infinite type: %S unifies with %S"
                              (tl-type-to-datum a)
                              (tl-type-to-datum b)))))
       ((eq tl-gnode--fail-reason 'kind-mismatch)
        (signal 'termlisp-type-error
                (list (format "Kind mismatch: %S vs %S"
                              (tl-type-to-datum a)
                              (tl-type-to-datum b)))))
       (t (cons nil nil))))))

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

(defun tl-type--domain-sexp (rest)
  "Turn REST, a binder's tokens after its `:', into a type sexp.
`Vec a n' is one application and `a -> b' is an arrow chain, and both can
occur in the same domain, so the tokens are split on `->' first and each
run is then put back exactly as it was written.  Reading the whole tail
as a chain instead would turn `Vec a n' into `Vec -> a -> n', which is a
type nobody wrote and a kind error by the time anything checks it."
  (cond ((null (cdr rest)) (car rest))
        ((not (memq '-> rest)) rest)
        (t (cons '-> (mapcar (lambda (p) (if (cdr p) p (car p)))
                             (tl-split-arrow rest))))))

(defun tl-type-parse--binder (part)
  "Return (NAMES DOMAIN) when PART is a single binder token `(N... : TYPE)'.
NAMES is a list of the names, so `(n m : Nat)' binds two names over one
domain while `(n : Nat)' still binds one -- a comma between the names is
just whitespace to the reader, so the two spellings differ only in how
many names precede the `:'.  The domain runs from the `:' to the end of
the token, so both `(f : a -> b)' and `(xs : Vec a n)' bind over the type
that follows without parentheses.  They used not to: the `:' was only
looked for a single token from the end, so a bare `->' read as an arrow
*between* `f : a' and `b', and `f' came back applied to the keyword `:',
which is a type that looks nothing like the one written and reports
itself only as a stray kind error much later.  Anything else comes back
nil, so an ordinary segment is left alone."
  (let ((tok (car part)))
    (when (and (null (cdr part)) (consp tok))
      (let ((colon (cl-position ': tok)))
        (when (and colon (> colon 0) (< colon (1- (length tok)))
                   (cl-loop for x on tok until (eq x (nthcdr colon tok))
                            always (symbolp (car x))))
          (list (cl-subseq tok 0 colon)
                (tl-type--domain-sexp (nthcdr (1+ colon) tok))))))))

(defun tl-type-parse-pi (name domain parse-body)
  "Build a dependent function type with binder NAME over DOMAIN.
PARSE-BODY is called under the binder's scope to produce the codomain,
which is what lets `(n : Nat) -> Vec a n' mention the term it binds.
DOMAIN is parsed first, outside that scope, so a binder never sees
itself -- `((n : Nat) -> ...)' cannot smuggle `n' into its own type."
  (let* ((dom (tl-type-parse* domain))
         (v (tl-make-rigid-var name))
         (tl-type-parse-vars (cons (cons name v) tl-type-parse-vars)))
    (tl-tcon 'Pi (list v dom (funcall parse-body)))))

(defun tl-type-parse-arrow (parts)
  "Parse PARTS as a right-associative arrow chain, honouring binders.
A part whose single token is a binder `(NAME : TYPE)' turns the arrow
into a dependent function type, so `(n : Nat) -> Vec a n -> a' is a Pi
while `A -> B' keeps the ordinary non-dependent `->'.  A non-dependent
arrow is what every existing datatype in the prelude is written with,
and is deliberately not desugared into a Pi here: keeping them distinct
means the kind checker can still tell a function of terms from a
function of types without normalising anything.  Several names may share
one domain, `(n m : Nat) -> ...', and then become nested Pis in the
order written."
  (if (null (cdr parts))
      (tl-type-parse-segment (car parts))
    (let ((binder (tl-type-parse--binder (car parts))))
      (if binder
          (cl-labels ((bind (names)
                        (if (null names)
                            (tl-type-parse-arrow (cdr parts))
                          (tl-type-parse-pi (car names) (cadr binder)
                                            (lambda () (bind (cdr names)))))))
            (bind (car binder)))
        (tl-tarrow (tl-type-parse-segment (car parts))
                   (tl-type-parse-arrow (cdr parts)))))))

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
   ;; A literal in type position: `Vec a 3' indexes by a number, and the
   ;; node's HEAD slot is documented to carry a literal for leaves.
   ((or (numberp sexp) (stringp sexp)) (tl-make-node sexp nil nil))
   ;; Type-level lambda.  Its parameter is bound, not free, so it must
   ;; not be registered as an ordinary (unifiable) type variable.
   ((and (consp sexp) (eq (car sexp) 'lambda) (= (length sexp) 3)
         (symbolp (if (consp (cadr sexp)) (car (cadr sexp)) (cadr sexp))))
    (let* ((p (if (consp (cadr sexp)) (car (cadr sexp)) (cadr sexp)))
           (v (tl-make-rigid-var p))
           (tl-type-parse-vars (cons (cons p v) tl-type-parse-vars)))
      (tl-tcon 'lambda (list v (tl-type-parse* (caddr sexp))))))
   ;; Explicit `Pi', spelled out for programmatic construction; the
   ;; arrow-chain form above is the one meant to be read.
   ((and (consp sexp) (eq (car sexp) 'Pi) (= (length sexp) 3)
         (tl-type-parse--binder (list (cadr sexp))))
    (let ((b (tl-type-parse--binder (list (cadr sexp)))))
      (tl-type-parse-pi (car b) (cadr b)
                        (lambda () (tl-type-parse* (caddr sexp))))))
   ((consp sexp)
    ;; A lambda in head position parses to the very node a lambda
    ;; written alone parses to, so the two spellings cannot diverge:
    ;; `tl-nbe--whnf' reaches the head to find out whether the
    ;; application beta-reduces, and the raw form would never answer.
    ;; Any other head keeps the parse-var treatment it always had.
    (tl-tcon (let ((h (car sexp)))
               (if (and (consp h) (eq (car h) 'lambda))
                   (tl-type-parse* h)
                 (tl-type-head h)))
             (mapcar #'tl-type-parse* (cdr sexp))))
   (t (signal 'termlisp-type-error (list (format "Bad type: %S" sexp))))))

(defun tl-type-parse (sexp)
  "Parse surface type expression SEXP into a type."
  (let ((tl-type-parse-vars nil))
    (tl-type-parse* sexp)))

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

(defun tl--splice-head (head)
  "Return `(HEAD-NAME . EXTRA-CHILDREN)' for HEAD used in head position.
A binder in head position stands for the argument's value, and a value
with arguments of its own is a *spine*, not a head: `(f x)' over
`f := (VCons Zero)' is `(VCons Zero x)'.  So a substituted head is either
reduced to the symbol it names -- the shape a head written in a type
already has, and the only shape the reducer can look a function up
under -- or spliced, its own children going in front of the ones it is
being applied to.

Without this the two spellings of one term diverge exactly where it
counts: `(zc t)' reduces to `(VCons Zero t)' while the substituted
`((zc) t)' reduces to nothing, and a unifier that would have agreed with
either side on its own is left comparing a `VCons' against a `zc'.

Variables are left alone, since a higher-kinded head variable is a head
and not a term to splice.  So are `lambda' and `Pi', whose children are
bound syntax rather than arguments: splicing `(lambda (v) body)' into
the applications around it would turn three children into three
unrelated ones where the lambda is a function of two."
  (cond
   ((not (tl-node-p head)) (cons head nil))
   ((tl-node-var-p head) (cons head nil))
   ((memq (tl-node-head head) '(lambda Pi)) (cons head nil))
   ((not (tl-node-application head)) (cons (tl-node-head head) nil))
   (t (let ((inner (tl--splice-head (tl-node-head head))))
        (cons (car inner)
              (append (cdr inner) (tl-node-children head)))))))

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
                      (let* ((args (tl-tcon-args node))
                             ;; canonicalise the head first: a unioned
                             ;; (but not yet deref'd) head var must map
                             ;; to its representative, else instantiation
                             ;; would leave sibling heads distinct.
                             (head (tl-type-deref (tl-tcon-name node))))
                        (if (null args)
                            node
                          (or (gethash node memo)
                              (let* ((spliced
                                      (if (tl-node-var-p head)
                                          ;; a higher-kinded head var is
                                          ;; substituted too, so scheme
                                          ;; instantiation copies it --
                                          ;; and what it is substituted
                                          ;; with is a *value*, which may
                                          ;; be a spine and not a name.
                                          (tl--splice-head (funcall f head))
                                        ;; A head that was never a variable
                                        ;; was written where it stands:
                                        ;; leave it, spine and all, exactly
                                        ;; as it was.
                                        (cons head nil)))
                                     (new (tl-make-node (car spliced) nil t)))
                                (puthash node new memo)
                                (setf (tl-node-children new)
                                      (append (cdr spliced)
                                              (mapcar #'go args)))
                                new)))))
                     (t node)))))
      (go type))))

(defun tl-type-subst (type sub)
  "Apply substitution SUB (alist var-node -> type) to TYPE."
  (tl-map-type
   (lambda (tv) (let ((cell (assq tv sub))) (if cell (cdr cell) tv)))
   type))

(defun tl-generalized-vars (type &optional level)
  "Return the type variables of TYPE that are generalizable at LEVEL.
LEVEL defaults to `tl-current-level'.  A variable qualifies when it was
introduced *inside* the scope being generalized -- a deeper level says
exactly that: it did not exist when the scope opened, so nothing outside
the scope can be relying on it.  A variable carrying no level, one made
directly rather than through `tl-fresh-tvar', predates every scope and
is therefore never quantified."
  (let ((at (or level tl-current-level)))
    (cl-remove-if (lambda (v)
                    (let ((l (tl-node-level v)))
                      (null (and l (> l at)))))
                  (tl-free-tvars type))))

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

(defun tl-constraint-args (c)
  "Return the parameter type list of predicate C.
A single-parameter predicate stores its argument directly; a multi-parameter
one stores `(Class t1 ... tk)'."
  (let ((ty (tl-type-deref (tl-constraint-type c))))
    (if (and (tl-tcon-p ty)
             (eq (tl-tcon-name ty) (tl-constraint-class c))
             (cdr (tl-tcon-args ty)))
        (tl-tcon-args ty)
      (list ty))))

(defun tl-improve-constraints (env preds)
  "Unify predicate parameters according to class functional dependencies.
Mutate the type graph in place and return non-nil when any equality was
learned.  Iterated to a fixpoint; speculative unifications roll back on
failure."
  (let ((changed nil) (again t))
    (while again
      (setq again nil)
      (dolist (c preds)
        (let* ((cls (gethash (tl-constraint-class c) (tl-env-class-env env)))
               (fds (and cls (tl-cclass-fundeps cls)))
               (args (tl-constraint-args c)))
          (dolist (fd fds)
            (let ((from (car fd)) (to (cdr fd)))
              (dolist (c2 preds)
                (when (and (not (eq c c2))
                           (eq (tl-constraint-class c) (tl-constraint-class c2)))
                  (let ((args2 (tl-constraint-args c2)))
                    (when (cl-every
                           (lambda (i)
                             (let ((a (nth i args)) (b (nth i args2)))
                               (and a b
                                    (or (eq (tl-gnode-deref a) (tl-gnode-deref b))
                                        (tl-gnode-unify a b)))))
                           from)
                      (dolist (j to)
                        (let ((a (nth j args)) (b (nth j args2)))
                          (when (and a b
                                     (not (eq (tl-gnode-deref a) (tl-gnode-deref b)))
                                     (tl-gnode-unify a b))
                            (setq changed t again t)))))))))))))
    changed))

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

(defun tl-ambiguities (env env-vars preds)
  "Return the predicates of PREDS that are ambiguous.
A variable is determined when it is in ENV-VARS, or is a `to' parameter of
a predicate whose `from' parameters (per a class functional dependency)
are all determined.  A predicate is ambiguous when any of its variables is
undetermined."
  (let ((det (copy-sequence env-vars)) (changed t))
    (while changed
      (setq changed nil)
      (dolist (c preds)
        (let* ((cls (and env (gethash (tl-constraint-class c)
                                      (tl-env-class-env env))))
               (fds (and cls (tl-cclass-fundeps cls)))
               (args (tl-constraint-args c)))
          ;; Fundep determination: determined `from' forces `to'.
          (dolist (fd fds)
            (when (cl-every
                   (lambda (i)
                     (cl-every (lambda (v) (memq v det))
                               (tl-free-tvars (nth i args))))
                   (car fd))
              (dolist (j (cdr fd))
                (dolist (v (tl-free-tvars (nth j args)))
                  (unless (memq v det) (push v det) (setq changed t))))))
          ;; Plain closure: a predicate's own variables, once determined.
          (let ((vs (tl-free-tvars (tl-constraint-type c))))
            (when (cl-every (lambda (v) (memq v det)) vs)
              (dolist (v vs)
                (unless (memq v det) (push v det) (setq changed t))))))))
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

(defun tl-constraints-zonk (constraints bindings)
  "Return CONSTRAINTS with every one of its types pushed through BINDINGS.
This is one pass only: it reports where the constraints currently stand,
it does not decide anything about them."
  (mapcar (lambda (c)
            (tl-constraint (tl-constraint-class c)
                           (tl-apply-bindings (tl-constraint-type c) bindings)))
          constraints))

(defun tl-constraints-improve (env constraints)
  "Return CONSTRAINTS after the fundeps ENV's classes declare are applied.
`tl-improve-constraints' writes the equalities it learns straight into
the type graph, so CONSTRAINTS is zonked once more before being handed
on: those equalities are only visible through the bindings just written."
  (tl-improve-constraints env constraints)
  (tl-constraints-zonk constraints nil))

(defun tl-constraints-default (env deferred)
  "Return DEFERRED with each defaultable variable replaced by its default.
Which classes carry a default is `tl-default-subs'' business, asked of
ENV; a constraint no default applies to comes back unchanged, still free."
  (let ((subs (tl-default-subs env deferred)))
    (mapcar (lambda (c)
              (tl-constraint (tl-constraint-class c)
                             (tl-type-subst (tl-constraint-type c) subs)))
            deferred)))

(defun tl-constraints-check (env retained deferred &optional reject-ambiguous)
  "Signal `termlisp-type-error' for a DEFERRED constraint RETAINED cannot entail.
Instances are looked for in ENV.  A ground constraint with no matching
instance is always an error.  One
still mentioning free type variables is an error only with
REJECT-AMBIGUOUS; without it the ambiguity is left standing to be
solved, defaulted, or generalized away somewhere outwards."
  (dolist (c deferred)
    (unless (tl-entail env retained c)
      (let ((free (tl-free-tvars (tl-constraint-type c))))
        (when (or reject-ambiguous (null free))
          (signal 'termlisp-type-error
                  (list (if free
                            (format "Ambiguous constraint: no instance for %S %S"
                                    (tl-constraint-class c) (tl-constraint-type c))
                          (format "No instance for %S %S"
                                  (tl-constraint-class c) (tl-constraint-type c))))))))))

(defun tl-constraints-dedup (retained)
  "Return RETAINED with duplicate constraints dropped.
Duplicates are those agreeing on `tl-constraint-canonical-key' and
`tl-constraint-eq', so two spellings of the same predicate reach the
scheme's context once."
  (tl-remove-duplicates-by-key retained
                               #'tl-constraint-canonical-key #'tl-constraint-eq))

(defun tl-close-constraints (env gen-vars constraints bindings &optional reject-ambiguous)
  "Zonk CONSTRAINTS, retain the generalizable ones, solve or default the rest.
GEN-VARS are the type variables being generalized; a constraint whose
type mentions one is retained.  The deferred constraints are defaulted
\(see `tl-default-subs') and solved; an unsolved ground constraint -- or,
with REJECT-AMBIGUOUS, one still mentioning free type variables -- is
rejected with `termlisp-type-error'.

The work is staged, one function per stage, so a caller or a reader can
see the shape of it in five lines and take any single stage on its own:

  `tl-constraints-zonk'     where the constraints stand now
  `tl-constraints-improve'  what class fundeps learned from them
  `tl-split-context'        which are kept with the scheme
  `tl-constraints-default'  what numeric defaulting settles
  `tl-constraints-check'    what nothing could account for"
  (let* ((zonked (tl-constraints-zonk constraints bindings))
         (improved (tl-constraints-improve env zonked))
         (split (tl-split-context env gen-vars improved))
         (retained (car split))
         (deferred (tl-constraints-default env (cadr split))))
    (tl-constraints-check env retained deferred reject-ambiguous)
    (tl-constraints-dedup (nreverse retained))))

(defun tl-generalize (type &optional constraints level)
  "Generalize TYPE, quantifying the variables generalizable at LEVEL,
keeping CONSTRAINTS whose type mentions a quantified variable.  LEVEL
defaults to `tl-current-level'; `tl-generalized-vars' is what decides
which variables qualify."
  (let* ((vars (tl-generalized-vars type level))
         (kept (cl-remove-if-not
                (lambda (c)
                  (cl-intersection vars (tl-free-tvars (tl-constraint-type c))))
                constraints)))
    (tl-tscheme vars (tl-map-type #'identity type)
                (tl-remove-duplicates-by-key kept
                                             #'tl-constraint-canonical-key #'equal))))

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

(defvar tl-elab-fn-sites nil
  "Calls to constrained functions recorded during inference.
Each element is `(FORM . CONSTRAINTS)': the application cons cell and the
instantiated constraints of the callee's scheme.  Only populated while
`tl-elab-active' is non-nil.  Used for dictionary passing.")

(defvar tl-elab-let-dicts nil
  "Constrained local `let'/`Let' bindings recorded during elaboration.
Each element is `(BINDING-CELL . (CONSTRAINTS . DICT-NAMES))': the binding
form `(NAME EXPR)' and the dictionary parameters to abstract its lambda
over.  Only populated while `tl-elab-active' is non-nil.")

(defvar tl-elab-bindings nil
  "Final substitution of the most recent inference, for elaboration.
Set by the define/constant entry points so the elaborator can zonk the
recorded method-call constraints.")

(defun tl-emit-constraint (c)
  "Record constraint C in the current `tl-infer-constraints'."
  (push c tl-infer-constraints))

(defun tl-fresh-instance-var (v)
  "Return a fresh variable standing in for the quantified variable V.
It carries V's kind, so a higher-kinded variable stays higher-kinded.
Its level sits one deeper than the scope doing the instantiating: what
an instantiation introduces is known to no one yet, so every enclosing
`let' is free to quantify it, which is what leaves `let f = g' as
polymorphic as it is in Haskell."
  (let ((nv (tl-fresh-tvar (1+ tl-current-level))))
    (when (tl-node-kind v)
      (setf (tl-node-kind nv) (tl-node-kind v)))
    nv))

(defun tl-instantiate-scheme (scheme)
  "Instantiate SCHEME with fresh type variables.
Return `(TYPE . CONSTRAINTS)', freshening the type and any constraints
with the same substitution.  A non-scheme is returned as
`(SCHEME . nil)'."
  (if (tl-tscheme-p scheme)
      (let ((sub (mapcar (lambda (v) (cons v (tl-fresh-instance-var v)))
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

(defun tl-skolemize-scheme (scheme)
  "Replace SCHEME's quantified variables with rigid type constants."
  (tl-type-subst (tl-tscheme-type scheme)
                 (mapcar (lambda (v) (cons v (tl-tcon (gensym "sk") nil)))
                         (tl-tscheme-vars scheme))))

(defvar tl-builtin-types (make-hash-table :test #'eq)
  "Type schemes for builtin functions.
`termlisp-types' registers the arithmetic core at its own load; the
rest of the bundled primitives arrive with `termlisp-ir-types', which
`termlisp-eval' requires, so every evaluator and loader sees them
while a host requiring `termlisp-types' alone keeps the core and
registers whatever else it has.  See `tl-register-builtin-type'.")

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
                                          &optional (param-syms nil param-syms-p)
                                          param-annos)
  "Register constructor type schemes for datatype NAME with CTORS.
PARAM-SYMS, if non-nil, are the datatype's declared type parameters
\(reused for extensions and for an explicitly declared parameter list).
PARAM-ANNOS, when given, is an alist mapping a parameter symbol to the
kind sexp its declaration annotated it with; see `tl-kind-parse'.
Returns the datatype's parameter symbols.
When PARAM-SYMS is explicitly supplied (even nil), CTORS are an
extension and any type parameter not declared by the datatype is an
error.

A constructor may declare its own result type after a top-level `:',
see `tl-split-ctor'.  That is what makes an indexed (GADT) declaration
possible: `Cons' returns `(Vec a (Succ n))' rather than `Vec' applied to
the parameters, so pattern matching can unify that index against the
scrutinee.  A constructor that omits the `:' returns NAME applied to the
parameters, exactly as every ordinary datatype always has."
  (let* ((tl-type-parse-vars
          ;; A declared parameter is named after itself rather than left
          ;; as a bare gensym, because a `kpi' binds one and a kind is
          ;; then read back in messages: `Π(a : *).' says which parameter
          ;; the next one comes out of, and `Π(t1710 : *).' says nothing
          ;; at all.  The head of a variable is otherwise unused -- every
          ;; comparison goes through the BIND slots -- so this costs
          ;; nothing but legibility.
          (mapcar (lambda (s)
                    (let ((v (tl-fresh-tvar)))
                      (setf (tl-node-head v) s)
                      (cons s v)))
                  param-syms))
         (split (mapcar #'tl-split-ctor ctors))
         (ctor-args (cl-mapcar (lambda (ctor cells)
                                 (cons (car ctor) (mapcar #'tl-type-parse* (car cells))))
                               ctors split))
         ;; Results parse in the same dynamic scope as the fields, so an
         ;; index that appears only in a result still becomes a parameter
         ;; and shares one type variable with every other use of it.
         (ctor-results (mapcar (lambda (cells)
                                 (and (cdr cells) (tl-type-parse* (cdr cells))))
                               split))
         (syms (or param-syms (mapcar #'car (reverse tl-type-parse-vars))))
         ;; A kind annotation is read in this same scope, so `(univ a)'
         ;; reaches the very node that parameter `a' already is.  The
         ;; dependency has to point at the parameter itself and not at a
         ;; copy of it: the binder `kpi' creates has to be the variable
         ;; the rest of the declaration talks about, or the two would
         ;; disagree about which type the index came out of.
         (kind-annos
          (and param-annos (fboundp 'tl-kind-parse)
               (mapcar (lambda (cell)
                         (let ((tv (cdr (assq (car cell) tl-type-parse-vars))))
                           (unless tv
                             (signal 'termlisp-type-error
                                     (list (format "Kind annotation on unknown parameter %S"
                                                   (car cell)))))
                           (cons tv (tl-kind-parse (cdr cell) param-syms))))
                       param-annos))))
    (when param-syms-p
      (dolist (cell tl-type-parse-vars)
        (unless (memq (car cell) param-syms)
          (signal 'termlisp-type-error
                  (list (format "Undeclared type parameter %S in extension of %S"
                                (car cell) name))))))
    (let* ((params (mapcar (lambda (s) (cdr (assq s tl-type-parse-vars))) syms))
           (results (mapcar (lambda (r) (or r (tl-tcon name params)))
                            ctor-results))
           ;; The arity is known before anything is kinded, so stand the
           ;; datatype up now, with a fresh variable for each parameter's
           ;; kind.  A result that applies this datatype to the wrong
           ;; number of arguments is then an error here, at the
           ;; declaration, rather than something the reader meets much
           ;; later at the first use.  The parameter kinds are still
           ;; inferred below and the entry registered properly then; this
           ;; one exists to make the shape checkable, not to decide it.
           ;; A head that does not exist yet -- one this datatype is
           ;; mutually recursive with, or one an oracle has not
           ;; declared -- takes a fresh variable of its own and is left
           ;; unchecked, which is the leniency a forward reference needs.
           (early (and (fboundp 'tl-kind-var)
                       (let ((k tl-kind-star))
                         (dotimes (_ (length params))
                           (setq k (tl-karr (tl-kind-var) k)))
                         k))))
      (when early (puthash name early (tl-env-kind-env env)))
      ;; Infer each parameter's kind from the constructor field types; a
      ;; well-formed field is a proper type.  An unknown head is not an
      ;; error: it takes a fresh kind variable, which unifies with
      ;; anything, so only a head that is known and applied wrongly is
      ;; caught -- exactly the distinction to be drawn.
      (when (fboundp 'tl-kind-check)
        (dolist (ca ctor-args)
          (dolist (argty (cdr ca))
            (tl-kind-check env argty))))
      ;; Lift the constructors to the type level *before* the results are
      ;; kinded: a result is the only place an index variable meets the
      ;; universe it belongs to, so `kind(n) = Nat' is settled right here.
      (when (fboundp 'tl-register-lifted-constructors)
        (tl-register-lifted-constructors env name ctor-args))
      ;; A constructor may share the datatype's name -- `(Pair a b)' has
      ;; to -- and lifting writes that constructor's kind under the name
      ;; too, which is a different kind: `Zero' takes the universe `Nat'
      ;; where `Nat' itself takes `*'.  In a result type the name means
      ;; the datatype, so stand the datatype's entry back up before the
      ;; results are read against it.  This only moves the constructor's
      ;; entry aside sooner; `tl-register-datatype-kind' below settled it
      ;; over afterwards all along.
      (when early (puthash name early (tl-env-kind-env env)))
      (when (fboundp 'tl-kind-check)
        (dolist (r results)
          (tl-kind-check env r)))
      ;; The datatype's kind is `kind(param1) -> ... -> *', or its arity
      ;; when kind inference is unavailable.
      (cond ((fboundp 'tl-register-datatype-kind)
             (tl-register-datatype-kind env name params kind-annos))
            (t (puthash name (length syms) (tl-env-kind-env env))))
      ;; Each constructor arrows its field types onto its own result.
      (dolist (pair (cl-mapcar #'cons ctor-args results))
        (let ((ca (car pair)) (ty (cdr pair)))
          (dolist (argty (reverse (cdr ca)))
            (setq ty (tl-tarrow argty ty)))
          (puthash (car ca) (tl-tscheme params ty)
                   (tl-env-type-env env))))
      syms)))

(defun tl-tenv-locals (env)
  "Return the local bindings ENV carries in front of its base env.
During inference an environment is a pair `(LOCALS . BASE)' of the
bindings introduced by enclosing binders and the `tl-env' they were
introduced over; a bare `tl-env' has no locals, so this is nil for it."
  (if (consp env) (car env) nil))

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
   ;; A `let' binds names and gives their values types, and that is all it
   ;; does -- but the shape it is given in decides whether those types can
   ;; ever be quantified.  Rewriting it into an inline-lambda application,
   ;; which is what inference used to do, closes the question before it is
   ;; asked: a lambda application instantiates its argument's scheme at one
   ;; type and the binding is monomorphic from then on.  `let' therefore
   ;; keeps its bindings as bindings and goes to the rule that knows how to
   ;; quantify them.  Without a rule of its own it falls through to
   ;; `tl-infer-application', where `let' is just an unknown function -- so
   ;; the whole body typechecks as a fresh unconstrained variable and
   ;; nothing the body says is checked at all.
   ((and (consp expr) (eq (car expr) 'let))
    (tl-let-check-form expr)
    (let ((rule (gethash 'Let tl-infer-ir-heads)))
      ;; With `termlisp-ir-types' loaded there is a rule that can quantify
      ;; the bindings; without it the table is empty and `let' falls back
      ;; to the lambda application, which typechecks if it does not
      ;; generalize -- still better than dropping to
      ;; `tl-infer-application', where `let' is an unknown function and
      ;; the body is never checked.
      (if rule
          (funcall rule env (cons 'Let (cdr expr)))
        (tl-infer env (tl-desugar-let expr)))))
   ;; `(list e...)' is variadic, so it carries no scheme of its own.  Expand
   ;; it to nested `Cons' applications (as the evaluator does in `tl-run')
   ;; and infer the result, which gives `list' an arity-indexed type at every
   ;; call site and enforces element homogeneity.
   ((and (consp expr) (eq (car expr) 'list))
    (tl-infer env (tl-desugar-list expr)))
   ;; `reduce TERM' evaluates to TERM's normal form, and a normal form
   ;; has the type TERM had: that is preservation, which `rewrite' is
   ;; the form that has to prove for a rule it adds.  The argument is
   ;; inferred as written -- typechecking reads the term, the reduction
   ;; happens at evaluation -- and its arity is checked here because an
   ;; expression form has no pattern of its own to be checked against.
   ((and (consp expr) (eq (car expr) 'reduce))
    (unless (and (consp (cdr expr)) (null (cddr expr)))
      (signal 'termlisp-type-error '("reduce takes exactly one term")))
    (tl-infer env (cadr expr)))
   ((and (consp expr) (gethash (car-safe expr) tl-infer-ir-heads))
    (funcall (gethash (car-safe expr) tl-infer-ir-heads) env expr))
   ((consp expr) (tl-infer-application env expr))
   (t (signal 'termlisp-type-error (list (format "Cannot infer: %S" expr))))))

(defvar tl-infer-holes nil
  "The `_' holes left in the form being inferred, most recent first.
Each entry is a fresh type variable standing for one hole.  Recording
them is what lets a driver show a goal for every position the program
said nothing about, instead of leaving an unsolved variable that looks
just like an ordinary unknown.  Callers that want to report holes bind
this; inference itself neither requires nor clears it.")

(defun tl-infer-hole ()
  "Return a fresh type variable standing for a `_'.
The variable is recorded in `tl-infer-holes' so whoever is driving the
inference can report the goal it leaves behind.  A hole types exactly
like an ordinary unknown -- that is what makes it usable inside a larger
term, where the surrounding context decides what it must be -- but it is
remembered, so it is never mistaken for something the program answered."
  (let ((v (tl-fresh-tvar)))
    (push v tl-infer-holes)
    v))

(defun tl-goal--readable (datum)
  "Return DATUM with numbered metavariables spelled `t1', `t2', ...
A `?1' symbol prints as `\\?1' because `?1' is the reader's character
syntax, so handing the datum straight back would show a goal in spelling
the reader re-reads as a character rather than as the variable it stood
for."
  (cond
   ((symbolp datum)
    (let ((name (symbol-name datum)))
      (if (string-match-p "\\`?[0-9]+\\'" name)
          (intern (concat "t" (if (eq (aref name 0) ??)
                                  (substring name 1)
                                name)))
        datum)))
   ((consp datum) (cons (tl-goal--readable (car datum))
                        (tl-goal--readable (cdr datum))))
   (t datum)))

(defun tl-goal-lines (holes)
  "Return one display line per hole in HOLES, most recent last.
What a hole's type has already become is the whole point: `(+ 1 _)'
leaves a hole the context has decided is a number, and saying so is
worth far more than printing an unknown on its own.  The node is
dereferenced rather than zonked through a substitution, because
unification wrote the answer straight into the hole itself."
  (let ((lines nil) (n 0))
    (dolist (h (reverse holes) (nreverse lines))
      (setq n (1+ n))
      (push (format "hole %d : %s" n
                    (format "%S" (tl-goal--readable
                                  (tl-type-to-datum (tl-gnode-deref h)))))
            lines))))

(defvar tl-infer-forward-names nil
  "Names the unit being checked declares in a later form, or nil.
A hash table mapping each such name to t.  A file, or a string holding
several top-level forms, may mention a definition before the form that
introduces it; inference cannot know that name's type yet, so it hands
out a fresh variable, exactly as it once did for every unknown symbol.
What changed is the scope of the allowance: outside such a unit, or for
a name that no upcoming form declares, an unresolved symbol is an error
rather than an unconstrained variable.  That is what made `(nosuch 1)'
typecheck and then evaluate to a stuck form -- an unbound head
constrains nothing, so nothing downstream was checked either.")

(defvar tl-infer-forward-vars nil
  "Pending forward references of the unit being checked, or nil.
A hash table mapping a forward-declared name to the references made to
it before its definition was read -- a list of (REFERRER . VAR), one
entry per reference, REFERRER the definition that made it (nil for a
bare top-level expression) and VAR the variable inference handed out.
The references stay unlinked until the batch ends: only the batch's
last form can know whether the definition they wait for was itself
waiting for one, and a scheme is not final until every forward name it
mentioned has been linked too.  See `tl-forward--link'.")

(defvar tl-infer-forward-order nil
  "Definitions of this batch that some earlier form referred forward to.
A list of (ENV . NAME) in registration order, so the most recently
registered definition is first.  That is the reverse definition order
the linking pass wants: a scheme only says everything its own body's
forward references had to say once those names have been linked, and
each of those names was defined later.")

(defvar tl-infer-forward-regen nil
  "Which definitions generalized their scheme, by name.
A hash table mapping a defined name to non-nil when the scheme just
registered was quantified by inference rather than copied from a
signature or fixed monomorphically.  Linking can leave a variable of
the instantiated definition inside the referencing definition's
scheme, and only a scheme that was generalized in the first place may
be generalized again: re-quantifying a value-restricted constant would
undo the restriction that made it monomorphic.")

(defvar tl-infer-defining nil
  "The name of the definition currently being inferred, or nil.
A forward reference made while this is set belongs to that definition,
which is the scheme linking must quantify again once the name the
reference waited for has arrived.")

(defun termlisp--declared-names (form)
  "Return the names FORM declares at the top level, or nil for none.
Only the forms that introduce a name a later form could refer to
matter: `define', both `datatype' spellings, `datatype-extension' and a
`:' signature.  Class declarations are deliberately absent -- a method's
scheme is looked up through `tl-env-method-env' before this point, and
a class never appears in term position for a forward reference to
rescue."
  (when (consp form)
    (cond
     ((eq (car form) 'define)
      (let ((target (cadr form)))
        (cond ((consp target) (and (symbolp (car target)) (list (car target))))
              ((symbolp target) (list target)))))
     ((eq (car form) 'datatype)
      (let* ((rest (cdr form))
             (rest (if (eq (car rest) 'open) (cdr rest) rest))
             (head (car rest)))
        (cons (if (consp head) (car head) head)
              (delq nil (mapcar (lambda (c) (and (consp c) (car c)))
                                (cdr rest))))))
     ((eq (car form) 'datatype-extension)
      (cons (cadr form)
            (mapcar (lambda (c) (and (consp c) (car c))) (cddr form))))
     ((eq (car form) ':)
      (and (symbolp (cadr form)) (list (cadr form))))
     (t nil))))

(defun termlisp-collect-forward-names (forms)
  "Return a hash of every name FORMS declares, merged with any outer set.
Merging matters because a driver that already knows its whole unit --
a file being loaded -- may still hand a multi-form string to
`termlisp-eval'.  Replacing the outer set there would make a legal
forward reference inside the file fail for reasons the string cannot
see."
  (let ((tbl (make-hash-table :test #'eq)))
    (when tl-infer-forward-names
      (maphash (lambda (k v) (puthash k v tbl)) tl-infer-forward-names))
    (dolist (form forms)
      (dolist (name (termlisp--declared-names form))
        (when (symbolp name) (puthash name t tbl))))
    tbl))

(defun termlisp-collect-file-forward-names (file)
  "Return a hash of the names FILE declares, or nil if FILE cannot be read.
FILE may be an ordinary Emacs Lisp file whose top-level forms are
term-lisp declarations wrapped in the `datatype'/`define' macros.  A
file that uses reader syntax the term-lisp reader rejects yields nil
rather than a parse error: guessing at forward references is an
optimization, and refusing to load over it would be the wrong trade."
  (condition-case nil
      (termlisp-collect-forward-names (termlisp-parse-file file))
    (error nil)))

(defun tl-forward--declare (env name generalized)
  "Record NAME's registration in ENV for the batch's linking pass.
GENERALIZED is non-nil when the scheme just registered was quantified
by inference, which is what decides whether linking may quantify the
scheme of a definition that referred to NAME forward (see
`tl-infer-forward-regen').  Nothing is unified here.  A definition that
forward-references another is itself linked when the batch ends, in
reverse registration order, so by the time NAME's earlier uses are
read its scheme already carries what its own body's forward references
had to say."
  (when tl-infer-forward-regen
    (puthash name generalized tl-infer-forward-regen))
  (when (and tl-infer-forward-names
             (gethash name tl-infer-forward-names))
    (push (cons env name) tl-infer-forward-order)))

(defun tl-forward--link ()
  "Unify every pending forward reference with the definition it waited for.
Walks `tl-infer-forward-order' -- newest registration first, so a
scheme is linked only after every name its own body referred forward
to -- and drains each name's entries from `tl-infer-forward-vars'.
Each reference's variable is unified with a fresh instance of the
definition's now-final scheme, and the scheme of the definition that
made the reference is quantified again when `tl-infer-forward-regen'
permits it, because an instance variable of this link now sits inside
it unquantified.  Only structure is linked: the class constraints a
definition carries were closed when the using definition was
registered, and this pass does not revisit them.  A reference that
does not fit its definition signals a `termlisp-type-error' naming the
definition.  A name no form in the batch ever defines keeps its
references unconstrained, exactly as before linking existed."
  (dolist (entry tl-infer-forward-order)
    (let* ((env (car entry))
           (name (cdr entry))
           (pending (and tl-infer-forward-vars
                         (gethash name tl-infer-forward-vars))))
      (when pending
        (remhash name tl-infer-forward-vars)
        (let ((scheme (gethash name (tl-env-type-env env)))
              (tl-occurrence-check (tl-env-option env :occurs-check)))
          (when (tl-tscheme-p scheme)
            (dolist (ref pending)
              (let* ((inst (car (tl-instantiate-scheme scheme)))
                     (u (tl-unify-types (cdr ref) inst nil)))
                (unless (car u)
                  (signal 'termlisp-type-error
                          (list (condition-case nil
                                    (format "Definition of %S does not match its earlier use:\n  the use needs: %s\n  the definition gives: %s"
                                            name
                                            (tl-type-text
                                             (tl-type-to-datum (cdr ref)))
                                            (tl-type-text
                                             (tl-type-to-datum inst)))
                                  (error "Definition of %S does not match its earlier use"
                                         name)))))
                ;; The instance's variables the unification left open
                ;; are now part of the referencing definition's scheme,
                ;; quantified by nothing.  Add only variables from this
                ;; instantiation, and only above the level the
                ;; registration generalized at: whatever the
                ;; registration deliberately left monomorphic stays
                ;; that way, and a scheme copied from a signature is
                ;; the author's quantification and is not touched.
                (let ((rs (and (car ref)
                               (gethash (car ref) (tl-env-type-env env)))))
                  (when (and (tl-tscheme-p rs)
                             (not (gethash (car ref) (tl-env-sig-env env)))
                             tl-infer-forward-regen
                             (gethash (car ref) tl-infer-forward-regen))
                    (let* ((old (tl-tscheme-vars rs))
                           (add (cl-remove-if
                                 (lambda (v)
                                   (or (memq v old)
                                       (let ((l (tl-node-level v)))
                                         (null (and l (> l 1))))))
                                 (tl-free-tvars inst))))
                      (when add
                        (setf (tl-tscheme-vars rs) (append old add))))))))))))))

(defun tl-infer-symbol (env sym)
  "Infer the type of a bare symbol SYM."
  (let ((cell (assq sym (tl-tenv-locals env)))
        (base (tl-tenv-base env)))
    (cond
     ;; Term position only: a `_' in a pattern has always meant "match
     ;; anything, bind nothing", which is a different question answered
     ;; by `tl-infer-pattern' and does not come through here.
     ((eq sym '_) (cons (tl-infer-hole) nil))
     (cell (let ((v (cdr cell)))
             (if (tl-tscheme-p v)
                 (let ((r (tl-instantiate-scheme v)))
                   (dolist (c (cdr r)) (tl-emit-constraint c))
                   (cons (car r) nil))
               (cons v nil))))
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
     ;; A type name in term position.  The README's `(f Void)' passes
     ;; the uninhabited type itself as the argument, so a declared
     ;; datatype is a value here -- and its type is exactly itself, one
     ;; fresh variable per parameter.  Saying so is what keeps `(car
     ;; Bool)' an error: the old unconstrained fallback let any type
     ;; name stand for any argument type at all.
     ((and base (gethash sym (tl-env-datatypes base)))
      (let* ((spec (gethash sym (tl-env-datatypes base)))
             (params (plist-get spec :params)))
        (cons (tl-tcon sym (and params
                                (mapcar (lambda (_p) (tl-fresh-tvar)) params)))
              nil)))
     ;; A name some later form in this unit declares: type it as an
     ;; unconstrained variable, because there is no scheme to read yet.
     ;; The variable is also remembered, so that when the definition
     ;; finally arrives every earlier use can be told what it really
     ;; was -- see `tl-forward--link'.
     ((and tl-infer-forward-names (gethash sym tl-infer-forward-names))
      (let ((v (tl-fresh-tvar)))
        (when tl-infer-forward-vars
          (push (cons tl-infer-defining v)
                (gethash sym tl-infer-forward-vars)))
        (cons v nil)))
     ;; Nothing knows this name.  It used to become a fresh variable,
     ;; which is how `(nosuch 1)' typechecked and then evaluated to a
     ;; stuck form: an unbound head constrains nothing, so every
     ;; argument mismatch downstream was silently accepted too.  A name
     ;; the environment cannot resolve is an error at the point it is
     ;; mentioned, not a promise that later code will supply it.
     (t (signal 'termlisp-type-error
                (list (format "Unknown symbol: %S" sym)))))))

(defun tl-infer-lambda (env params body)
  "Infer `(lambda PARAMS BODY)'."
  ;; A lambda is a function body, so it opens a generalization scope:
  ;; the parameters introduced here are generalizable by a `let' in the
  ;; body, and by nothing further out.
  (let ((ptypes nil)
        (pbinds nil)
        (tl-current-level (1+ tl-current-level)))
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

(defun tl-expr-term--global-p (env name)
  "Return non-nil when NAME denotes something at the type level in ENV.
Local bindings are excluded by the caller: a local named `g' read here
would come back as a global `g' of the same spelling, and a type that
then reduced through the wrong one would compare equal to the wrong
type.  Everything else that a bare name can mean -- a defined function,
a method, a constructor, a declared datatype, a builtin -- is a term
the type level may name."
  (let ((base (tl-tenv-base env)))
    (and base
         (or (gethash name (tl-env-type-env base))
             (gethash name (tl-env-method-env base))
             (gethash name (tl-env-constructors base))
             (gethash name (tl-env-datatypes base))
             (gethash name tl-builtin-types)))))

(defun tl-expr-term (env expr)
  "Return the type-level term node the call-site expression EXPR denotes.
A `Pi' binder in a callee's type stands for its argument's *value*, and
at the call site that value is in hand -- it is EXPR.  Writing it here is
what turns `(?13 ?6)', a fresh variable nothing would ever tie back,
into `(zc ?6)', the spelling the signature already had.  Before this the
binder's occurrences were all bound to `tl-fresh-tvar', so a result type
such as `Eq b (f x) (f y)' kept an unsolved head and only agreed with its
signature when a later unification happened to name the function -- which
is why `cong Succ' worked and `cong zc' did not.

A name whose type-level reading would be the wrong name -- a local, or an
argument with no head to write such as a literal or a `lambda' -- answers
nil, and the caller keeps the old fresh variable there.  That is a
degradation to the behaviour every argument had before this function
existed, not a new failure."
  (cond
   ((symbolp expr)
    (and (not (assq expr (tl-tenv-locals env)))
         (tl-expr-term--global-p env expr)
         (tl-tcon expr nil)))
   ((and (consp expr) (symbolp (car expr))
         (not (memq (car expr) '(lambda do let list quote)))
         (tl-expr-term--global-p env (car expr)))
    ;; An argument with no type-level spelling of its own -- a local, a
    ;; literal -- becomes a fresh variable rather than voiding the whole
    ;; term, which is the same choice `tl-clause--pattern-term' makes for
    ;; a subpattern that denotes nothing: part of a term still tells the
    ;; caller more than none of it.
    (tl-tcon (car expr)
             (mapcar (lambda (a) (or (tl-expr-term env a)
                                     (tl-fresh-tvar)))
                     (cdr expr))))
   (t nil)))

(defun tl-apply-pi (ftype &optional term)
  "Spell FTYPE as an ordinary arrow when it is a `Pi' about to be applied.
The codomain's occurrences of its binder become one fresh variable,
unless TERM -- the argument this Pi is being applied to, as a type-level
term from `tl-expr-term' -- says what the binder was, in which case they
become TERM instead.  The binder stood for the argument's value, and the
call site has it; leaving it to unification to rediscover was a
description of a gap, not a reason for one.

A plain `->' comes back untouched, and so does a type with no argument
left to consume."
  (if (and (tl-node-p ftype) (tl-node-application ftype)
           (eq (tl-node-head ftype) 'Pi)
           (= (length (tl-node-children ftype)) 3))
      (let ((args (tl-node-children ftype)))
        (tl-tarrow (cadr args)
                   (tl-type-subst (caddr args)
                                  (list (cons (car args)
                                              (or term (tl-fresh-tvar)))))))
    ftype))

(defun tl-infer-application (env expr)
  "Infer a function application EXPR = (F A1 ... AN)."
  (let* ((head (car expr))
         (args (cdr expr))
         (base (tl-tenv-base env))
         (msc (and (symbolp head) (tl-method-scheme-for env head)))
         ;; A *local* binding whose scheme carries class constraints (a
         ;; generalized `let'): also a dictionary-passing site.
         (lsc (and (null msc) (symbolp head)
                   (let ((v (cdr (assq head (tl-tenv-locals env)))))
                     (and (tl-tscheme-p v) (tl-tscheme-constraints v) v))))
         ;; A call to a program function whose scheme carries class
         ;; constraints: it is a dictionary-passing site.
         (hsc (and (null msc) (null lsc) (symbolp head) base
                   (not (assq head (tl-tenv-locals env)))
                   (gethash head (tl-env-type-env base))))
         (rh (cond
              (msc
               (let ((r (tl-instantiate-scheme msc)))
                 (dolist (c (cdr r))
                   (tl-emit-constraint c)
                   (when tl-elab-active (push (cons expr c) tl-elab-sites)))
                 (cons (car r) nil)))
              (lsc
               (let ((r (tl-instantiate-scheme lsc)))
                 (dolist (c (cdr r)) (tl-emit-constraint c))
                 (when tl-elab-active (push (cons expr (cdr r)) tl-elab-fn-sites))
                 (cons (car r) nil)))
              ((and (tl-tscheme-p hsc) (tl-tscheme-constraints hsc))
               (let ((r (tl-instantiate-scheme hsc)))
                 (dolist (c (cdr r)) (tl-emit-constraint c))
                 (when tl-elab-active (push (cons expr (cdr r)) tl-elab-fn-sites))
                 (cons (car r) nil)))
              (t (tl-infer env head))))
         (ftype (car rh))
         (bindings (cdr rh)))
    (dolist (arg args)
      (let* ((ra (tl-infer (tl-zonk-env env bindings) arg))
             (aty (car ra))
             (res (tl-fresh-tvar)))
        (setq bindings (tl-compose-bindings bindings (cdr ra)))
        (setq ftype (tl-apply-pi (tl-apply-bindings ftype bindings)
                                 (tl-expr-term env arg)))
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
   ((and (consp pat) (eq (car pat) :dot))
    ;; Checked exactly as a literal is -- the term has a type and that
    ;; type must be the type of the position -- but for the opposite
    ;; reason.  A literal is checked because its value was written and
    ;; may not fit; a dot is checked because the value was *asserted*,
    ;; and the assertion is a claim about the argument.  Both reduce to
    ;; one unification.  The term is inferred in the definition's scope,
    ;; so a name only this pattern introduces is not available here, and
    ;; says so as an unknown symbol rather than as a mismatch.
    (let* ((r (tl-infer env (cadr pat)))
           (bs (cdr r))
           (u (tl-unify-types (tl-apply-bindings (car r) bs) expected bs)))
      (unless (car u)
        (signal 'termlisp-type-error
                (list (format "Dot pattern %S mismatches" pat))))
      (cons nil (cdr u))))
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

(defun tl-type-text (datum)
  "Print DATUM as text, leaving a `?N' variable name readable.
`format' with `%S' escapes a symbol named `?3' as `\\?3', because a
bare one would read back as a character constant.  In an error message
that escape is noise twice over: the message is read, not read in."
  (cond ((consp datum)
         (concat "(" (mapconcat #'tl-type-text datum " ") ")"))
        ((null datum) "nil")
        ((symbolp datum) (symbol-name datum))
        (t (format "%s" datum))))

(defun tl-type-mismatch-note (target got)
  "A note naming the two types TARGET and GOT that failed to agree.
A proof that fails has to say where, or the reader is left bisecting:
`Eq Nat Zero (Succ Zero)' and `Eq Nat (Succ Zero) Zero' agree everywhere
but one index, and naming that difference is most of what fixing the
proof needs.  TARGET may be nil, where only GOT is known.  Rendering is
best-effort: an unreadable type is not worth losing the error over."
  (condition-case nil
      (concat (when target
                (format "\n  the signature says: %s"
                        (tl-type-text (tl-type-to-datum target))))
              (format "\n  this clause gives:  %s"
                      (tl-type-text (tl-type-to-datum got))))
    (error "")))

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

(defun tl-clause--pattern-term (env pattern)
  "The term node PATTERN denotes in ENV, or nil when it denotes nothing to put.
A variable pattern matches without saying what the argument was, so it
contributes nothing and the codomain keeps the binder it already had --
a name nothing in a type can reduce, so leaving it alone costs nothing.
A constructor pattern says exactly what the argument was, and only that
lets the codomain reduce: `(lenV (vapp xs ys))' over the pattern `VNil'
is `(lenV (vapp VNil ys))', which is `lenV ys', and without it the base
case of that theorem has nothing to prove.  A constructor is told from a
variable the same way `tl-infer-pattern' tells them, because a pattern
is only an answer to that question.  A dot pattern is a constructor
pattern that was written as a term, so it is read as one -- the dotted
term is asked what it denotes and the answer is used as it would have
been had the term been spelt as a pattern.  A dotted variable still
denotes nothing, which is the honest answer: `(dot k)' pins the
argument to a value the checker cannot enumerate and cannot reduce
either, and pretending otherwise would let a codomain reduce to
something the match never guaranteed."
  (cond
   ((or (eq pattern '_) (eq pattern nil)) nil)
   ((symbolp pattern)
    (and (tl-constructor-name-p env pattern) (tl-tcon pattern nil)))
   ((and (consp pattern) (eq (car pattern) :dot))
    (tl-clause--pattern-term env (cadr pattern)))
   ((and (consp pattern) (eq (car pattern) :literal))
    (tl-tcon (cadr pattern) nil))
   ((and (consp pattern) (symbolp (car pattern))
         (tl-constructor-name-p env (car pattern)))
    (tl-tcon (tl-type-head (car pattern))
             (mapcar (lambda (p) (or (tl-clause--pattern-term env p)
                                     (tl-fresh-tvar)))
                     (cdr pattern))))
   (t nil)))

(defun tl-clause--skolem (binder)
  "Return a rigid constant standing for BINDER's universally quantified value.
A signature says \"for every x\", and the body of one clause cannot say
which x it meant, so while the clause is checked x has to be something
that may equal only itself.  Left a *variable* it would be solved to
whatever the body turned out to need, and
`(: f (-> (x : Nat) (Eq Nat x (Succ x))))' would be inhabited by `Refl'
-- the same constant `tl-infer-constant' already checks a plain
definition against.  A constant still lets the body's own fresh
variables be *told* what it is, `?z' binding to it, so the true case
`(: w (-> (x : Nat) (Eq Nat x x)))' comes out right and the two
occurrences then have to agree or the clause is refused.

The name carries the binder's so a refusal can say which one it was."
  (tl-tcon (gensym (format "%s/" (tl-node-head binder))) nil))

(defun tl-clause--peel-pis (env target params)
  "Replace TARGET's leading Pis with arrows, one per PARAMS, in order.
A definition's clauses infer plain arrows, never Pis, so the two shapes
have to agree before anything can be unified -- but simply dropping the
Pi would strand the codomain's occurrences of its binder on a name no
longer there.  So each binder is first replaced by what that clause's
pattern says the argument was in ENV, which is also what lets the codomain
reduce: over `VNil', `(lenV (vapp xs ys))' becomes `(lenV (vapp VNil
ys))' and thence `lenV ys', and the base case of `lenAppend' comes out
as `Eq Nat (lenV ys) (lenV ys)', which `Refl' inhabits.

A pattern that says nothing -- a variable, or `_ -- leaves the binder
where it was, and that binder is replaced by `tl-clause--skolem' instead
of left alone.  It came here instantiated as an ordinary variable, which
is the right thing at a call site and the wrong thing here: this is the
one place the signature is being *read back*, and a variable it can be
solved to is a signature that any body may satisfy.

A parameter that runs out of Pis keeps whatever shape TARGET had left,
and a TARGET that runs out of parameters is left whole, so neither
mismatch in count is an error here -- `tl-unify-types' reports it, with
the two types printed, which is more useful than a complaint about
arity."
  (let ((cur target) (ps params) (domains nil))
    (while (and ps (tl-node-p cur) (tl-node-application cur)
                (eq (tl-node-head cur) 'Pi))
      (let* ((args (tl-node-children cur))
             (binder (car args))
             (dom (cadr args))
             (cod (caddr args))
             (val (tl-clause--pattern-term env (car ps))))
        (setq cur (tl-type-subst
                   cod (list (cons binder (or val (tl-clause--skolem binder)))))
              ps (cdr ps))
        (push dom domains)))
    ;; Pis left over after the patterns ran out are still universally
    ;; quantified, and get the same treatment for the same reason: with
    ;; a fresh variable there, a body that ignores the argument would
    ;; have the whole rest of the statement to solve it against.
    (while (and (tl-node-p cur) (tl-node-application cur)
                (eq (tl-node-head cur) 'Pi))
      (let ((args (tl-node-children cur)))
        (setq cur (tl-tarrow
                   (cadr args)
                   (tl-type-subst (caddr args)
                                  (list (cons (car args)
                                              (tl-clause--skolem
                                               (car args)))))))))
    (dolist (d domains)
      (setq cur (tl-tarrow d cur)))
    cur))

(defun tl-infer-define-clauses (env name clauses)
  "Infer NAME from CLAUSES (list of `(PARAMS . BODY)'); register a scheme."
  (let* ((placeholder (tl-fresh-tvar))
         (tl-infer-constraints nil)
         (tyenv (tl-env-type-env env))
         (sig (and (gethash name (tl-env-sig-env env))
                   (gethash name tyenv))))
    ;; With a signature, the function's own name means that signature
    ;; while its clauses are being read, so a recursive call is free to
    ;; instantiate it afresh.  A bare placeholder would have been pinned
    ;; by whichever clause ran first, handing every later clause -- and
    ;; every recursive call inside one -- the index that clause fixed.
    (puthash name (or sig (tl-tscheme nil placeholder)) tyenv)
    (let ((bindings nil))
      (if (catch 'tl-clause-inconsistent
            (dolist (clause clauses)
              (let* ((tl-current-level (1+ tl-current-level))
                     (params (car clause))
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
                    ;; Each clause is checked against its own instance of
                    ;; the signature, not against one type shared by all
                    ;; of them: a pattern match on an indexed family
                    ;; refines the index, so the clauses of `append' have
                    ;; types that share no unifier at all -- `VNil' pins
                    ;; the index to `Zero' and `(VCons x xs)' to one past
                    ;; its tail's.  This is the direction that makes the
                    ;; elaboration bidirectional: with a signature the
                    ;; clause is *checked* against it, and only in the
                    ;; signature's absence is its type inferred.
                    (let* ((target (tl-clause--peel-pis
                                    env
                                    (if sig (car (tl-instantiate-scheme sig))
                                      placeholder)
                                    params))
                           (u (tl-unify-types target ctype bindings)))
                      (unless (car u)
                        (if (or tl-type-lenient tl-type-lenient-clauses)
                            (throw 'tl-clause-inconsistent t)
                          (signal 'termlisp-type-error
                                  (list (format "Clause of %s%s%s"
                                                name
                                                (if sig
                                                    " does not match its signature"
                                                  " has inconsistent type")
                                                (tl-type-mismatch-note
                                                 (and sig target) ctype))))))
                      (setq bindings (cdr u)))))))
            nil)
          (puthash name (tl-tscheme nil (tl-fresh-tvar)) tyenv)
        (let ((final (tl-apply-bindings placeholder bindings)))
          ;; The definition's own placeholder is now bound to its type, so
          ;; it must not count as an ambient variable (which would stop
          ;; generalization of the very variables it mentions).
          (remhash name tyenv)
          (let* ((gen-vars (tl-generalized-vars final)))
            (if sig
                ;; Every clause has already been checked against its own
                ;; instance of the signature, which is the check that
                ;; counts, so nothing is left to unify here: what remains
                ;; is to close the constraints and put the signature back
                ;; where callers look for it.  The clauses cannot be
                ;; cross-checked against one shared type either -- that is
                ;; exactly what an indexed family forbids.
                (progn
                  (setq tl-elab-bindings bindings)
                  (tl-close-constraints env nil tl-infer-constraints bindings)
                  (puthash name sig tyenv)
                  (tl-forward--declare env name nil))
              (setq tl-elab-bindings bindings)
              (when (fboundp 'tl-kind-check)
                (tl-kind-check env final))
              (let* ((kept (tl-close-constraints env gen-vars tl-infer-constraints bindings))
                     (sc (tl-generalize final kept)))
                (puthash name sc tyenv)
                (tl-forward--declare env name t)))))))))

(defun tl-syntactic-value-p (expr)
  "Return non-nil if EXPR is a syntactic value (value restriction)."
  (or (atom expr)
      (and (consp expr) (eq (car expr) 'lambda))))

(defun tl-infer-constant (env name expr)
  "Infer a constant binding NAME = EXPR."
  (let* ((tl-infer-constraints nil)
         (r (tl-infer (cons nil env) expr)))
    (let* ((ty (tl-apply-bindings (car r) (cdr r)))
           (bindings (cdr r)))
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
            (tl-forward--declare env name nil)
            ty)
        (if (tl-syntactic-value-p expr)
            (let* ((gen-vars (tl-generalized-vars ty))
                   (kept (tl-close-constraints env gen-vars tl-infer-constraints bindings)))
              (puthash name (tl-generalize ty kept) (tl-env-type-env env))
              (tl-forward--declare env name t))
          (tl-close-constraints env nil tl-infer-constraints bindings)
          (puthash name (tl-tscheme nil ty) (tl-env-type-env env))
          (tl-forward--declare env name nil))
        ty))))

(defun tl-type--argument-domains (type)
  "Every argument domain TYPE exposes, outermost first.
Walks the chain of `Pi' and `->' nodes and stops at the first thing that
is neither, so it sees the arguments that survive as arguments whether
or not the binder above each one was named.  A domain this pass drops is
no longer there to constrain anything, which is why a binder is judged
against the domains after it rather than against all of them."
  (let ((acc nil) (cur type))
    (while (and (tl-node-p cur) (tl-node-application cur)
                (memq (tl-node-head cur) '(Pi ->)))
      (let ((args (tl-node-children cur)))
        (push (if (eq (tl-node-head cur) 'Pi) (cadr args) (car args)) acc)
        (setq cur (car (last args)))))
    (nreverse acc)))

(defun tl-type--mentions-p (name domains)
  "Non-nil when the variable NAME is free in any of DOMAINS."
  (cl-some (lambda (d) (memq name (tl-free-tvars d))) domains))

(defun tl-signature-binders (type)
  "Settle TYPE's leading dependent binders as argument, implicit or kept.
Each leading `(NAME : DOMAIN) ->' binder is decided by two questions:
does the codomain still mention NAME, and can anything after it fix the
value down?

Mentioned and fixed -- `(n m : Nat) -> Vec a n -> Vec a m ->
Vec a (plus n m)' -- the caller need pass nothing: the vectors say as
much as `n' and `m' would, so the Pi is dropped and NAME is left for
unification to find.  That is what makes `append' a two-argument
function instead of a four-argument one, and it is what this pass did
for every mentioned binder until a proof by induction said the rule was
too coarse.

Mentioned and *not* fixed -- `(xs : Vec a n) -> (ys : Vec a m) ->
Eq Nat (lenV (vapp xs ys)) (plus (lenV xs) (lenV ys))' -- nothing
after the binder constrains it, so there is nothing for the call site
to find and nothing for it to pass either, unless the Pi stays.  It
stays.  This is the one case a plain arrow cannot serve: dropping the
Pi would strand every occurrence of NAME in the codomain on a binder no
longer there.  Keeping it is what makes `lenAppend' take the two
vectors it is a statement about.

Unmentioned -- `(n : Nat) -> Nat' -- the name says nothing the type can
use, so it is an ordinary argument, spelled as the plain arrow it always
was.  Nothing is lost in dropping the Pi, because nothing ever referred
to the name.

Decisions run outermost inward, so by the time a binder is reached every
domain after it is already settled: dropping a Pi takes its domain away
with it, and a domain no longer there constrains nothing.

A kept Pi is quantified like any other free variable, so each
instantiation gets a binder of its own and a call site sees the codomain
said about an unknown value -- which is exactly what happens to an
implicit parameter, and for the same reason: the value is the caller's
context to supply.

Keeping one Pi says nothing about the binders behind it, so the walk
goes on: `(n : Nat) -> (x : Nat) -> (xs : Vec a n) -> Vec a n ->
Eq a x x' settles `n' and `x', and then finds `xs' fixed by the vectors
after all.  Stopping at the first explicit binder would have left `xs'
an argument the caller has to pass, for no reason the type gave."
  (let ((cur type) (wrap nil))
    (while (and (tl-node-p cur) (tl-node-application cur)
                (eq (tl-node-head cur) 'Pi))
      (let* ((args (tl-node-children cur))
             (binder (car args))
             (dom (cadr args))
             (cod (caddr args)))
        (cond
         ((not (memq binder (tl-free-tvars cod)))
          (push dom wrap)
          (setq cur cod))
         ((tl-type--mentions-p binder (tl-type--argument-domains cod))
          ;; Re-spelled rather than deleted outright: the occurrences
          ;; are shared nodes, and an ordinary variable is what
          ;; unification is willing to solve -- leaving it rigid would
          ;; keep the very rigidity that made it useless.
          (setq cur (tl-type-subst cod (list (cons binder (tl-fresh-tvar))))))
         (t
          (push (cons binder dom) wrap)
          (setq cur cod)))))
    ;; Fold what the walk recorded back over whatever it stopped on,
    ;; innermost first -- `push' has them innermost first.  A bare domain
    ;; came back as a plain arrow, a kept Pi as the Pi it was.
    (dolist (w wrap)
      (setq cur (if (tl-node-p w)
                    (tl-tarrow w cur)
                  (tl-tcon 'Pi (list (car w) (cdr w) cur)))))
    cur))

(defun tl-register-signature (env form)
  "Register a `(: NAME TYPE)' signature in ENV.
Leading binders whose name the type goes on to mention become implicit
parameters (see `tl-signature-binders'), which is what lets
`(n m : Nat) -> Vec a n -> Vec a m -> Vec a (plus n m)' be written
without the caller ever passing `n' or `m'."
  (let* ((name (cadr form))
         (ty (tl-signature-binders (tl-type-parse (caddr form))))
         (sc (tl-tscheme (tl-free-tvars ty) ty)))
    (when (fboundp 'tl-kind-check-scheme)
      (tl-kind-check-scheme env sc))
    (puthash name sc (tl-env-type-env env))
    (puthash name t (tl-env-sig-env env))
    (tl-forward--declare env name nil)
    name))

(defun tl-typecheck-define (env form)
  "Typecheck a `define' FORM, registering it in ENV.
A definition whose name is a class method is skipped: its signature
comes from the class declaration (registered in `tl-env-method-env'),
and instance implementations are checked against that signature."
  (let* ((target (cadr form))
         (tl-occurrence-check (tl-env-option env :occurs-check))
         (tl-infer-defining (if (consp target) (car target) target)))
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
        (prog1 (tl-infer-define-clauses env name clauses)
          ;; Announce the definition for a coverage check, if one was
          ;; asked for.  Reading the type back out of the environment
          ;; rather than passing it along means what gets announced is
          ;; what every other caller sees: the signature's scheme when
          ;; there was one, and the inferred one otherwise.  The check
          ;; itself waits until the batch ends, because a function's
          ;; clauses may be spread over several forms.
          (when (tl-env-option env :coverage)
            (let ((sc (gethash name (tl-env-type-env env))))
              (when sc
                (push (list env name (tl-tscheme-type sc))
                      tl-coverage-announcements)))))))
     (t (tl-infer-constant env target (caddr form))))))

(defun tl-class-parse-fundep (fd pindex)
  "Parse one fundep FD = `(A... -> B...)' of parameter names.
Return `(FROM-POSITIONS . TO-POSITIONS)' as indices into the parameters."
  (let ((from nil) (to nil) (arrow nil))
    (dolist (x fd)
      (if (eq x '->)
          (setq arrow t)
        (if arrow (push x to) (push x from))))
    (cons (mapcar (lambda (p) (cdr (assq p pindex))) (nreverse from))
          (mapcar (lambda (p) (cdr (assq p pindex))) (nreverse to)))))

(defun tl-register-class (env form)
  "Register `(class NAME (PARAM...) SUPERS METHOD-DECL... [FUNDEPS])' in ENV.
A parameter may carry its kind: `(f : (-> * *))' pins what the class's
instances must be, which is the whole content of `Functor : (* -> *) ->
*'.  A bare parameter keeps meaning what it always meant -- a type
nothing has pinned, each use and each instance deciding for itself.
FUNDEPS, when present, is `(fundeps (A... -> B...)...)' of parameter names."
  (let* ((name (nth 1 form))
         (declared (nth 2 form))
         (params (mapcar (lambda (p) (if (consp p) (car p) p)) declared))
         (kind-sexps
          (let ((acc nil))
            (dolist (p declared)
              (cond
               ((and (consp p) (eq (cadr p) ':) (= (length p) 3))
                (push (cons (car p) (caddr p)) acc))
               ((consp p)
                (signal 'termlisp-error
                        (list (format "Malformed parameter %S in class %S; write it as (NAME : KIND)"
                                      p name))))))
            (nreverse acc)))
         (super-forms (nth 3 form))
         (rest (nthcdr 4 form))
         (fundep-form (and (consp (car (last rest)))
                           (eq (caar (last rest)) 'fundeps)
                           (car (last rest))))
         (method-decls (if fundep-form (butlast rest) rest))
         (pindex (cl-loop for p in params for i from 0 collect (cons p i)))
         (parse-vars (cl-loop for p in params collect (cons p (tl-fresh-tvar))))
         (first-var (cdr (car parse-vars)))
         ;; An annotation is read against the parameters' own names and
         ;; kept under them, so an instance head is later measured
         ;; against the kind its class declared.
         (kind-annos
          (and kind-sexps (fboundp 'tl-kind-parse)
               (mapcar (lambda (cell)
                         (cons (car cell) (tl-kind-parse (cdr cell) params)))
                       kind-sexps)))
         (fundeps (mapcar (lambda (fd) (tl-class-parse-fundep fd pindex))
                          (cdr fundep-form)))
         (methods nil)
         (supers nil))
    (dolist (sf super-forms)
      (let ((tl-type-parse-vars parse-vars))
        (push (tl-constraint (car sf) (tl-type-parse* (cadr sf))) supers)))
    (setq supers (nreverse supers))
    (dolist (md method-decls)
      (let* ((mname (car md))
             (tl-type-parse-vars parse-vars)
             (ty (tl-type-parse* (cadr md))))
        (push (cons mname
                    (tl-tscheme (tl-free-tvars ty)
                                ty
                                (list (tl-constraint name first-var))))
              methods)))
    (setq methods (nreverse methods))
    (puthash name (tl-cclass name params supers methods fundeps kind-annos)
             (tl-env-class-env env))
    (dolist (m methods)
      (puthash (car m) (cdr m) (tl-env-method-env env)))
    name))

(defun tl-register-instance (env form)
  "Register `(instance (CLASS TYPE) [CONTEXT] DICT)' in ENV.
CONTEXT, when present, is a list of `(CLASS TYPE)' predicates the instance
requires; DICT is then a constructor applied to one sub-dictionary per
context predicate.  Without a context DICT is the runtime dictionary value
the elaborator inserts as the first argument of overloaded method calls.
When the class pinned its parameter's kind, TYPE is measured against it
here; see `tl-register-class'."
  (let* ((head (nth 1 form))
         (cname (car head))
         (rest (nthcdr 2 form))
         (ctx-forms (and (consp (car rest)) (car rest)))
         (dict (if ctx-forms (cadr rest) (car rest)))
         (tl-type-parse-vars nil)
         (ty (tl-type-parse* (cadr head)))
         (context (mapcar (lambda (cf)
                            (tl-constraint (car cf) (tl-type-parse* (cadr cf))))
                          ctx-forms))
         (inst (tl-instance cname ty context nil dict)))
    ;; A class that pinned its parameter's kind refuses an instance at
    ;; any other, here at the declaration rather than at the first
    ;; method call that cannot resolve.  A class that pinned nothing
    ;; keeps deciding per instance, as it always has.
    (let* ((cls (gethash cname (tl-env-class-env env)))
           (want (and cls
                      (cdr (assq (car (tl-cclass-params cls))
                                 (tl-cclass-kinds cls))))))
      (when (and want (fboundp 'tl-kind-infer))
        (let* ((expected (tl-kind-freshen want))
               (offered (tl-kind-whnf (tl-kind-infer env ty))))
          (unless (tl-kind-unify expected offered)
            (signal 'termlisp-type-error
                    (list (format "Kind error: instance of %S is at a %s where a %s is required"
                                  cname
                                  (tl-kind->string offered)
                                  (tl-kind->string expected))))))))
    (puthash cname (append (gethash cname (tl-env-instance-env env)) (list inst))
             (tl-env-instance-env env))
    cname))

(defun tl-typecheck-form (env form)
  "Typecheck one top-level FORM in ENV."
  (let ((tl-infer-constraints nil)
        (tl-occurrence-check (tl-env-option env :occurs-check))
        ;; Oracle mode tolerates a failed unification and clauses that
        ;; share no common type; a proof may tolerate neither, since both
        ;; turn a mistake into an unconstrained variable instead of an
        ;; error.  Nothing on this path sets either flag today -- the only
        ;; binder is `tl-typecheck-ir', which no evaluator, loader or REPL
        ;; entry point reaches -- but a guarantee that rests on nobody
        ;; happening to set a variable is not a guarantee.  Binding them
        ;; here makes the typed path strict by construction, so a caller
        ;; that later does reach the oracle cannot quietly widen what a
        ;; proof is allowed to contain.
        (tl-type-lenient nil)
        (tl-type-lenient-clauses nil))
    (cond
     ;; A rewrite is checked first and only then read as the `define' it
     ;; means, so a refusal leaves `tl-env-clauses' untouched: the
     ;; checker must not be the half of the system that believes a
     ;; clause the evaluator refused to add.
     ((and (consp form) (eq (car form) 'rewrite))
      (tl-typecheck-define env (tl-rewrite-desugar env form)))
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
  (let* ((forms (termlisp-parse string))
         (tl-infer-forward-names (termlisp-collect-forward-names forms))
         (tl-infer-forward-vars (or tl-infer-forward-vars
                                    (make-hash-table :test #'eq)))
         (tl-infer-forward-order nil)
         (tl-infer-forward-regen (or tl-infer-forward-regen
                                     (make-hash-table :test #'eq)))
         ;; Type-level reduction runs against this env, so that a
         ;; signature's `plus n m' can unfold while its type is being
         ;; compared with another.  `termlisp-eval-form' has always
         ;; bound this; without it here this driver rejected every
         ;; definition whose result index was a computed one -- `append'
         ;; is written in exactly that style -- while the evaluator
         ;; accepted it.
         (tl-nbe-reduce-env env))
    (dolist (form forms env)
      (tl-typecheck-form env form))
    ;; Every form has been read, so a forward name has all its clauses:
    ;; the uses made of it before its definition arrived can be told
    ;; what it really was.
    (tl-forward--link)
    ;; STRING is one batch, so this is the first moment every definition
    ;; in it has all of its clauses and a coverage check can mean
    ;; anything.  A form that fails leaves nothing queued: the driver
    ;; clears the queue before the check runs.
    (tl-run-post-batch)
    ;; The driver's own verdict lives in whether it signaled; what it
    ;; hands back is the environment it checked into, which is what
    ;; `termlisp-typecheck' promises in turn.  The coverage hook above
    ;; may return anything at all, so without this the batch driver
    ;; would pass the hook's leftovers on as its result.
    env))

(defun termlisp-typecheck (string &optional env)
  "Typecheck STRING in ENV (fresh if nil).  Return ENV; signal on error."
  (let ((env (or env (termlisp-make-env))))
    (termlisp-typecheck-def env string)))

(defun termlisp-typecheck-file (file &optional env)
  "Typecheck the contents of FILE in ENV."
  (termlisp-typecheck
   (with-temp-buffer (insert-file-contents file) (buffer-string))
   env))

;;; Type preservation of rewrite rules.
;;; A rule LHS -> RHS preserves types when every redex it matches at a
;;; type T rewrites to a reduct at that same T.  Both sides are typed
;;; as terms with the pattern variables bound -- the left side first,
;;; then everything the left side left open is frozen into a rigid
;;; constant before the right side is read.  Freezing is what makes the
;;; question the right one: the rule has to hold at every instantiation
;;; the match admits, and a variable the right side was still free to
;;; solve would only record the one instantiation it liked.  Three
;;; verdicts come out, `preserved', `violated', `cannot-check', and
;;; only the first says the rule is safe: anything that cannot be read
;;; is reported as what it is, never as silence.

(defun tl-preserve-check (env rule)
  "Decide whether RULE preserves the types of the terms it rewrites.
ENV is a type environment -- a `tl-env', or the local/base pair
`tl-tenv-extend' builds -- giving every name in RULE its scheme.  RULE
is a `tl-grule', plain or clause-based.  Return (VERDICT . REASON)
where VERDICT is one of the symbols `preserved', `violated', and
`cannot-check', and REASON is a string saying why the verdict is what
it is (nil when preserved).  Type-level reduction runs against ENV
while the two sides are compared, so `plus Zero m' and `m' are one
index rather than two.  A guard is not read: guarding only makes
a rule apply less often, and fewer redexes cannot undo what the
unguarded rule already preserves."
  (let ((clauses (or (tl-grule-clauses rule)
                     (and (tl-grule-pattern rule)
                          (list (cons (tl-grule-pattern rule)
                                      (tl-grule-template rule)))))))
    (if (null clauses)
        (cons 'cannot-check "the rule has no pattern to match with")
      (let ((verdict 'preserved)
            (reason nil)
            ;; Both sides are typed with ENV's type-level reduction in
            ;; reach -- the binding the batch driver and the evaluator
            ;; already put around their own comparisons -- because the
            ;; verdict must not depend on who asked.  Left unbound, the
            ;; comparison is structural, and a rule whose codomain
            ;; computes its result index comes back violated for
            ;; returning exactly what it promises while every path that
            ;; checks a program accepts it.
            (tl-nbe-reduce-env env))
        (dolist (clause clauses)
          (let* ((pat (car clause))
                 (side (if (tl-grule-clauses rule)
                           (tl-preserve--pat-side pat)
                         (tl-preserve--graph-side pat)))
                 (v (if (eq side :unsupported)
                        (cons 'cannot-check
                              (format "pattern %S has no term reading" pat))
                      (let* ((vars (delete-dups (cdr side)))
                             (ident (mapcar
                                     (lambda (v)
                                       (cons v (tl-make-node v nil nil)))
                                     vars))
                             (term (tl-preserve--template-term
                                    (cdr clause) ident)))
                        (if (eq term :unsupported)
                            (cons 'cannot-check
                                  (format "the template of %S cannot be read as a term"
                                          pat))
                          (tl-preserve--pair env (car side) term vars))))))
            (pcase (car v)
              ('violated
               (unless (eq verdict 'violated)
                 (setq verdict 'violated reason (cdr v))))
              ('cannot-check
               (when (eq verdict 'preserved)
                 (setq verdict 'cannot-check reason (cdr v)))))))
        (cons verdict reason)))))

(defun tl-preserve--pat-side (pat)
  "Read compiled pattern PAT as a term, collecting its variables.
Return (TERM . VARS), where every pattern variable is also a term
variable, or `:unsupported' when PAT says how to match but not what
the matched thing is: a rest binds a sequence, an as-pattern renames
one, a list pattern matches a spelling no term has."
  (pcase pat
    (`(pvar ,name) (cons name (list name)))
    (`(pwild) (cons '_ nil))
    (`(plit ,value) (cons value nil))
    ;; A lone list subpattern is matched against the whole child list,
    ;; so this is the application (HEAD) with no children, not HEAD
    ;; applied to something spelled pnil.
    (`(pcon ,head (pnil)) (cons (list head) nil))
    (`(pcon ,head) (cons head nil))
    (`(pcon ,head . ,subs)
     (let ((terms nil) (vars nil) (ok t))
       (dolist (s subs)
         (let ((r (tl-preserve--pat-side s)))
           (if (eq r :unsupported)
               (setq ok nil)
             (push (car r) terms)
             (setq vars (append vars (cdr r))))))
       (if ok
           (cons (cons head (nreverse terms)) vars)
         :unsupported)))
    (_ :unsupported)))

(defun tl-preserve--graph-side (pattern)
  "Read graph PATTERN as a term, collecting its pattern variables.
Return (PATTERN . VARS), the pattern being its own term reading, or
`:unsupported' when PATTERN asks for something a term cannot say --
a `:rest' element binds the remaining nodes as a sequence, and a
sequence is not one thing a type could be the type of."
  (let ((vars nil) (ok t))
    (cl-labels ((walk (p)
                  (cond
                   ((tl-graph--pvar-p p) (push p vars))
                   ((consp p)
                    (if (or (tl-graph--rest-p p) (tl-graph--splice-p p))
                        (setq ok nil)
                      (dolist (x p) (walk x)))))))
      (walk pattern))
    (if ok
        (cons pattern (nreverse vars))
      :unsupported)))

(defun tl-preserve--template-term (template ident)
  "Render TEMPLATE as the term it instantiates to under IDENT.
IDENT maps each pattern variable to a leaf of the same name, the
identity substitution, so the template rebuilds itself with its
variables left standing and reading that back gives the term to type.
This is what lets a closure template -- the body of the clause the
rule was compiled from -- be checked at all: substituting every name
for itself changes nothing, and the body comes back.  Return the term,
or `:unsupported' when the template cannot be read: a function that
signals, a splice with no list to splice, a variable the pattern never
bound."
  (condition-case nil
      (tl-node->sexp (tl-graph-instantiate template ident))
    (error :unsupported)))

(defun tl-preserve--infer (env term)
  "Infer the type of TERM in ENV as (TYPE), or as (nil MESSAGE).
MESSAGE carries the failure, whatever class it was: a mismatch is the
interesting one, and an unreadable name is told apart from it by
`tl-preserve--unknown-names', which asks the environment directly."
  (condition-case e
      (list (car (tl-infer env term)))
    (termlisp-type-error
     (list nil (if (stringp (cadr e)) (cadr e) (error-message-string e))))
    (error (list nil (error-message-string e)))))

(defun tl-preserve--skolemize (locals lhs-ty)
  "Freeze what the left side left open in LOCALS and LHS-TY.
Return (SKOLEM-LOCALS SKOLEM-TYPE): every free variable of the bound
types and of LHS-TY replaced, in both, by one fresh rigid constant
each.  What the left side left open stands for every value the match
admits -- the pattern's own variables, the instances the head scheme
was read at -- so the right side may read those types but must not
solve them.  The name of each constant carries a gensym only for
distinction; a refusal renders it as itself."
  (let* ((zlocals (mapcar (lambda (cell)
                            (cons (car cell)
                                  (tl-apply-bindings (cdr cell) nil)))
                          locals))
         (zty (tl-apply-bindings lhs-ty nil))
         (open nil))
    (dolist (cell zlocals)
      (dolist (v (tl-free-tvars (cdr cell)))
        (setq open (cons v open))))
    (dolist (v (tl-free-tvars zty))
      (setq open (cons v open)))
    (let ((seen nil) (sub nil))
      (dolist (v open)
        (unless (memq v seen)
          (push v seen)
          (push (cons v (tl-tcon (gensym "sk") nil)) sub)))
      (list (mapcar (lambda (cell)
                      (cons (car cell) (tl-type-subst (cdr cell) sub)))
                    zlocals)
            (tl-type-subst zty sub)))))

(defun tl-preserve--unknown-names (env term)
  "Names in TERM that ENV gives no type to, or nil when it knows them all.
This is the gap half of the verdict.  A reduct that fails to type
against a name the environment has never heard of proves nothing about
the rule, while one that fails with every name known proves the rule
violates preservation -- so the two failures of `tl-preserve--infer'
are told apart by asking, not by reading the message."
  (let ((unknown nil))
    (cl-labels ((known-p (s)
                  (or (eq s '_)
                      (assq s (tl-tenv-locals env))
                      (let ((base (tl-tenv-base env)))
                        (and base
                             (or (gethash s (tl-env-type-env base))
                                 (gethash s (tl-env-method-env base))
                                 (gethash s (tl-env-datatypes base)))))
                      (gethash s tl-builtin-types)
                      (and tl-infer-forward-names
                           (gethash s tl-infer-forward-names))))
                (walk (term bound)
                  (cond
                   ((or (numberp term) (stringp term)) nil)
                   ((symbolp term)
                    (unless (or (memq term bound) (known-p term))
                      (push term unknown)))
                   ((consp term)
                    (pcase (car-safe term)
                      ('lambda
                       (if (and (consp (cdr term)) (consp (cadr term))
                                (consp (cddr term)) (null (cdddr term)))
                           (walk (caddr term) (append (cadr term) bound))
                         (push 'malformed-lambda unknown)))
                      ('let
                       (if (and (consp (cdr term)) (listp (cadr term))
                                (consp (cddr term)))
                           (let ((names nil))
                             (dolist (b (cadr term))
                               (if (and (consp b) (consp (cdr b))
                                        (null (cddr b)))
                                   (progn
                                     (walk (cadr b) bound)
                                     (push (car b) names))
                                 (push 'malformed-let unknown)))
                             (dolist (body (cddr term))
                               (walk body (append names bound))))
                         (push 'malformed-let unknown)))
                      ((or 'do 'list)
                       (dolist (x (cdr term)) (walk x bound)))
                      (_
                       ;; An IR head is read by its handler, never
                       ;; resolved as a name, so it counts as known.
                       (unless (and (symbolp (car term))
                                    (gethash (car term) tl-infer-ir-heads))
                         (walk (car term) bound))
                       (dolist (x (cdr term)) (walk x bound))))))))
      (walk term nil))
    (nreverse unknown)))

(defun tl-preserve--pair (env lhs rhs vars)
  "Type the terms LHS and RHS against each other in ENV.
VARS are the rule's pattern variables: bound while the left side is
read, frozen rigid before the right side is, so the right side is
checked at every type the match allows rather than at the one it would
choose.  Return (VERDICT . REASON) as `tl-preserve-check'."
  (let* ((tl-infer-constraints nil)
         (tl-infer-holes nil)
         (tl-elab-active nil)
         ;; Lenient inference would absorb the very mismatch being
         ;; looked for, so the oracle's tolerance is turned off here.
         (tl-type-lenient nil)
         (locals (mapcar (lambda (v) (cons v (tl-fresh-tvar))) vars))
         (lhs-r (tl-preserve--infer (tl-tenv-extend env locals) lhs)))
    (cond
     ((null (car lhs-r))
      (cons 'cannot-check
            (format "the pattern does not type: %s" (cadr lhs-r))))
     (tl-infer-constraints
      (cons 'cannot-check
            (format "the pattern needs class dictionaries: %S"
                    (mapcar #'tl-constraint-class tl-infer-constraints))))
     (t
      (pcase-let ((`(,sk-vars ,sk-ty)
                   (tl-preserve--skolemize locals (car lhs-r))))
        (setq tl-infer-constraints nil)
        (let* ((env2 (tl-tenv-extend env sk-vars))
               (rhs-r (tl-preserve--infer env2 rhs)))
          (cond
           ((null (car rhs-r))
            (let ((unknown (tl-preserve--unknown-names env2 rhs)))
              (if unknown
                  (cons 'cannot-check
                        (format "the reduct names what nothing has a type for: %S"
                                unknown))
                (cons 'violated
                      (format "the reduct does not type: %s" (cadr rhs-r))))))
           (tl-infer-constraints
            (cons 'cannot-check
                  (format "the reduct needs class dictionaries: %S"
                          (mapcar #'tl-constraint-class tl-infer-constraints))))
           (t
            (let ((u (condition-case e
                          (tl-unify-types sk-ty (car rhs-r) nil)
                        (termlisp-type-error
                         (cons nil (cadr e))))))
              (if (car u)
                  '(preserved)
                (cons 'violated
                      (or (cdr u)
                          (format "the reduct is at %s, the pattern at %s"
                                  (tl-type-text
                                   (tl-type-to-datum (car rhs-r)))
                                  (tl-type-text
                                   (tl-type-to-datum sk-ty)))))))))))))))

(provide 'termlisp-types)
;;; termlisp-types.el ends here
