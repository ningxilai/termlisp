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
(cl-defstruct (tl-cclass (:constructor tl-cclass (name params supers methods &optional fundeps)))
  name params supers methods fundeps)
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

(defun tl-tarrow (a b) (tl-tcon '-> (list a b)))
(defun tl-tint () (tl-tcon 'Int nil))
(defun tl-tstring () (tl-tcon 'String nil))
(defun tl-tbool () (tl-tcon 'Bool nil))

(defun tl-tfun-args (ty)
  "If TY is `(-> a b)', return (a b), else nil."
  (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
    (tl-tcon-args ty)))

(defvar tl-occurrence-check nil
  "When non-nil, unification performs the occurs check.
A cyclic (infinite) type is then rejected with a `termlisp-type-error'
naming it.  Off by default: equirecursive types (as in Coalton) are
allowed, matching `tl-gtype--default-occurs-check'.")

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
    (tl-tcon (tl-type-head (car sexp)) (mapcar #'tl-type-parse* (cdr sexp))))
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
\(reused for extensions and for an explicitly declared parameter list).
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
          (mapcar (lambda (s) (cons s (tl-fresh-tvar))) param-syms))
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
         (syms (or param-syms (mapcar #'car (reverse tl-type-parse-vars)))))
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
             (tl-register-datatype-kind env name params))
            (t (puthash name (length syms) (tl-env-kind-env env))))
      ;; Each constructor arrows its field types onto its own result.
      (dolist (pair (cl-mapcar #'cons ctor-args results))
        (let ((ca (car pair)) (ty (cdr pair)))
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
     ((and tl-infer-forward-names (gethash sym tl-infer-forward-names))
      (cons (tl-fresh-tvar) nil))
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
is only an answer to that question."
  (cond
   ((or (eq pattern '_) (eq pattern nil)) nil)
   ((symbolp pattern)
    (and (tl-constructor-name-p env pattern) (tl-tcon pattern nil)))
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
                  (puthash name sig tyenv))
              (setq tl-elab-bindings bindings)
              (when (fboundp 'tl-kind-check)
                (tl-kind-check env final))
              (let ((kept (tl-close-constraints env gen-vars tl-infer-constraints bindings)))
                (puthash name (tl-generalize final kept) tyenv)))))))))

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
            ty)
        (if (tl-syntactic-value-p expr)
            (let* ((gen-vars (tl-generalized-vars ty))
                   (kept (tl-close-constraints env gen-vars tl-infer-constraints bindings)))
              (puthash name (tl-generalize ty kept) (tl-env-type-env env)))
          (tl-close-constraints env nil tl-infer-constraints bindings)
          (puthash name (tl-tscheme nil ty) (tl-env-type-env env)))
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
    name))

(defun tl-typecheck-define (env form)
  "Typecheck a `define' FORM, registering it in ENV.
A definition whose name is a class method is skipped: its signature
comes from the class declaration (registered in `tl-env-method-env'),
and instance implementations are checked against that signature."
  (let ((target (cadr form))
        (tl-occurrence-check (tl-env-option env :occurs-check)))
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
FUNDEPS, when present, is `(fundeps (A... -> B...)...)' of parameter names."
  (let* ((name (nth 1 form))
         (params (nth 2 form))
         (super-forms (nth 3 form))
         (rest (nthcdr 4 form))
         (fundep-form (and (consp (car (last rest)))
                           (eq (caar (last rest)) 'fundeps)
                           (car (last rest))))
         (method-decls (if fundep-form (butlast rest) rest))
         (pindex (cl-loop for p in params for i from 0 collect (cons p i)))
         (parse-vars (cl-loop for p in params collect (cons p (tl-fresh-tvar))))
         (first-var (cdr (car parse-vars)))
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
    (puthash name (tl-cclass name params supers methods fundeps)
             (tl-env-class-env env))
    (dolist (m methods)
      (puthash (car m) (cdr m) (tl-env-method-env env)))
    name))

(defun tl-register-instance (env form)
  "Register `(instance (CLASS TYPE) [CONTEXT] DICT)' in ENV.
CONTEXT, when present, is a list of `(CLASS TYPE)' predicates the instance
requires; DICT is then a constructor applied to one sub-dictionary per
context predicate.  Without a context DICT is the runtime dictionary value
the elaborator inserts as the first argument of overloaded method calls."
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
    ;; STRING is one batch, so this is the first moment every definition
    ;; in it has all of its clauses and a coverage check can mean
    ;; anything.  A form that fails leaves nothing queued: the driver
    ;; clears the queue before the check runs.
    (tl-run-post-batch)))

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
