;;; termlisp-case.el --- Case-tree matcher for the TGR -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A compiled pattern is a tagged list:
;;   (pvar NAME)       bind NAME
;;   (pwild)           match anything, bind nothing
;;   (plit VALUE)      match a literal VALUE
;;   (pcon HEAD PAT...) match constructor HEAD with subpatterns PAT...
;;   (pas NAME PAT)    match PAT and also bind the whole value to NAME
;;   (pnil)            match the empty list
;;   (prest NAME)      bind NAME to the remaining sibling nodes as a list
;; `tl-pat-parse' turns surface patterns into these compiled patterns.
;;
;; `prest' may only appear as the final element of a constructor's
;; subpatterns, e.g. `(pcon :hooks (pvar $a) (prest $rest))'.  It binds
;; `$rest' to the (possibly empty) list of the application node's remaining
;; children, so a variadic rule can capture an argument list; the
;; template's `(:splice $rest)' element splices those nodes back into the
;; replacement.
;;
;; A constructor whose sole subpattern is a list pattern, e.g.
;; `(pcon :hooks (plist (pvar $a) (pvar $b) (prest $rest)))', matches its
;; whole child list against that pattern (a `plist' chain plus an optional
;; trailing `(prest NAME)').  This is the direct analogue of the design's
;; "structural patterns over the argument list" and is the recommended way
;; to write repeatable keywords.  A `plist' in any other argument position
;; is an ordinary cons/nil pattern over a single child.
;;
;; A template is instantiated by `tl-graph-instantiate', in
;; `termlisp-graph', which substitutes the *node* that was matched where a
;; template says `$name' rather than that node's s-expression.  The
;; difference matters to a host whose variables are the nodes themselves:
;; a fresh leaf in place of a matched one is not the variable that was
;; matched, so anything equated against it would be equated against
;; nothing.
;;
;; Matching may reduce.  A host binds `tl-graph-whnf' and every argument is
;; reduced through it before its constructor is looked at, because `(id
;; Zero)' occupies an argument before it is known to be a `Zero'.  The node
;; a rule is being matched against (`tl-pat--subject') is the one exception:
;; reducing it would be the very step whose clause is being selected.
;;
;; `tl-case-compile' turns a list of `(PATTERN . TEMPLATE)' clauses into a
;; decision tree (an Idris `CaseBuilder'-style dispatcher):
;;   (ct-case COLUMN ALTS)     scrutinise position COLUMN
;;   (ct-leaf INDEX)           clause INDEX matched (first match wins)
;;   (ct-fail)                 no clause matches
;;   (ct-con HEAD ARITY TREE)  value is constructor HEAD applied to ARITY args
;;   (ct-const VALUE TREE)     value is the literal VALUE
;;   (ct-default TREE)         value is anything else (a variable clause)
;;
;; COLUMN addresses a position in a clause's flat pattern vector.  A clause
;; starts as the one-element vector (PATTERN); refining a constructor at
;; column C replaces that entry with the constructor's subpatterns, which
;; then occupy columns C..C+N-1, mirroring Idris's splicing of a
;; constructor's arguments into the pattern vector.
;;
;; `pas' is transparent to dispatch (its inner pattern decides the group).
;; All bindings, including the whole-subterm binding of a `pas', are
;; recovered when the winning clause's original pattern is matched, so the
;; tree only records the winning clause index.

;;; Code:

(require 'termlisp-base)
(require 'termlisp-graph)

(defun tl-pat-parse (sexp)
  "Parse surface pattern SEXP into a compiled pattern.
Signal `termlisp-error' on an unknown form."
  (pcase sexp
    (`(pvar ,name) (list 'pvar name))
    (`(pwild) '(pwild))
    (`(plit ,value) (list 'plit value))
    (`(pcon ,head . ,pats) (cons 'pcon (cons head (mapcar #'tl-pat-parse pats))))
    (`(pas ,name ,pat) (list 'pas name (tl-pat-parse pat)))
    (`(plist . ,pats) (tl-pat-parse-list pats))
    (`(prest ,name) (list 'prest name))
    (_ (signal 'termlisp-error (list (format "Bad pattern: %S" sexp))))))

(defun tl-pat-parse-list (pats)
  "Parse PATS as the elements of a `plist' pattern into a cons/nil chain."
  (if (null pats)
      '(pnil)
    (list 'pcon 'cons (tl-pat-parse (car pats)) (tl-pat-parse-list (cdr pats)))))

(defvar tl-pat--subject nil
  "The node a rule is currently being matched against, or nil outside one.
`tl-pat-whnf' leaves the subject alone: reducing it would be the very step
whose clause we are trying to pick, so the matcher would ask the question
again and never answer.  Everything below the subject is fair game -- an
argument has to be reduced before its constructor is visible.")

(defun tl-pat-whnf (node)
  "Return NODE reduced enough to expose its constructor, or NODE itself.
Reduction comes from `tl-graph-whnf', which a host binds while it matches;
nil means no reduction is offered and matching stays purely structural.
The node a rule is being matched against (`tl-pat--subject') is never
reduced: see there.  Without reduction below the subject a clause could not
see that `plus Zero n' already *is* a `Succ', so a type that ought to
reduce would be reported as unequal."
  (if (and tl-graph-whnf (not (eq node tl-pat--subject)))
      (funcall tl-graph-whnf node)
    node))

(defun tl-pat-match (pat node bindings)
  "Match compiled pattern PAT against graph NODE, extending BINDINGS.
Return `(t . bindings)' on success and nil on failure, following the
`tl-unify' convention.  BINDINGS is a proper alist mapping pattern
variables to nodes; a successful match with no bindings still returns a
truthy `(t)' so it is distinguishable from failure.

A `(pcon HEAD)' with no subpatterns matches a non-application node whose
head is `eq' to HEAD.  A zero-child application `(HEAD)' is deliberately
not matched, preserving the TGR distinction between the atom `HEAD' and
the nullary application `(HEAD)'; a nullary type constructor is built as
an atom, so nothing at the type level depends on the distinction.

Constructor and literal patterns reduce NODE first through `tl-pat-whnf'.
A variable or wildcard binds NODE as it stands, because the term that is
substituted into a body later is the unreduced one."
  (pcase pat
    (`(pvar ,name)
     (let ((cell (assq name bindings)))
       (cond ((null cell) (cons t (cons (cons name node) bindings)))
             ((eq (cdr cell) node) (cons t bindings))
             (t nil))))
    (`(pwild) (cons t bindings))
    (`(plit ,value)
     (let ((node (tl-pat-whnf node)))
       (when (and (not (tl-node-application node))
                  (equal (tl-node-head node) value))
         (cons t bindings))))
    (`(pnil)
     (when (and (not (tl-node-application node))
                (eq (tl-node-head node) nil))
       (cons t bindings)))
    (`(pcon ,head . ,pats)
     (let ((node (tl-pat-whnf node)))
       (cond
        ((null pats)
         (when (and (not (tl-node-application node))
                    (eq (tl-node-head node) head))
           (cons t bindings)))
        ;; A sole list subpattern matches the whole child list, so a variadic
        ;; application can be written `(pcon HEAD (plist ...))'.
        ((and (null (cdr pats)) (tl-pat-list-pattern-p (car pats)))
         (when (and (tl-node-application node)
                    (eq (tl-node-head node) head))
           (tl-pat-match-list (car pats) (tl-node-children node) bindings)))
        ((and (tl-node-application node)
              (eq (tl-node-head node) head))
         (tl-pat-match-seq pats (tl-node-children node) bindings)))))
    (`(pas ,name ,sub)
     (let ((r (tl-pat-match sub node bindings)))
       (when r
         (let ((cell (assq name (cdr r))))
           (cond ((null cell) (cons t (cons (cons name node) (cdr r))))
                 ((eq (cdr cell) node) r)
                 (t nil))))))
    (_ (signal 'termlisp-error (list (format "Bad compiled pattern: %S" pat))))))

(defun tl-pat-match-seq (pats nodes bindings)
  "Match PATS against NODES positionally, extending BINDINGS.
Exact arity is required unless the final pattern is a `(prest NAME)',
which binds NAME to the list of remaining NODES (possibly empty)."
  (let ((ok t))
    (while (and ok pats)
      (cond
       ((eq (car-safe (car pats)) 'prest)
        (unless (null (cdr pats))
          (signal 'termlisp-error
                  '("A (prest NAME) pattern must be the last list element")))
        (let ((r (tl-pat-bind-list (cadr (car pats)) nodes bindings)))
          (if r (setq bindings r) (setq ok nil)))
        (setq pats nil nodes nil))
       ((null nodes) (setq ok nil))
       (t
        (let ((r (tl-pat-match (car pats) (car nodes) bindings)))
          (if r
              (setq bindings (cdr r) pats (cdr pats) nodes (cdr nodes))
            (setq ok nil))))))
    (when (and ok (null pats) (null nodes))
      (cons t bindings))))

(defun tl-pat-bind-list (name nodes bindings)
  "Extend BINDINGS with NAME bound to the node list NODES.
Return the extended bindings, or nil when NAME is already bound to a
different list (non-linear pattern)."
  (let ((cell (assq name bindings)))
    (cond ((null cell) (cons (cons name nodes) bindings))
          ((equal (cdr cell) nodes) bindings)
          (t nil))))

(defun tl-pat-list-pattern-p (pat)
  "Return non-nil when compiled PAT is a cons/nil list pattern.
A list pattern used as the sole subpattern of a `pcon' is matched against
the constructor's whole child list by `tl-pat-match-list'."
  (pcase pat
    (`(pnil) t)
    (`(pcon cons . ,_) t)
    (_ nil)))

(defun tl-pat-match-list (pat nodes bindings)
  "Match compiled list PAT against NODES, a list of graph nodes.
PAT is a cons/nil chain as produced by `tl-pat-parse-list'.  A trailing
`(prest NAME)' or a bare `(pvar NAME)' binds the remaining NODES."
  (pcase pat
    (`(pnil) (when (null nodes) (cons t bindings)))
    ;; `tl-pat-parse-list' wraps every element in a cons, so a trailing
    ;; `(prest NAME)' appears as the head of the final cell.
    (`(pcon cons (prest ,name) (pnil))
     (let ((r (tl-pat-bind-list name nodes bindings)))
       (when r (cons t r))))
    (`(pcon cons ,head ,tail)
     (when nodes
       (let ((r (tl-pat-match head (car nodes) bindings)))
         (when r (tl-pat-match-list tail (cdr nodes) (cdr r))))))
    (`(prest ,name)
     (let ((r (tl-pat-bind-list name nodes bindings)))
       (when r (cons t r))))
    (`(pvar ,name)
     (let ((r (tl-pat-bind-list name nodes bindings)))
       (when r (cons t r))))
    (_ (signal 'termlisp-error
               (list (format "Bad list pattern: %S" pat))))))

(defun tl-pat-strip-pas (pat)
  "Return PAT with any outer `pas' wrappers removed."
  (while (eq (car-safe pat) 'pas)
    (setq pat (nth 2 pat)))
  pat)

(defun tl-pat-variable-p (pat)
  "Return non-nil when PAT is irrefutable (matches any value).
A `pvar', a `pwild', a `prest', or a `pas' wrapping one is irrefutable.
`pas' is transparent here because its binding is recovered when the winning
clause is matched, not while dispatching."
  (memq (car-safe (tl-pat-strip-pas pat)) '(pvar pwild prest)))

(defun tl-pat-contains-rest-p (pat)
  "Return non-nil when PAT varies a constructor's arity.
That is a `(prest NAME)' pattern anywhere, or a constructor whose sole
subpattern is a list pattern (matched against the whole child list).  Such
clauses cannot be dispatched by the column-wise decision tree, so
`tl-case-compile' falls back to a linear scan for them."
  (pcase pat
    (`(prest . ,_) t)
    (`(pas ,_ ,sub) (tl-pat-contains-rest-p sub))
    (`(pcon . ,_)
     (let ((subs (cddr pat)))
       (or (and (consp subs) (null (cdr subs))
                (tl-pat-list-pattern-p (car subs)))
           (cl-some #'tl-pat-contains-rest-p subs))))
    (_ nil)))

(defun tl-pat-dispatch-key (pat)
  "Return the dispatch key for refutable pattern PAT, or nil.
The key is `(con HEAD ARITY)' for a constructor, `(const VALUE)' for a
literal, and nil for an irrefutable pattern (see `tl-pat-variable-p')."
  (pcase (tl-pat-strip-pas pat)
    (`(pcon ,head . ,subs) (list 'con head (length subs)))
    (`(plit ,value) (list 'const value))
    (`(pnil) (list 'const nil))
    (_ nil)))

(defun tl-pat-dispatch-heads (pat)
  "Return the head values PAT can match, or `:generic'.
A `(pcon HEAD ...)' pattern only matches a node whose head is HEAD, and a
literal `(plit VALUE)' or `(pnil)' only matches a node whose head is VALUE
or nil respectively, so those are the values a rule with such a pattern can
be indexed under.  An irrefutable pattern (variable, wildcard or rest)
matches any head and yields `:generic'.  `pas' is transparent."
  (pcase (tl-pat-strip-pas pat)
    (`(pcon ,head . ,_) (list head))
    (`(plit ,value) (list value))
    (`(pnil) (list nil))
    (_ :generic)))

(defun tl-ct-refutable-column (rows)
  "Return the leftmost column holding a refutable pattern in ROWS, or nil.
Every ROW is `(PATTERNS . CLAUSE-INDEX)' and all rows have equal width."
  (let ((width (length (car (car rows))))
        (col nil)
        (c 0))
    (while (and (null col) (< c width))
      (when (cl-some (lambda (row)
                       (not (tl-pat-variable-p (nth c (car row)))))
                     rows)
        (setq col c))
      (setq c (1+ c)))
    col))

(defun tl-ct-row-drop (row col)
  "Return ROW with the pattern at COL removed."
  (cons (append (cl-subseq (car row) 0 col)
                (nthcdr (1+ col) (car row)))
        (cdr row)))

(defun tl-ct-row-refine (row col key)
  "Return ROW refined at COL for dispatch KEY.
A constructor key splices its subpatterns into COL; a constant key
consumes COL.  Any `pas' wrapper is stripped."
  (if (eq (car key) 'con)
      (let ((pat (tl-pat-strip-pas (nth col (car row)))))
        (cons (append (cl-subseq (car row) 0 col)
                      (cddr pat)
                      (nthcdr (1+ col) (car row)))
              (cdr row)))
    (tl-ct-row-drop row col)))

(defun tl-ct-row-specialize (row col key)
  "Return irrefutable ROW specialised at COL for dispatch KEY.
A constructor key replaces the variable with ARITY wildcards; a constant
key consumes COL.  Duplicating an irrefutable row into every constructor
alternative is what keeps an earlier catch-all ahead of a later
constructor (first match wins)."
  (if (eq (car key) 'con)
      (cons (append (cl-subseq (car row) 0 col)
                    (make-list (nth 2 key) '(pwild))
                    (nthcdr (1+ col) (car row)))
            (cdr row))
    (tl-ct-row-drop row col)))

(defun tl-ct-groups (rows col)
  "Group refutable ROWS by their dispatch key at COL.
Return an alist of (KEY . ROWS) in first-occurrence order."
  (let (groups)
    (dolist (row rows)
      (let* ((key (tl-pat-dispatch-key (nth col (car row))))
             (cell (assoc key groups)))
        (if cell
            (setcdr cell (append (cdr cell) (list row)))
          (setq groups (append groups (list (cons key (list row))))))))
    groups))

(defun tl-ct-alt (key subtree)
  "Build the constructor or constant alternative for KEY and SUBTREE."
  (pcase key
    (`(con ,head ,arity) (list 'ct-con head arity subtree))
    (`(const ,value) (list 'ct-const value subtree))))

(defun tl-ct-build-rows (rows)
  "Compile equal-width pattern ROWS into a decision tree.
Return `(ct-fail)' when ROWS is empty and `(ct-leaf INDEX)' when the first
row is irrefutable (it matches everything left to match)."
  (if (null rows)
      '(ct-fail)
    (let ((col (tl-ct-refutable-column rows)))
      (if (null col)
          (list 'ct-leaf (cdr (car rows)))
        (tl-ct-build-case col rows)))))

(defun tl-ct-build-case (col rows)
  "Compile ROWS by dispatching on column COL."
  (let (vars refs)
    (dolist (row rows)
      (if (tl-pat-variable-p (nth col (car row)))
          (setq vars (append vars (list row)))
        (setq refs (append refs (list row)))))
    (let ((alts nil))
      (dolist (group (tl-ct-groups refs col))
        (let* ((key (car group))
               (combined (append
                          (mapcar (lambda (r) (tl-ct-row-refine r col key))
                                  (cdr group))
                          (mapcar (lambda (r) (tl-ct-row-specialize r col key))
                                  vars))))
          (setq combined (sort combined (lambda (a b) (< (cdr a) (cdr b)))))
          (setq alts (append alts
                             (list (tl-ct-alt key (tl-ct-build-rows combined)))))))
      ;; The default alternative is taken without consuming COLUMN, so the
      ;; irrefutable rows keep their column and the later columns stay put.
      (when vars
        (setq alts (append alts
                           (list (list 'ct-default (tl-ct-build-rows vars))))))
      (list 'ct-case col alts))))

(defun tl-case-compile (clauses)
  "Compile CLAUSES into a decision tree.
Each clause is `(PATTERN . TEMPLATE)' where PATTERN is a compiled pattern
from `tl-pat-parse'.  Clauses are matched in order; the tree dispatches on
the leftmost column with a refutable pattern and, at a leaf, records the
index of the winning clause.

When any clause contains a `(prest NAME)' pattern its constructor arity is
not fixed, so the column-wise tree cannot dispatch it; such clause lists
compile to `(ct-linear)', which `tl-case-match' evaluates by scanning the
clauses in order."
  (if (cl-some (lambda (clause) (tl-pat-contains-rest-p (car clause))) clauses)
      '(ct-linear)
    (let ((rows nil)
          (index 0))
      (dolist (clause clauses)
        (setq rows (append rows (list (cons (list (car clause)) index))))
        (setq index (1+ index)))
      (tl-ct-build-rows rows))))

(defun tl-case--con-match-p (value head arity)
  "Return non-nil when VALUE is the constructor HEAD applied to ARITY args.
A zero-arity constructor is the atom HEAD (a non-application node), matching
`tl-pat-match's treatment of a `(pcon HEAD)' with no subpatterns; a positive
arity requires an application node with exactly ARITY children."
  (if (= arity 0)
      (and (not (tl-node-application value))
           (eq (tl-node-head value) head))
    (and (tl-node-application value)
         (eq (tl-node-head value) head)
         (= (length (tl-node-children value)) arity))))

(defun tl-case--replace-nth (list n replacement)
  "Return LIST with element N replaced by the elements of REPLACEMENT."
  (append (cl-subseq list 0 n) replacement (nthcdr (1+ n) list)))

(defun tl-case--remove-nth (list n)
  "Return LIST with element N removed."
  (append (cl-subseq list 0 n) (nthcdr (1+ n) list)))

(defun tl-case-match (tree clauses node)
  "Match NODE against the decision TREE built from CLAUSES.
Return `(INDEX . BINDINGS)' for the first matching clause, or nil when no
clause matches.  BINDINGS is the alist produced by `tl-pat-match' for the
winning clause's original pattern, so whole-subterm and nonlinear bindings
are recovered exactly.
NODE is bound as `tl-pat--subject' for the duration: it is the term the
rule is about, and reducing it would be the very step being selected."
  (let ((tl-pat--subject node))
    (tl-case-match-tree tree clauses
                        (cons node (tl-node-children node))
                        node)))

(defun tl-case-match-tree (tree clauses scrutinees root)
  "Walk TREE over SCRUTINEES, recovering bindings against ROOT.
SCRUTINEES is the flat vector of values addressed by the tree's columns;
descending a constructor splices its children into the vector and a constant
consumes its column, mirroring `tl-ct-row-refine'."
  (pcase tree
    (`(ct-case ,column ,alts)
     ;; Dispatch has to reduce before it can decide: `(id Zero)' occupies
     ;; the column but the branch it belongs to is `Zero''s.  Only the leaf
     ;; reduces (`tl-pat-match') would leave the tree looking at the syntax
     ;; of a term that has not been evaluated yet.
     (tl-case-match-alts alts clauses column scrutinees
                         (tl-pat-whnf (nth column scrutinees)) root))
    (`(ct-leaf ,index)
     (let ((r (tl-pat-match (car (nth index clauses)) root nil)))
       (when r (cons index (cdr r)))))
    (`(ct-fail) nil)
    (`(ct-linear) (tl-case-match-linear clauses root))
    (_ (signal 'termlisp-error (list (format "Bad case tree: %S" tree))))))

(defun tl-case-match-linear (clauses root)
  "Return `(INDEX . BINDINGS)' for the first clause of CLAUSES matching ROOT.
Used for clause lists containing rest patterns, which bypass the decision
tree; see `tl-case-compile'."
  (let ((index 0))
    (catch 'found
      (dolist (clause clauses)
        (let ((r (tl-pat-match (car clause) root nil)))
          (when r (throw 'found (cons index (cdr r)))))
        (setq index (1+ index)))
      nil)))

(defun tl-case-match-alts (alts clauses column scrutinees value root)
  "Dispatch VALUE over ALTS for COLUMN, continuing on the matching branch."
  (catch 'matched
    (dolist (alt alts)
      (pcase alt
        (`(ct-con ,head ,arity ,sub)
         (when (tl-case--con-match-p value head arity)
           (throw 'matched
                  (tl-case-match-tree
                   sub clauses
                   (tl-case--replace-nth scrutinees column
                                         (tl-node-children value))
                   root))))
        (`(ct-const ,const ,sub)
         (when (and (not (tl-node-application value))
                    (equal (tl-node-head value) const))
           (throw 'matched
                  (tl-case-match-tree
                   sub clauses (tl-case--remove-nth scrutinees column) root))))
        (`(ct-default ,sub)
         (throw 'matched
                (tl-case-match-tree sub clauses scrutinees root)))
        (_ (signal 'termlisp-error
                   (list (format "Bad case alternative: %S" alt))))))))

;;; Integration with the term-graph rewriter.

(defun tl-graph-crule-match (node rule)
  "Match NODE against clause-based RULE.
Return `(INDEX . BINDINGS)' for the first matching clause, or nil.  RULE's
clauses are compiled to a decision tree once and the tree is memoised in the
rule's `compiled' slot."
  (let ((tree (or (tl-grule-compiled rule)
                  (setf (tl-grule-compiled rule)
                        (tl-case-compile (tl-grule-clauses rule))))))
    (tl-case-match tree (tl-grule-clauses rule) node)))

(defun tl-graph-crule-instantiate (rule match)
  "Build the replacement node for clause-based RULE and MATCH.
MATCH is `(INDEX . BINDINGS)' from `tl-graph-crule-match'; the winning
clause's TEMPLATE is instantiated with `tl-graph-instantiate', which puts
the *matched nodes themselves* where the template says `$name'.  Rendering
the reduct through a sexp and rebuilding it would hand back fresh leaves in
place of the variables that were matched, and a fresh leaf is not a
unification variable: the type layer would then equate a copy while the
original stayed free.  A `(:splice $name)' template element still splices
the node list bound to a `(prest $name)' pattern."
  (let ((clause (nth (car match) (tl-grule-clauses rule))))
    (tl-graph-instantiate (cdr clause) (cdr match))))

(defun tl-graph-crule-reduce (node rule)
  "Return clause-based RULE's reduct for NODE, or nil when it does not apply.
NODE is never modified; see `tl-graph-reduce'."
  (let ((match (tl-graph-crule-match node rule)))
    (when (and match
               (or (null (tl-grule-guard rule))
                   (funcall (tl-grule-guard rule) (cdr match))))
      (tl-graph-crule-instantiate rule match))))

(provide 'termlisp-case)
;;; termlisp-case.el ends here
