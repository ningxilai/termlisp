;;; termlisp-dpo.el --- Double-Pushout rewriting, simulated via SPO -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Double-Pushout rewriting is Single-Pushout rewriting plus a condition.
;; A rule is a span L <- K -> R, a match is a morphism m : L -> G, and
;; the step is two pushouts: the complement of L <- K -> G cuts m(L\K) out
;; of G, and the pushout of D <- K -> R glues R back on.
;;
;; Single-Pushout drops the requirement that the complement exist as a
;; subgraph and cuts whatever hangs off m(L\K) whether or not the rule
;; asked for it; its complement therefore always exists.  That is the
;; reason to build DPO *on top of* SPO rather than beside it: check the
;; gluing condition first, and the SPO step that follows is already the
;; DPO step.  One construction serves both, and the part that differs is
;; a predicate rather than a second algorithm.
;;
;; The destructive half -- cutting m(L\K) and re-attaching every edge that
;; pointed at it -- is not performed destructively here.  `tl-node' has no
;; back edges, so a cut would have to find every holder by walking the
;; whole graph; and a term graph hash-conses, so a holder the rule did not
;; mention is some other spelling of the same term.  Instead the reduct is
;; recorded in the node's MEMO slot (see `termlisp-graph'), which every
;; holder reaches through that one indirection.  Nothing is deleted, no
;; CHILDREN list is edited, and SPO's having a complement always become
;; the plain fact that this step never fails.
;;
;; What is left over is exactly the question DPO asks and SPO does not:
;; was the cut closed?  `tl-dpo-gluing' answers it as a pure predicate,
;; naming the node and the condition, and leaves the decision to the
;; caller.  On a shared term graph the answer is often no -- hash-consing
;; means a redex is reachable from every place its spelling occurs -- and
;; a caller reducing a whole term wants the indirection precisely then,
;; so refusing is not the useful default.  It is reported.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-graph)
;; Case patterns are what a clause-based rule matches with, and the
;; image walker below reads them with the same reduction-under-the-subject
;; rule the matcher does; graph cannot require case without a cycle, but
;; nothing case requires leads back here.
(require 'termlisp-case)

(cl-defstruct (tl-dpo-match (:constructor tl-make-dpo-match))
  "A morphism from a rule's left-hand side into a host graph.
ROOT is the image of L's root -- the redex root the step replaces.
IMAGE is the set of host nodes m reached, without repetition: the
dangling condition is a statement about which host nodes the cut would
take, and a set is what that question is about.
POSITIONS is an alist from a pattern position to the host node it
reached, one entry per position, which is where the identification
condition looks: two positions that are different elements of L
reaching one host node is what non-injective means.
INTERFACE is the part of IMAGE that survives the step: the image of K,
the nodes a rule's template names and so cannot be cut.
VARS is an alist from a pattern variable to the host node it matched.

A repeat of one variable must reach one node by `eq', which is what
`tl-graph-match' already demands and what makes the identification
condition decidable here."
  root image positions interface vars)

(defun tl-dpo--rest-p (pat)
  "Return non-nil if PAT is a `(:rest $name)' pattern element."
  (and (consp pat) (eq (car pat) :rest) (tl-graph--pvar-p (cadr pat))))

(defun tl-dpo-match (pattern node)
  "Match PATTERN against NODE, recording the whole correspondence.
Return a `tl-dpo-match', or nil when PATTERN does not fit NODE.
Unlike `tl-graph-match', which keeps only what a template will read,
this records every host node the pattern reached: the gluing condition
is a statement about that set, so the set has to exist before the
question can be asked.  INTERFACE is left nil; `tl-dpo-interface' fills
it in once the template is known."
  (let ((vars nil)
        (image nil)
        (positions nil)
        (ok t))
    (cl-labels ((take (pat nd)
                  (push (cons pat nd) positions)
                  (unless (memq nd image) (push nd image)))
                (bind (pat nd)
                  (let ((cell (assq pat vars)))
                    (cond ((null cell) (push (cons pat nd) vars))
                          ((eq (cdr cell) nd) t)
                          (t (setq ok nil)))))
                (seq (pats nds)
                  (while (and ok pats)
                    (cond
                     ((tl-dpo--rest-p (car pats))
                      (unless (null (cdr pats)) (setq ok nil))
                      (when ok
                        (bind (cadar pats) nds)
                        (dolist (d nds) (take (cadar pats) d))
                        (setq pats nil nds nil)))
                     ((null nds) (setq ok nil))
                     (t (one (car pats) (car nds))
                        (setq pats (cdr pats) nds (cdr nds)))))
                  (when (and ok nds) (setq ok nil)))
                (one (pat nd)
                  (when ok
                    (cond
                     ((tl-graph--pvar-p pat)
                      ;; A repeat is one element of L appearing at two
                      ;; positions, so the node is taken the first time
                      ;; only: recording both would hand `tl-dpo-gluing'
                      ;; two positions of different elements reaching one
                      ;; node, which is not what identification means.
                      (if (assq pat vars)
                          (bind pat nd)
                        (take pat nd)
                        (bind pat nd)))
                     ((consp pat)
                      (if (and (tl-node-application nd)
                               (eq (tl-node-head nd) (car pat)))
                          (progn (take pat nd)
                                 (seq (cdr pat) (tl-node-children nd)))
                        (setq ok nil)))
                     (t (if (and (not (tl-node-application nd))
                                 (eq (tl-node-head nd) pat))
                            (take pat nd)
                          (setq ok nil)))))))
      (one pattern node)
      (when ok
        (tl-make-dpo-match :root node
                           :image (nreverse image)
                           :positions (nreverse positions)
                           :vars (nreverse vars))))))

(defun tl-dpo--template-vars (template)
  "Return the pattern variables TEMPLATE names, in order of appearance.
A template that is a function names no variable: it reads the bindings
itself, and what it keeps of the match is whatever it returns."
  (let ((seen nil)
        (out nil))
    (cl-labels ((go (x)
                  (cond
                   ((tl-graph--pvar-p x) (unless (memq x seen)
                                           (push x seen)
                                           (push x out)))
                   ((tl-graph--splice-p x) (go (cadr x)))
                   ((consp x) (go (car x)) (go (cdr x))))))
      (go template)
      (nreverse out))))

(defun tl-dpo-interface (match template)
  "Fill in MATCH's INTERFACE from TEMPLATE, and return MATCH.
K is what a rule's left and right hand sides share -- the nodes the
template names, which `tl-graph-instantiate' hands back unchanged
rather than rebuilding.  A variable the template never mentions is not
in K, so its node is in the zone the step is entitled to cut, which is
the whole reason the dangling condition has something to say about it."
  (let ((vars (tl-dpo-match-vars match))
        (keep nil))
    (dolist (v (tl-dpo--template-vars template))
      (let ((cell (assq v vars)))
        (when cell (push (cdr cell) keep))))
    (setf (tl-dpo-match-interface match) keep)
    match))

(defun tl-dpo-parents (graph)
  "Return a table mapping every node of GRAPH to its parents.
The value is a list of parent nodes; a root maps to nil.  `tl-node'
records only CHILDREN, so the reverse direction has to be built from
the root -- which is also the only direction in which being outside the
match has a meaning, since a node unreachable from the root is not part
of the graph being rewritten."
  (let ((table (make-hash-table :test #'eq)))
    (dolist (node (tl-graph--preorder (tl-graph-root graph)))
      (unless (gethash node table)
        (puthash node nil table))
      (unless (memq (tl-node-head node) tl-graph-opaque-heads)
        (dolist (child (tl-node-children node))
          (puthash child (cons node (gethash child table)) table))))
    table))

(defun tl-dpo-gluing (match parents)
  "Check DPO's gluing condition for MATCH against a PARENTS table.
Return nil when it holds, or a list (CONDITION NODE) naming the first
offender.  Two conditions are reported.

`identification' -- two positions of L that are different elements
reached one host node.  The complement would have to cut one of them
and keep the other, which is not a subgraph construction; SPO folds
them instead.  One variable appearing twice is not this: a repeat is
one element of L appearing at two positions, and `tl-dpo-match' binds
it once.

`dangling' -- a host node in m(L) outside m(K) has a parent that is not
in m(L).  Cutting it would take an edge the rule never matched, so the
DPO complement does not exist; SPO cuts the edge anyway.

Both are ordinary on a term graph that hash-conses, because a redex is
then reachable from every place its spelling occurs.  This function
reports; it does not decide.  A node absent from PARENTS -- one the
table was not built over -- counts as having no parents."
  (let* ((in-l (make-hash-table :test #'eq))
         (k (make-hash-table :test #'eq))
         (bad nil))
    (dolist (n (tl-dpo-match-image match))
      (puthash n t in-l))
    (dolist (n (tl-dpo-match-interface match))
      (puthash n t k))
    (catch 'identification
      (let ((seen nil))
        (dolist (pair (tl-dpo-match-positions match))
          (let ((nd (cdr pair)))
            (when (memq nd seen)
              (throw 'identification
                     (setq bad (list 'identification nd))))
            (push nd seen)))))
    (unless bad
      (catch 'dangling
        (dolist (n (tl-dpo-match-image match))
          (unless (gethash n k)
            (dolist (p (gethash n parents))
              (unless (gethash p in-l)
                (throw 'dangling (setq bad (list 'dangling n)))))))))
    bad))

(defun tl-spo-apply (match template)
  "Glue TEMPLATE onto MATCH's redex.  Return the reduct.
This is the Single-Pushout half of a rule: it always succeeds, because
it cuts nothing.  The reduct is recorded in the redex root's MEMO slot
for the generation in force, so that every holder of that node reaches
it through one indirection instead of the step having to find and
re-attach each of them.  CHILDREN is not edited, so the graph the
caller still holds reads back exactly as it did.  A record written by
another generation reads back as absent; see `tl-graph-memo-reduct'."
  (let ((reduct (tl-graph-instantiate template (tl-dpo-match-vars match))))
    (tl-graph-memo-record (tl-dpo-match-root match) reduct)
    reduct))

(defun tl-dpo-apply (rule node &optional graph)
  "Apply RULE to NODE under DPO discipline.  Return (REDUCT . GLUING).
REDUCT is nil when RULE does not apply at all.  GLUING is the verdict
of `tl-dpo-gluing', or nil when no PARENTS table was available -- pass
GRAPH to have the condition actually checked, which costs one walk.
The reduct is returned and recorded regardless of GLUING: a condition
that fails says the step was not *local*, not that it was wrong, and on
a shared graph locality is usually what the caller wants to give up.
See `tl-spo-apply' for how the step itself is performed."
  (let* ((pattern (tl-grule-pattern rule))
         (match (and pattern (tl-dpo-match pattern node))))
    (if (null match)
        (cons nil nil)
      (let* ((match (tl-dpo-interface match (tl-grule-template rule)))
             (reduct (tl-spo-apply match (tl-grule-template rule))))
        (cons reduct
              (and graph
                   (tl-dpo-gluing match (tl-dpo-parents graph))))))))

(defun tl-dpo--image-match (pattern node)
  "Match compiled PATTERN against NODE, recording the whole correspondence.
Return a `tl-dpo-match', or nil when PATTERN does not fit NODE.  This is
`tl-pat-match' with every position kept rather than only the bindings a
template would read: a clause-based rule matches through the decision
tree in `termlisp-case', which throws the correspondence away, and the
gluing condition is a statement about that correspondence.

Matching follows `tl-pat-match' exactly, reduction included -- constructor
and literal positions reduce their node through `tl-pat-whnf' first, and
NODE itself is bound as `tl-pat--subject' so it is never reduced -- because
a walker that diverged from the matcher would answer about a different
match than the step took.  INTERFACE is left nil: what the step actually
kept of the match is read off the reduct, see `tl-dpo--step-gluing'."
  (let ((vars nil)
        (image nil)
        (positions nil)
        (ok t)
        (tl-pat--subject node))
    (cl-labels ((take (pat nd)
                  (push (cons pat nd) positions)
                  (unless (memq nd image) (push nd image)))
                (bind (name nd)
                  (let ((cell (assq name vars)))
                    (cond ((null cell) (push (cons name nd) vars))
                          ((eq (cdr cell) nd) t)
                          (t (setq ok nil)))))
                (bind-list (name nds)
                  ;; `tl-pat-bind-list' compares a repeat with `equal', so
                  ;; a rest variable's agreement is agreement of the list.
                  (let ((cell (assq name vars)))
                    (cond ((null cell) (push (cons name nds) vars))
                          ((equal (cdr cell) nds) t)
                          (t (setq ok nil)))))
                (lseq (pat nodes)
                  ;; `tl-pat-match-list': PAT is a cons/nil chain matched
                  ;; against the node list NODES, element patterns taking
                  ;; the nodes they reach.
                  (pcase pat
                    (`(pnil) (unless (null nodes) (setq ok nil)))
                    (`(pcon cons (prest ,name) (pnil))
                     (bind-list name nodes)
                     (dolist (d nodes) (take (car pat) d)))
                    (`(pcon cons ,head ,tail)
                     (if (null nodes)
                         (setq ok nil)
                       (one head (car nodes))
                       (when ok (lseq tail (cdr nodes)))))
                    (`(prest ,name)
                     (bind-list name nodes)
                     (dolist (d nodes) (take pat d)))
                    (`(pvar ,name)
                     (bind-list name nodes)
                     (dolist (d nodes) (take pat d)))
                    (_ (setq ok nil))))
                (seq (pats nodes)
                  ;; `tl-pat-match-seq': positional, exact arity unless a
                  ;; final `(prest NAME)' takes the rest.
                  (while (and ok pats)
                    (cond
                     ((eq (car-safe (car pats)) 'prest)
                      (unless (null (cdr pats)) (setq ok nil))
                      (when ok
                        (bind-list (cadr (car pats)) nodes)
                        (dolist (d nodes) (take (car pats) d))
                        (setq pats nil nodes nil)))
                     ((null nodes) (setq ok nil))
                     (t
                      (one (car pats) (car nodes))
                      (setq pats (cdr pats) nodes (cdr nodes)))))
                  (when (and ok pats) (setq ok nil)))
                (one (pat nd)
                  (when ok
                    (pcase pat
                      (`(pvar ,name)
                       (if (assq name vars)
                           (bind name nd)
                         (take pat nd)
                         (bind name nd)))
                      (`(pwild) (take pat nd))
                      ((or `(plit ,value) `(lit ,value))
                       ;; `lit' is what `tl-nbe--case-pattern' has been
                       ;; known to emit; `tl-pat-match' would signal on
                       ;; it, so a step matched through the tree with it
                       ;; cannot exist -- but reading both keeps this
                       ;; walker from being the thing that breaks.
                       (let ((m (tl-pat-whnf nd)))
                         (when (and (not (tl-node-application m))
                                    (equal (tl-node-head m) value))
                           (take pat m))))
                      (`(pnil)
                       (let ((m (tl-pat-whnf nd)))
                         (when (and (not (tl-node-application m))
                                    (eq (tl-node-head m) nil))
                           (take pat m))))
                      (`(pas ,name ,sub)
                       ;; An as-pattern renames what its subpattern
                       ;; already reached; it adds no position of its
                       ;; own, so it is not taken.
                       (one sub nd)
                       (when ok (bind name nd)))
                      (`(pcon ,head . ,pats)
                       (let ((m (tl-pat-whnf nd)))
                         (cond
                          ((null pats)
                           (when (and (not (tl-node-application m))
                                      (eq (tl-node-head m) head))
                             (take pat m)))
                          ((and (null (cdr pats))
                                (tl-pat-list-pattern-p (car pats)))
                           (when (and (tl-node-application m)
                                      (eq (tl-node-head m) head))
                             (take pat m)
                             (lseq (car pats) (tl-node-children m))))
                          ((and (tl-node-application m)
                                (eq (tl-node-head m) head))
                           (take pat m)
                           (seq pats (tl-node-children m)))
                          (t (setq ok nil)))))
                      (_ (setq ok nil))))))
      (one pattern node)
      (when ok
        (tl-make-dpo-match :root node
                           :image (nreverse image)
                           :positions (nreverse positions)
                           :vars (nreverse vars))))))

(defun tl-dpo--step-gluing (graph node rule reduct)
  "Return the gluing verdict of the step RULE took at NODE in GRAPH, or nil.
REduct is the step's result, still unrecorded -- the graph handed in is
the graph the cut is about to happen to, which is the only state the
question can be asked in.

The match is made again here rather than carried out of the reducer:
`tl-graph--step' asks only whether a rule applied, and the
correspondence the gluing condition speaks about does not survive that
trip.  Nothing has changed yet when this runs, so it is the same match
the step took.  A pattern/template rule is matched with `tl-dpo-match';
a clause-based rule is matched with the case matcher to learn which
clause won, and the image is walked from that clause's compiled pattern
by `tl-dpo--image-match'.

K -- the part of m(L) the step does not cut -- is read off REDUCT: the
nodes of m(L) that the reduct still holds are exactly what survived.  For
a data template that is what `tl-dpo-interface' would have found by
reading the template, because a template rebuilds everything it does not
name; for a closure template, which names no variable and reads its
bindings itself, it is the only honest answer.  Return nil when the cut
was local, or a list (CONDITION NODE) as `tl-dpo-gluing' reports it."
  (let* ((pattern (tl-grule-pattern rule))
         (match
          (if pattern
              (tl-dpo-match pattern node)
            (let ((cm (tl-graph-crule-match node rule)))
              (and cm
                   (tl-dpo--image-match
                    (car (nth (car cm) (tl-grule-clauses rule)))
                    node))))))
    (when match
      (let ((kept (make-hash-table :test #'eq))
            (keep nil))
        (dolist (n (tl-graph--preorder reduct))
          (puthash n t kept))
        (dolist (n (tl-dpo-match-image match))
          (when (gethash n kept)
            (push n keep)))
        (setf (tl-dpo-match-interface match) keep))
      (tl-dpo-gluing match (tl-dpo-parents graph)))))

(defvar tl-dpo-last-gluing nil
  "The gluing verdict of the most recent DPO normalisation, or nil.
Set by `tl-dpo-normalize'.  A list `(CONDITION NODE)' naming the first
cut the walk took that was not local -- `tl-dpo-gluing' reports the
condition -- or nil when every cut was.  This is a record rather than an
error because being unreachable from anywhere but the redex is not a
property a hash-consed term graph usually has.")

(defun tl-dpo-normalize (node rules fuel signal)
  "Reduce NODE to normal form with RULES, under DPO discipline.
Wrap NODE in a graph of its own -- it may be reachable from a signature
-- reduce it, and hand back the reduct.  FUEL and SIGNAL are
`tl-graph-rewrite''s: how many steps may be taken, and the error class
to report when they run out.

Every step the walk takes is checked as it happens: `tl-graph-step-hook'
is bound for the duration, each step's cut is run through
`tl-dpo--step-gluing' against the graph it is about to happen to, and
the first verdict that is not local is written to `tl-dpo-last-gluing'.
The verdict is left there rather than signalled -- a redex reachable
from more than one place is the ordinary case on a hash-consed graph,
and a normalisation that refused there would refuse most of what it is
asked to do.  What the verdict is for is that a caller needing the
reduction to have been local can ask whether it was; nil means every
cut the walk took was."
  (setq tl-dpo-last-gluing nil)
  (if (null rules)
      node
    (let ((tl-graph-step-hook
           (lambda (graph redex rule reduct)
             (unless tl-dpo-last-gluing
               (let ((verdict (tl-dpo--step-gluing graph redex rule reduct)))
                 (when verdict
                   (setq tl-dpo-last-gluing verdict)))))))
      (tl-graph-root
       (tl-graph-rewrite (tl-make-graph node nil) rules fuel signal)))))

(provide 'termlisp-dpo)
;;; termlisp-dpo.el ends here
