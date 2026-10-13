;;; termlisp-graph-unify.el --- Term-graph unification -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Unification on the shared term graph of `termlisp-graph'.  A node is
;; either a *variable* (its VAR slot set) or a *compound* (an application
;; node with a head and children).  Unifying a variable with a term links
;; it to that term in place (union-find), so equal structure is shared and
;; cyclic/recursive terms are representable.
;;
;; Following Coalton's type unifier, the occurs check is *off by default*:
;; this makes the system equirecursive.  Bindings are undone on failure via
;; a trail, preserving the no-change-loser discipline.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-graph)

(defun tl-node-var-p (node)
  "Return non-nil when NODE is a unification variable."
  (and (tl-node-p node) (tl-node-var node)))

(defun tl-make-var-node (&optional name)
  "Return a fresh unification variable node named NAME."
  (let ((node (tl-make-node (or name (gensym "tv")))))
    (setf (tl-node-var node) t)
    node))

(defun tl-make-rigid-var (name)
  "Return a *bound* variable node named NAME.
A `Pi' binder fixes its variable before anything is unified, so this
node is a unification variable for traversal and substitution (`var' is
set) but may not be bound: unification meets it only when it is already
the same node, never when it must be equated with something new.  Without
the distinction, unifying two `Pi's would let a caller rewrite the
binder's own type -- `((n : Nat) -> Vec a n)' would happily unify with
`((n : Nat) -> Vec Int Zero)'."
  (let ((node (tl-make-var-node name)))
    (setf (tl-node-rigid node) t)
    node))

(defun tl-gnode-subst (node from to)
  "Return NODE with the rigid variable FROM replaced by TO.
Subtrees are shared, so a variable reached through the result is still
the node it was in NODE: unification through the copy binds the
original, which is what lets two `Pi's be compared without losing the
bindings either side discovers.  A nested `Pi' that rebinds FROM's own
name shadows it, and substitution stops there."
  (let ((memo (make-hash-table :test #'eq)))
    (cl-labels ((go (n)
                  (cond
                   ((eq n from) to)
                   ((not (tl-node-application n)) n)
                   ((and (eq (tl-node-head n) 'Pi)
                         (= (length (tl-node-children n)) 3)
                         (let ((b (car (tl-node-children n))))
                           (and (tl-node-var-p b)
                                (eq (tl-node-head b) (tl-node-head from)))))
                    n)
                   (t (or (gethash n memo)
                          (let ((new (tl-make-node (tl-node-head n)
                                                   (mapcar #'go (tl-node-children n))
                                                   t)))
                            (puthash n new memo)
                            new))))))
      (go node))))

(defun tl-gnode-deref (node)
  "Follow NODE's BIND links to its representative, compressing the path."
  (let ((root node))
    (while (tl-node-bind root)
      (setq root (tl-node-bind root)))
    (let ((p node))
      (while (and (tl-node-bind p) (not (eq p root)))
        (let ((next (tl-node-bind p)))
          (setf (tl-node-bind p) root)
          (setq p next))))
    root))

(defun tl-gnode-occurs (var node)
  "Return non-nil when variable VAR occurs in NODE (cycle-safe)."
  (let ((seen (make-hash-table :test #'eq))
        (stack (list node))
        (found nil))
    (while (and stack (not found))
      (let ((n (tl-gnode-deref (pop stack))))
        (unless (gethash n seen)
          (puthash n t seen)
          (cond ((eq n var) (setq found t))
                ((and (tl-node-application n) (not (tl-node-var n)))
                 (dolist (c (tl-node-children n)) (push c stack)))))))
    found))

(defvar tl-gnode--fail-reason nil
  "Why the most recent `tl-gnode-unify' failed: nil, `infinite-type', or
`kind-mismatch'.  Bound and inspected by callers to report the right error.")

(defun tl-gnode--kinds-compatible (kx ky)
  "Return non-nil when kind nodes KX and KY can be unified.
Uses the kind unifier when available; otherwise structural equality."
  (if (fboundp 'tl-kind-unify)
      (let ((saved tl-gnode--fail-reason))
        (prog1 (tl-kind-unify kx ky)
          (setq tl-gnode--fail-reason saved)))
    (equal kx ky)))

(defun tl-gnode--union (x y trail)
  "Union variable roots X and Y, recording the change on TRAIL.
Return the new representative, or nil on a kind clash (recorded in
`tl-gnode--fail-reason').  Known kinds are propagated to the root."
  (let* ((rx (tl-gnode-deref x))
         (ry (tl-gnode-deref y))
         (kx (tl-node-kind rx))
         (ky (tl-node-kind ry)))
    (cond
     ((eq rx ry) rx)
     ((and kx ky (not (tl-gnode--kinds-compatible kx ky)))
      (setq tl-gnode--fail-reason 'kind-mismatch)
      nil)
     (t
      (let ((root
             (cond
              ((> (tl-node-rank rx) (tl-node-rank ry))
               (push (list ry (tl-node-bind ry) (tl-node-rank ry)) trail)
               (setf (tl-node-bind ry) rx)
               rx)
              ((< (tl-node-rank rx) (tl-node-rank ry))
               (push (list rx (tl-node-bind rx) (tl-node-rank rx)) trail)
               (setf (tl-node-bind rx) ry)
               ry)
              (t
               (push (list ry (tl-node-bind ry) (tl-node-rank ry)) trail)
               (setf (tl-node-bind ry) rx)
               (push (list rx nil (tl-node-rank rx)) trail)
               (setf (tl-node-rank rx) (1+ (tl-node-rank rx)))
               rx))))
        (when (null (tl-node-kind root))
          (setf (tl-node-kind root) (or kx ky)))
        root)))))

(defun tl-gnode--bind (var term trail)
  "Bind representative VAR to TERM, recording the change on TRAIL."
  (push (list var (tl-node-bind var) (tl-node-rank var)) trail)
  (setf (tl-node-bind var) term)
  term)

(defun tl-gnode--rollback (trail)
  "Restore the BIND/RANK changes recorded on TRAIL."
  (dolist (entry trail)
    (let ((node (nth 0 entry))
          (bind (nth 1 entry))
          (rank (nth 2 entry)))
      (setf (tl-node-bind node) bind)
      (setf (tl-node-rank node) rank))))

(defun tl-gnode--head (h)
  "Reduce head H to a form that compares `eq' across representations.
Binding a variable head to a constructor wraps that constructor in a
plain leaf node (see the higher-kinded case in `tl-gnode-unify'), so a
head reached through a variable yields the wrapper while the matching
head written in a type is the bare symbol.  Dereference H and unwrap
such a leaf back to its symbol, so both spellings of one constructor
compare equal.  A head that is still a variable, or a constructor
symbol, is returned unchanged."
  (let ((r (if (tl-node-p h) (tl-gnode-deref h) h)))
    (if (and (tl-node-p r)
             (not (tl-node-var-p r))
             (not (tl-node-application r)))
        (let ((hh (tl-node-head r)))
          (if (tl-node-p hh) (tl-gnode--head hh) hh))
      r)))

(defvar tl-unify-reduce nil
  "Function of one node returning its weak head normal form, or nil.
Set by the layer that owns an evaluation environment (see
`tl-nbe-reduce'); the unifier itself knows nothing of what a
type-level function *is*, only that two types may be equal after being
reduced.  With it nil, unification compares structurally and nothing is
ever reduced, which keeps ordinary Hindley-Milner checking clear of any
evaluator.")

(defvar tl-unify-reduce-fuel 64
  "How many reduction steps one unification pair may take.
Reducing is only ever a second look at a pair nothing else matched, so
the fuel is there to bound the case where it does not help: a type the
unifier is about to reject anyway, whose reduction runs on forever.")

(defun tl-gnode--moves (x y fuel)
  "Non-nil when reducing X or Y would take either one any further.
Called before a variable in head position is bound, where the decision
is irreversible: `f X' against `lenV (vapp xs ys)' would fix `f' to
`lenV', when what it has to become is the `Succ' that side reduces to.
Checking here costs a reduction that the comparison may not need, which
is why it is guarded on `tl-unify-reduce' and FUEL -- with no evaluator
hooked in, nothing ever moves and the binding stands as before."
  (and tl-unify-reduce (> fuel 0)
       (or (and (tl-node-application x)
                (not (eq (funcall tl-unify-reduce x) x)))
           (and (tl-node-application y)
                (not (eq (funcall tl-unify-reduce y) y))))))

(defun tl-gnode-unify (a b &optional occurs-check)
  "Unify nodes A and B, mutating BIND slots.  Return t, or nil (rolled back).
With OCCURS-CHECK, reject cyclic bindings (plain Hindley-Milner); without it
\(the default) the system is equirecursive, as in Coalton.  On failure
`tl-gnode--fail-reason' records `infinite-type' when the occurs check
rejected a cyclic binding."
  (setq tl-gnode--fail-reason nil)
  (let ((trail nil)
        (pending (list (cons a b)))
        (seen (make-hash-table :test #'eq))
        (fuel tl-unify-reduce-fuel)
        (ok t))
    (catch 'tl-gnode-fail
      (while pending
        (let* ((pair (pop pending))
               (x (tl-gnode-deref (car pair)))
               (y (tl-gnode-deref (cdr pair))))
          (cond
           ;; Skip a compound pair already being unified: with
           ;; equirecursive types the same pair can recur.
           ((and (not (tl-node-var-p x)) (not (tl-node-var-p y))
                 (let ((h (or (gethash x seen)
                              (puthash x (make-hash-table :test #'eq) seen))))
                   (prog1 (gethash y h) (puthash y t h)))))
           ((eq x y))
           ;; A rigid (Pi-bound) variable is fixed by its binder, so it
           ;; may only ever be equated with itself -- which the `eq'
           ;; case above already discharged.  Reaching here means
           ;; something is trying to unify the binder's variable with a
           ;; *new* term, which would let a caller rewrite the very type
           ;; the binder was declared over.
           ((or (and (tl-node-var-p x) (tl-node-rigid x))
                (and (tl-node-var-p y) (tl-node-rigid y)))
            (setq ok nil) (throw 'tl-gnode-fail nil))
           ;; Two dependent function types are equal up to what their
           ;; binders are *called*.  Binders are rigid and so cannot be
           ;; unified away; re-spell the second type's binder as the
           ;; first's and the comparison proceeds structurally.
           ((and (tl-node-application x) (tl-node-application y)
                 (eq (tl-node-head x) 'Pi) (eq (tl-node-head y) 'Pi)
                 (= (length (tl-node-children x)) 3)
                 (= (length (tl-node-children y)) 3))
            (let ((xa (tl-node-children x))
                  (ya (tl-node-children y)))
              (push (cons (nth 1 xa) (nth 1 ya)) pending)
              (push (cons (tl-gnode-subst (nth 2 ya) (nth 0 ya) (nth 0 xa))
                          (nth 2 xa))
                    pending)))
           ((tl-node-var-p x)
            (when (and occurs-check (tl-gnode-occurs x y))
              (setq ok nil tl-gnode--fail-reason 'infinite-type)
              (throw 'tl-gnode-fail nil))
            ;; A variable binds to the non-variable term (so it derefs
            ;; to it); two variables union by rank.
            (if (tl-node-var-p y)
                (unless (tl-gnode--union x y trail)
                  (setq ok nil) (throw 'tl-gnode-fail nil))
              (tl-gnode--bind x y trail)))
           ((tl-node-var-p y)
            (when (and occurs-check (tl-gnode-occurs y x))
              (setq ok nil tl-gnode--fail-reason 'infinite-type)
              (throw 'tl-gnode-fail nil))
            (if (tl-node-var-p x)
                (unless (tl-gnode--union y x trail)
                  (setq ok nil) (throw 'tl-gnode-fail nil))
              (tl-gnode--bind y x trail)))
           ((and (tl-node-application x) (tl-node-application y)
                 (= (length (tl-node-children x))
                    (length (tl-node-children y)))
                 (let ((hx (tl-gnode--head (tl-node-head x)))
                       (hy (tl-gnode--head (tl-node-head y))))
                   ;; Heads are compared with `eq': two distinct unbound
                   ;; variable nodes are `equal' structurally but must
                   ;; still be unified.
                   (and (or (eq hx hy)
                            ;; A head that is neither a symbol nor a node
                            ;; has no `eq' to offer: a `lambda' written
                            ;; straight into a type is a list, and its two
                            ;; occurrences in one signature are two
                            ;; different lists spelling one term.  Compare
                            ;; by value, but only where neither side is a
                            ;; node -- two distinct unbound variables are
                            ;; `equal' structurally and must still be
                            ;; unified, which is the whole reason `eq' is
                            ;; here in the first place.
                            (and (not (tl-node-p hx)) (not (tl-node-p hy))
                                 (equal hx hy))
                            (or (tl-node-var-p hx) (tl-node-var-p hy)))
                        ;; Matching heads are not by themselves a licence
                        ;; to decompose: `plus Zero (plus m k)' and `plus
                        ;; (plus Zero m) k' share the head `plus' and are
                        ;; one and the same number, yet their first
                        ;; arguments are `Zero' and a stuck `plus', so
                        ;; decomposing compares those and fails where
                        ;; reducing would say they agree.  A head that is
                        ;; not a function never moves, so this costs
                        ;; nothing where nothing can reduce -- and with no
                        ;; evaluator hooked in `tl-gnode--moves' answers
                        ;; nil for everything, which is the ordinary
                        ;; Hindley-Milner case exactly as before.
                        (not (tl-gnode--moves x y fuel)))))
            (let ((hx (tl-gnode--head (tl-node-head x)))
                   (hy (tl-gnode--head (tl-node-head y))))
              ;; Higher-kinded: a variable in head position unifies with
              ;; the other head (e.g. `(f a)' against `(Maybe Int)').
              (unless (eq hx hy)
                (push (cons (if (tl-node-p hx) hx (tl-make-node hx))
                            (if (tl-node-p hy) hy (tl-make-node hy)))
                      pending))
              (let ((cx (reverse (tl-node-children x)))
                    (cy (reverse (tl-node-children y))))
                ;; Left to right: `push' reverses, so the children are
                ;; walked backwards to come off `pending' in the order
                ;; they were written.  That order is not a matter of
                ;; taste here -- a later argument may mention an earlier
                ;; one, and a type-level function cannot reduce until the
                ;; argument it matches on is known, so comparing `Vec a
                ;; (plus n m)' before `Vec a n' has fixed `n' asks the
                ;; unifier to prove something it has not yet been told.
                (while cx
                  (push (cons (car cx) (car cy)) pending)
                  (setq cx (cdr cx) cy (cdr cy))))))
           ((equal x y))
           ;; Two types can be equal without looking alike: `plus Zero n'
           ;; and `n' are one and the same type, yet one is an
           ;; application and the other is a variable, and nothing above
           ;; was willing to match them.  Reduce both to weak head
           ;; normal form and take another look.
           ;;
           ;; Neither having moved means they are simply different: the
           ;; pair must fail here rather than be dropped, or the `seen'
           ;; guard further up would take the repeat for a recursive type
           ;; equating itself and pass -- which is how a two-domain
           ;; definition once satisfied a four-domain signature.  Fuel
           ;; bounds the other side, a reduction that keeps handing back
           ;; a fresh node for types about to be rejected anyway.
           ((and tl-unify-reduce (> fuel 0)
                 (or (tl-node-application x) (tl-node-application y)))
            (let ((rx (if (tl-node-application x)
                          (funcall tl-unify-reduce x) x))
                  (ry (if (tl-node-application y)
                          (funcall tl-unify-reduce y) y)))
              (if (and (eq rx x) (eq ry y))
                  (progn (setq ok nil) (throw 'tl-gnode-fail nil))
                (setq fuel (1- fuel))
                (push (cons rx ry) pending))))
           (t (setq ok nil) (throw 'tl-gnode-fail nil)))))
      t)
    (if ok
        t
      (tl-gnode--rollback trail)
      nil)))

(provide 'termlisp-graph-unify)
;;; termlisp-graph-unify.el ends here
