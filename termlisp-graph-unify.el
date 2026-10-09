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
;; a trail, preserving the no-change-loser discipline of `tl-unify'.
;;
;; The generic kernel of `termlisp-unify' can also traverse nodes, via the
;; `tl-decompose'/`tl-rebuild' methods below, which cross-checks this
;; implementation against the alist unifier.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-unify)
(require 'termlisp-graph)

(defun tl-node-var-p (node)
  "Return non-nil when NODE is a unification variable."
  (and (tl-node-p node) (tl-node-var node)))

(defun tl-make-var-node (&optional name)
  "Return a fresh unification variable node named NAME."
  (let ((node (tl-make-node (or name (gensym "tv")))))
    (setf (tl-node-var node) t)
    node))

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
     ((and kx ky (/= kx ky))
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

(defvar tl-gnode--fail-reason nil
  "Why the most recent `tl-gnode-unify' failed: nil, or `infinite-type'.
Bound and inspected by `tl-unify-types' to report an infinite type rather
than a mere mismatch.")

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
                 (let ((hx (tl-node-head x)) (hy (tl-node-head y)))
                   ;; Heads are compared with `eq': two distinct unbound
                   ;; variable nodes are `equal' structurally but must
                   ;; still be unified.
                   (or (eq hx hy)
                       (tl-node-var-p hx) (tl-node-var-p hy))))
            (let ((hx (tl-node-head x)) (hy (tl-node-head y)))
              ;; Higher-kinded: a variable in head position unifies with
              ;; the other head (e.g. `(f a)' against `(Maybe Int)').
              (unless (eq hx hy)
                (push (cons (if (tl-node-p hx) hx (tl-make-node hx))
                            (if (tl-node-p hy) hy (tl-make-node hy)))
                      pending))
              (let ((cx (tl-node-children x)) (cy (tl-node-children y)))
                (while cx
                  (push (cons (car cx) (car cy)) pending)
                  (setq cx (cdr cx) cy (cdr cy))))))
           ((equal x y))
           (t (setq ok nil) (throw 'tl-gnode-fail nil)))))
      t)
    (if ok
        t
      (tl-gnode--rollback trail)
      nil)))

;;; Bridge to the generic unifier (`termlisp-unify').

(cl-defmethod tl-decompose ((x tl-node))
  "Expose a compound node as (HEAD . CHILDREN) to the generic unifier.
Only `tl-decompose' is needed: the generic unifier never calls `tl-rebuild'."
  (when (and (tl-node-application x) (not (tl-node-var x)))
    (cons (tl-node-head x) (tl-node-children x))))

(provide 'termlisp-graph-unify)
;;; termlisp-graph-unify.el ends here
