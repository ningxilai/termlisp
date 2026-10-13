;;; termlisp-exhaust.el --- Exhaustiveness and redundancy of matches -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:

;; Maranget's usefulness algorithm, driven as a trampoline.
;;
;; Two questions about a set of clauses are the same question wearing
;; different hats.  A set is exhaustive when no value escapes all of it,
;; and a clause is redundant when nothing escapes the clauses above it;
;; both ask "is this pattern vector useful against this matrix of
;; earlier rows?", and this file answers that once.  `tl-exh-exhaustive'
;; asks with an all-wildcard vector; `tl-exh-redundant' asks with each
;; row in turn.
;;
;; The recursion is written as suspended frames rather than elisp calls.
;; A frame holds a thunk computing either the answer or the next frame,
;; and a continuation consuming an answer.  `tl-exh-run' steps frames in
;; a loop that never nests: at every moment exactly one closure is
;; running, so the evaluator's stack depth stays constant however deep
;; the pattern nest goes.  That is what makes a three-deep pattern over a
;; mutually recursive datatype safe rather than a `max-lisp-eval-depth'
;; accident -- which is why this file recurses through `tl-exh-run' and
;; never by calling itself.
;;
;; Every answer is three-valued.  `:yes' and `:no' are decisions;
;; `:unknown' admits that the checker could not decide.  `:unknown' is
;; the one result that must never be read as `:yes'.  A guard is a
;; runtime predicate, a `rest' pattern has no column meaning, an
;; unenumerable column type and an exhausted budget all yield it.
;; Upgrading any of those into "exhaustive" would hand a program a proof
;; it did not earn, which is the entire reason to have the check.
;;
;; Termination is argued rather than hoped for, and the argument has two
;; halves because the recursion has two shapes.  `tl-exh--measure' is the
;; sum of the signature's pattern sizes; every branch but one is required
;; to make it strictly smaller, since specialising a constructor column
;; replaces one pattern by its strictly smaller fields and every other
;; branch drops a column outright.  The exception is the branch that asks
;; about a constructor set in full: there one wildcard column becomes the
;; constructor's field columns, so the measure grows.  That branch is
;; bounded instead by `tl-exh-ancestors', the set of column types already
;; being expanded along the current path -- an equirecursive datatype
;; would otherwise re-ask the same question forever, and a repeat is cut
;; with `:unknown' rather than with an answer.  Either way a step that
;; fails to make progress is an error or an admission, never a silently
;; dropped subgoal.  `tl-exh-fuel' is the backstop behind both, not their
;; substitute.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-types)
(require 'termlisp-pattern)

(defvar tl-exh-fuel 8192
  "Steps `tl-exh-run' may take before giving up.
Each step is one question answered or one frame resumed.  The measure
check in `tl-exh--step' should make this unreachable; it exists
because a defence in depth costs one integer and a wrong termination
argument costs a hang.  Exceeding it signals rather than answering: a
coverage check that ran out of budget has proved nothing, and reading
that as coverage is exactly the failure this file exists to prevent.")

;;; The machine: a control form and a stack of plain frames
;;
;; The usefulness computation used to be a chain of closures: each
;; `tl-exh--useful*' built a frame holding a thunk to run and a
;; continuation to hand its answer to, and the driver applied whichever
;; of the two it got.  It was correct, and it was opaque.  The only way
;; to see what a frame was waiting for was to read the closure that
;; built it, so neither an exhausted budget nor an `:unknown' could say
;; which of them had run out -- and a frame could not be asked what it
;; was for without running it.
;;
;; Nothing here is a closure now.  Control is a list, a frame is a
;; list, and the machine's whole state at any step is one list and one
;; list of lists.  A frame is either
;;
;;   (wrap ANCESTORS KIND ARITY DATA)   rebuild a `:yes' witness
;;   (join ANCESTORS KIND PENDING UNKNOWN ENV MATRIX REST MEASURE TY)
;;                                      try the next alternative
;;
;; and ANCESTORS rides on both, as it did on the old frame, because the
;; sub-question a frame launched may have pushed an expansion the
;; enclosing one must not see.  A frame never re-enters itself: it
;; consumes an answer and yields either a finished answer or a
;; *smaller* question, so the stack cannot grow on the way back down.
;; That is the whole termination story, and it is the one
;; `tl-exh--measure' and `tl-exh-ancestors' already gave -- only now the
;; claim is visible in the frame instead of being true of a closure.

(defsubst tl-exh--answer-p (control)
  "Non-nil when CONTROL is an answer rather than a question.
An answer is `(STATUS . WITNESS)' with STATUS one of `:yes', `:no' or
`:unknown'; a question opens with the symbol `useful'.  The two can
never be confused, which is what lets the driver dispatch on a tag
instead of on a predicate whoever built the value would have had to
supply."
  (keywordp (car-safe control)))

(defvar tl-exh-ancestors nil
  "Column-type keys currently being expanded down the recursion path.
Bound by `tl-exh-run' around each step, never set globally.  A
constructor-set expansion pushes its column type here, and a repeat is
cut with `:unknown': an equirecursive datatype such as `Tree' would
otherwise ask whether `Tree' is covered, find that it is made of
`Tree's, and ask again forever.  The set only ever grows along a path,
so the path is bounded, and cutting with `:unknown' rather than with an
answer keeps the cut from being mistaken for a decision.")

(defun tl-exh-run (root &optional fuel)
  "Drive ROOT, a usefulness question, to an answer.
ROOT is `(useful ENV MATRIX SIG MEASURE ANCESTORS)'.  One step either
computes an answer or descends into a sub-question, pushing the frame
that will rebuild the answer when it comes back; an answer is handed to
the frame on top of the stack or, with the stack empty, is the result.
FUEL bounds the number of steps, and exceeding it signals rather than
answering: a coverage check that ran out of budget has proved nothing,
and reading that as coverage is exactly the failure this file exists to
prevent."
  (let ((fuel (or fuel tl-exh-fuel))
        (control root)
        (stack nil)
        (steps 0))
    (catch 'tl-exh-done
      (while (< steps fuel)
        (setq steps (1+ steps))
        (cond
         ((tl-exh--answer-p control)
          (if (null stack)
              (throw 'tl-exh-done control)
            (let* ((frame (pop stack))
                   ;; The frame resumes in the ancestors it was built
                   ;; in, not in whatever the sub-question pushed.
                   (tl-exh-ancestors (nth 1 frame))
                   (r (tl-exh--resume frame control stack)))
              (setq control (car r))
              (setq stack (cdr r)))))
         (t (let* ((tl-exh-ancestors (nth 5 control))
                   (r (tl-exh--step control stack)))
              (setq control (car r))
              (setq stack (cdr r))))))
      (signal 'termlisp-type-error
              (list (format "Coverage: fuel exhausted after %d steps" fuel))))))

;;; Answers
;;
;; An answer is `(STATUS . WITNESS)'.  STATUS is `:yes' (the vector is
;; useful), `:no' (it is not) or `:unknown' (undecided).  A witness is a
;; list of column witnesses, one per column, naming a value the query was
;; about; each column witness is `_' or `(con NAME COLUMN...)'.

(defsubst tl-exh--yes (witness)
  "Answer that the query matched, with the WITNESS that did it."
  (cons :yes witness))
(defsubst tl-exh--no ()
  "Answer that no row of the matrix reaches the query."
  (cons :no nil))
(defsubst tl-exh--unknown (witness)
  "Answer that the query could not be decided, with WITNESS so far.
WITNESS is nil where nothing has been pinned down; a caller must never
read this as `:yes' just because a witness came back with it."
  (cons :unknown witness))

(defun tl-exh--join (answers)
  "Fold ANSWERS, a list of `(STATUS . WITNESS)', into one answer.
`:yes' anywhere settles it; failing that a single `:unknown' makes the
whole undecided.  Propagation of `:unknown' lives only here and in the
two loops that remember it, so the rule that an undecided subgoal never
becomes a decision is stated in one place."
  (let ((yes (cl-find-if (lambda (a) (eq (car a) :yes)) answers))
        (unk (cl-find-if (lambda (a) (eq (car a) :unknown)) answers)))
    (cond (yes yes)
          (unk unk)
          (t (tl-exh--no)))))

;;; Pattern shapes
;;
;; These are the shapes `tl-pattern-parse' produces:
;;   (wild)  (var . N)  (lit V)  (rest . N)  (lam . N)
;;   (guard P E)  (or P...)  (and P...)  (con NAME P...)

(defun tl-exh--irrefutable-p (pat)
  "Non-nil when PAT matches every value of its type.
A variable, a wildcard and a `:lambda' binding each succeed on anything
offered, so each counts as covering the whole column.  A guard does not:
it can only make a clause match less."
  (memq (car-safe pat) '(wild var lam)))

(defun tl-exh--con-p (pat)
  "Non-nil when PAT is a constructor pattern, `(con NAME SUB...)'."
  (eq (car-safe pat) 'con))
(defun tl-exh--con-name (pat)
  "The constructor PAT names, or nil when PAT is not a constructor."
  (cadr pat))
(defun tl-exh--con-args (pat)
  "The subpatterns PAT applies its constructor to, possibly none."
  (cddr pat))

(defsubst tl-exh--col-pat (col)
  "The pattern of column COL, whose type is its second element.
Every column reader goes through this, so that the column's two-element
shape cannot be mistaken for the pattern's own list structure."
  (car col))

(defun tl-exh--zip (patterns types)
  "Pair PATTERNS with TYPES column-wise, padding the shorter with nil.
A column is the two-element list (PATTERN TYPE), never a dotted pair:
a pattern is itself a list, so `(PATTERN . TYPE)' would splice the type
onto the pattern's own arguments and every composite pattern would read
one field too many."
  (let ((out nil))
    (while (or patterns types)
      (push (list (car patterns) (car types)) out)
      (setq patterns (cdr patterns) types (cdr types)))
    (nreverse out)))

(defun tl-exh--wild-columns (n types)
  "N irrefutable columns carrying TYPES."
  (tl-exh--zip (make-list n '(wild)) types))

(defun tl-exh--expand-or (pat)
  "Flatten PAT's `or' alternatives into a list, or nil when PAT is not one."
  (when (eq (car-safe pat) 'or)
    (cl-mapcan (lambda (p) (or (tl-exh--expand-or p) (list p)))
               (cdr pat))))

(defun tl-exh--expand-row (row)
  "Rows equivalent to ROW with every `or' pattern expanded away.
An `or' in a column matches the union of its alternatives, so a row
carrying one stands for one row per choice -- the cartesian product over
the columns that have one.  Expanding once, out here, is what lets the
recursion ask about a single pattern per column instead of re-deriving at
every step what a row whose column held a union could match.  The product
can grow with the number of alternatives, and `tl-exh-fuel' bounds the
work if it ever grows too far."
  (let ((rows (list nil)))
    (dolist (col row)
      (let ((pat (tl-exh--col-pat col)))
        (let ((alts (or (tl-exh--expand-or pat) (list pat))))
          (setq rows
                (mapcan (lambda (prefix)
                          (mapcar (lambda (alt)
                                    (append prefix (list (list alt (cadr col)))))
                                  alts))
                        rows)))))
    rows))

(defun tl-exh--normalize-and (pat)
  "Return a pattern equivalent to PAT, or nil when none is available.
Only reductions preserving the value set exactly are performed: dropping
an irrefutable conjunct, merging constructors of one head position by
position, and collapsing a repeated variable.  Anything else has no
equivalent in this pattern language, and inventing one would either
invent coverage or discard it, so the caller reports `:unknown'."
  (if (not (eq (car-safe pat) 'and))
      pat
    (let* ((flat (cl-mapcan (lambda (p)
                              (or (and (eq (car-safe p) 'and) (cdr p)) (list p)))
                            (cdr pat))))
      (cond
       ;; An irrefutable conjunct constrains nothing, so the remaining
       ;; conjuncts decide the value set on their own.
       ((cl-some #'tl-exh--irrefutable-p flat)
        (let ((rest (cl-remove-if #'tl-exh--irrefutable-p flat)))
          (cond ((null rest) (list 'wild))
                ((null (cdr rest)) (car rest))
                (t (tl-exh--normalize-and (cons 'and rest))))))
       ((not (cl-every #'tl-exh--con-p flat)) nil)
       (t (let ((head (tl-exh--con-name (car flat)))
                (arity (length (tl-exh--con-args (car flat))))
                (ok t))
            (if (not (cl-every (lambda (p)
                                 (and (eq (tl-exh--con-name p) head)
                                      (= (length (tl-exh--con-args p)) arity)))
                               flat))
                nil
              (let ((merged
                     (cl-loop for i below arity
                              collect
                              (let ((subs (mapcar (lambda (p)
                                                    (nth i (tl-exh--con-args p)))
                                                  flat)))
                                (if (cl-every (lambda (s) (equal s (car subs)))
                                              subs)
                                    (car subs)
                                  (setq ok nil)
                                  nil)))))
                (when ok
                  (let ((final (tl-exh--normalize-and (cons 'and merged))))
                    (and final (cons 'con (cons head final)))))))))))))

;;; The termination measure
;;
;; Maranget's recursion terminates because every step shrinks the
;; signature -- except when it expands a constructor set, where one
;; wildcard column becomes that constructor's field columns and the
;; measure grows.  That branch is bounded by the ancestor set instead.

;; The expansion path again, in the section that uses it.  The variable
;; itself and its rationale are with the driver, where it is bound
;; around each step and never set globally.

(defun tl-exh--pat-size (pat)
  "Size of PAT, counting every subpattern it contains.
An `or' or `and' is larger than each of its parts, so replacing one by a
part strictly decreases; a constructor is larger than each of its
fields, so specialising one strictly decreases too."
  (pcase (car-safe pat)
    ('con (+ 1 (apply #'+ (mapcar #'tl-exh--pat-size (cddr pat)))))
    ('or (+ 1 (apply #'+ (mapcar #'tl-exh--pat-size (cdr pat)))))
    ('and (+ 1 (apply #'+ (mapcar #'tl-exh--pat-size (cdr pat)))))
    ('guard (+ 1 (tl-exh--pat-size (cadr pat))))
    (_ 1)))

(defun tl-exh--measure (sig)
  "Sum of the sizes of SIG's patterns.
This is the multiset the algorithm decreases.  It reads patterns alone,
never types, so an equirecursive datatype cannot make it grow: the
recursion descends into a type only when a pattern descends with it."
  (apply #'+ (mapcar (lambda (col) (tl-exh--pat-size (car col))) sig)))

(defun tl-exh--check-decrease (measure sig)
  "Signal unless SIG's measure is strictly below MEASURE.
A step that fails to make progress is an error rather than a skipped
subgoal: silently dropping it would let the enclosing query conclude
from a subgoal that was never answered."
  (let ((m (tl-exh--measure sig)))
    (when (>= m measure)
      (signal 'termlisp-type-error
              (list (format "Coverage: step made no progress (measure %d -> %d)"
                            measure m))))
    m))

(defun tl-exh--already-expanded-p (ty)
  "Non-nil when TY's key is on the current expansion path.
This is the equirecursive cut: `Tree' is made of `Tree's, so asking
whether a wildcard at `Tree' is covered expands into the very same
question, and no amount of shrinking the pattern will end that.  The
answer is `:unknown', not `:no', because nothing here has shown the
column covered."
  (and (tl-tcon-p ty) (member (tl-canonical-key ty) tl-exh-ancestors)))

(defun tl-exh--push-expansion (ty ancestors)
  "ANCESTORS with TY's key recorded, when TY has one.
The key is pushed for the duration of one constructor-set expansion, so
two sibling constructors of one type are independent while a nested
expansion of the same type is the repeat `tl-exh--already-expanded-p'
guards.  The result rides on the frame rather than being bound around
the call: a frame is built now and stepped later, and by then any
dynamic extent is gone."
  (if (tl-tcon-p ty) (cons (tl-canonical-key ty) ancestors) ancestors))

;;; Types of the columns
;;
;; Coverage is a question about a type: which constructors can appear in
;; a column decides whether a match there can be complete.

(defun tl-exh--field-types (ty)
  "The argument types of TY's arrows, outermost first."
  (let ((fields nil))
    (while (tl-tfun-args ty)
      (push (car (tl-tfun-args ty)) fields)
      (setq ty (cadr (tl-tfun-args ty))))
    (nreverse fields)))

(defun tl-exh--result-type (ty)
  "Strip TY's arrows, leaving the result."
  (while (tl-tfun-args ty)
    (setq ty (cadr (tl-tfun-args ty))))
  ty)

(defun tl-exh--absorbs-p (got wanted)
  "Non-nil when GOT, a constructor's type component, can stand at WANTED.
This is unification restricted to a yes-or-no answer, performed by
walking the two side by side rather than by binding anything: a check
must not leave a trail in the type graph.  A component that is either
side's free variable absorbs whatever it meets, because the constraint
would be discharged by binding that variable.  A component that is two
different constructors meeting head on -- `Zero' against `Succ k' --
cannot, and that is what pins an indexed family to the indices its
constructors actually reach."
  (let ((a (tl-type-deref got))
        (b (tl-type-deref wanted)))
    (cond
     ((or (not (tl-tcon-p a)) (not (tl-tcon-p b)))
      ;; At least one side is a bare type variable, which is free to
      ;; become whatever the other side demands.
      t)
     ((not (eq (tl-tcon-name a) (tl-tcon-name b))) nil)
     (t (let ((xa (tl-tcon-args a)) (xb (tl-tcon-args b)))
          (if (not (= (length xa) (length xb)))
              nil
            (cl-every #'tl-exh--absorbs-p xa xb)))))))

(defun tl-exh--ctor-info (env ctor result-type)
  "Return `(FIELD-TYPES . RESULT)' for CTOR applied at RESULT-TYPE, or nil.
CTOR's scheme is the one registered in ENV, instantiated by RESULT-TYPE's
own arguments, so a family whose index is a variable still admits the
constructors that could reach it, while one whose index is concrete
excludes those that cannot.  At `Vec Int Zero' the substituted result of
`VCons' is `Vec Int (Succ k)', which cannot stand there, so the single
constructor `VNil' is the whole story; at `Vec a n', with the index
unknown, both are admitted, which is the honest answer because either
could be what the caller meant."
  (let* ((sc (gethash ctor (tl-env-type-env env)))
         (ty (and sc (tl-tscheme-type sc)))
         (vars (and sc (tl-tscheme-vars sc))))
    (when ty
      (let* ((args (tl-tcon-args (tl-type-deref result-type)))
             (inst (if (and args (= (length args) (length vars)))
                       (tl-type-subst ty (cl-mapcar #'cons vars args))
                     ty))
             (res (tl-exh--result-type inst)))
        (when (or (null res) (tl-exh--absorbs-p res result-type))
          (cons (tl-exh--field-types inst) res))))))

(defun tl-exh--constructors-of (env type)
  "Applicable constructors of TYPE in ENV, as `(NAME FIELD-TYPES RESULT)' entries.
The symbol `:open' means TYPE's constructors are not enumerable -- an
`open' datatype, `Int', `String', a bare type variable.  That is a
different answer from \"none apply\" and must never be confused with it:
a column whose constructors cannot be listed cannot be shown covered by
enumerating them, so it takes the incomplete branch of the recursion and
so can never prove coverage by itself."
  (let* ((d (tl-type-deref type))
         (name (and (tl-tcon-p d) (tl-tcon-name d)))
         (spec (and name (gethash name (tl-env-datatypes env)))))
    (if (or (null spec) (plist-get spec :open))
        :open
      (let ((declared (plist-get spec :constructors))
            (out nil))
        (dolist (c declared)
          (let ((info (tl-exh--ctor-info env c d)))
            (when info
              (push (list c (car info) (cdr info)) out))))
        ;; A closed datatype yielding no applicable constructor is
        ;; uninhabited at this type -- `Void', or an index nothing
        ;; reaches -- and so vacuously covered.  But a datatype that
        ;; declares constructors and resolves none is far likelier to be
        ;; this checker failing to instantiate them, and "uninhabited" is
        ;; precisely the reading that would wave a bad match through.
        ;; Report `:open' instead: undecided, never covered.
        (if (and declared (null out)) :open (nreverse out))))))

;;; Matrix operations

(defun tl-exh--specialize (matrix name arity types)
  "Rows of MATRIX whose column 0 can match constructor NAME, expanded.
The column NAME occupies becomes its ARITY field columns, carrying
TYPES.  An irrefutable row is kept and padded with wildcards; a row led
by a different constructor cannot match NAME and is dropped, which is
the whole point of specialising."
  (let ((out nil))
    (dolist (row matrix (nreverse out))
      (let* ((pat (tl-exh--col-pat (car row)))
             (rest (cdr row)))
        (cond
         ((tl-exh--con-p pat)
          (when (eq (tl-exh--con-name pat) name)
            (push (append (tl-exh--zip (tl-exh--con-args pat) types) rest)
                  out)))
         ((tl-exh--irrefutable-p pat)
          (push (append (tl-exh--wild-columns arity types) rest) out)))))))

(defun tl-exh--default (matrix)
  "Rows of MATRIX whose column 0 is irrefutable, with that column dropped.
A row led by a constructor covers only that constructor's values and so
says nothing about the rest of the type; dropping it is what makes the
remaining rows the ones that cover the whole column."
  (let ((out nil))
    (dolist (row matrix (nreverse out))
      (when (tl-exh--irrefutable-p (tl-exh--col-pat (car row)))
        (push (cdr row) out)))))

(defun tl-exh--mentioned (matrix)
  "Constructors named in MATRIX's first column."
  (let ((out nil))
    (dolist (row matrix (nreverse out))
      (let ((pat (tl-exh--col-pat (car row))))
        (when (tl-exh--con-p pat)
          (cl-pushnew (tl-exh--con-name pat) out))))))

(defun tl-exh--witness (sig)
  "A column witness for each column of SIG, naming exactly what it covers."
  (mapcar (lambda (col)
            (let ((pat (car col)))
              (cond
               ((tl-exh--con-p pat)
                (cons 'con
                      (cons (tl-exh--con-name pat)
                            (make-list (length (tl-exh--con-args pat)) '_))))
               ((eq (car-safe pat) 'lit) (list 'lit (cadr pat)))
               (t '_))))
          sig))

;;; The usefulness computation

(defun tl-exh--step (control stack)
  "Take one step of the question CONTROL, with STACK beneath it.
Return `(NEW-CONTROL . NEW-STACK)'.  A step either answers outright --
the two base cases, where the matrix or the signature has run out --
or picks the first column apart and descends, pushing the frame that
will rebuild the answer.  What it never does is hand an answer to
anyone: that is `tl-exh--resume''s job, and keeping the two apart is
what makes the machine readable one function at a time."
  (let* ((env (nth 1 control))
         (matrix (nth 2 control))
         (sig (nth 3 control))
         (measure (nth 4 control))
         (ancestors (nth 5 control)))
    (cond
     ;; No row stands, so nothing covers SIG.
     ((null matrix) (cons (tl-exh--yes (tl-exh--witness sig)) stack))
     ;; SIG is fully specified and a row stands, so SIG is matched.
     ((null sig) (cons (tl-exh--no) stack))
     (t (let* ((col (car sig))
               (pat (tl-exh--col-pat col))
               (ty (cadr col))
               (rest (cdr sig)))
          (cond
           ((tl-exh--con-p pat)
            (tl-exh--step-con env matrix col rest measure ancestors stack))
           ((eq (car-safe pat) 'lit)
            (tl-exh--step-lit env matrix pat rest measure ancestors stack))
           ((eq (car-safe pat) 'or)
            (tl-exh--step-or env matrix (tl-exh--expand-or pat) rest
                             measure ancestors stack))
           ((eq (car-safe pat) 'and)
            (let ((norm (tl-exh--normalize-and pat)))
              (if (not norm)
                  (cons (tl-exh--unknown nil) stack)
                (let* ((sig2 (cons norm rest))
                       (m2 (tl-exh--measure sig2)))
                  ;; Normalisation is expected to shrink the pattern.
                  ;; One that does not has not simplified the question at
                  ;; all, and asking it again would spin, so this admits
                  ;; it cannot decide rather than repeating itself or
                  ;; claiming the conjunction settles something it left
                  ;; alone.
                  (if (>= m2 measure)
                      (cons (tl-exh--unknown nil) stack)
                    (cons (list 'useful env matrix sig2 m2 ancestors)
                          stack))))))
           ((tl-exh--irrefutable-p pat)
            (tl-exh--step-default env matrix ty rest measure ancestors stack))
           ;; `guard' and `rest' have no meaning in a column: a guard is a
           ;; runtime predicate this checker cannot evaluate, and `rest'
           ;; addresses a sibling list rather than a value.  Neither may
           ;; contribute a decision.
           (t (cons (tl-exh--unknown nil) stack))))))))

(defun tl-exh--step-con (env matrix col rest measure ancestors stack)
  "Descend by COL's constructor, with STACK beneath it.
COL's type is looked up in ENV, and may not resolve -- an `open'
datatype, a variable -- in which case the field types are unknown and
the recursion below simply cannot enumerate, which yields `:unknown'
rather than a guess.  MATRIX is specialised to the rows that can hold
this constructor, which is what makes the question smaller.  No
ancestor is pushed here: specialising by a constructor the pattern
already names shrinks that pattern, so the measure alone bounds it.
The frame waits with the constructor's name and arity, since that is
what the answer's witness has to be rebuilt into."
  (let* ((pat (tl-exh--col-pat col))
         (name (tl-exh--con-name pat))
         (subs (tl-exh--con-args pat))
         (ty (cadr col))
         (arity (length subs))
         (ctors (tl-exh--constructors-of env ty))
         (info (and (listp ctors) (cl-find name ctors :key #'car)))
         (fields (nth 1 info))
         (types (if (and fields (= (length fields) arity))
                    fields
                  (make-list arity nil)))
         (sig (append (tl-exh--zip subs types) rest)))
    (tl-exh--check-decrease measure sig)
    (cons (list 'useful env (tl-exh--specialize matrix name arity types)
                sig (tl-exh--measure sig) ancestors)
          (cons (list 'wrap ancestors 'con arity name) stack))))

(defun tl-exh--step-lit (env matrix pat rest measure ancestors stack)
  "Descend past a literal PAT, with STACK beneath it.
MATRIX keeps only the rows that can hold this exact value, which are
rows led by the same literal or by anything irrefutable -- that is the
whole of the restriction, and it is what makes the question smaller.
ENV is passed down to the recursion, which needs it to read the
constructors of every column beside this one.  Literals are never
enumerable as a type, so an all-literal column always reaches the
incomplete branch and so can never be shown complete."
  (let* ((value (cadr pat))
         (sig rest)
         (m (cl-remove-if-not
             (lambda (row)
               (let ((c (tl-exh--col-pat (car row))))
                 (or (tl-exh--irrefutable-p c)
                     (and (eq (car-safe c) 'lit) (equal (cadr c) value)))))
             matrix)))
    (tl-exh--check-decrease measure sig)
    (cons (list 'useful env m sig (tl-exh--measure sig) ancestors)
          (cons (list 'wrap ancestors 'lit nil value) stack))))

(defun tl-exh--step-or (env matrix alts rest measure ancestors stack)
  "Descend into ALTS in turn, with STACK beneath it.
Alternatives are independent questions about the same MATRIX, and ENV
is passed to each unchanged, so one `:yes' settles the lot.  The join
frame waits for each in turn; an `:unknown' settles nothing but is
remembered, because if no alternative proves useful and at least one
was undecided the honest answer is that the question is undecided, not
that it is answered."
  (if (null alts)
      (cons (tl-exh--no) stack)
    (let* ((alt (car alts))
           (sig (cons alt rest)))
      (tl-exh--check-decrease measure sig)
      (cons (list 'useful env matrix sig (tl-exh--measure sig) ancestors)
            (cons (list 'join ancestors 'or (cdr alts) nil
                        env matrix rest measure nil)
                  stack)))))

(defun tl-exh--step-default (env matrix ty rest measure ancestors stack)
  "Descend from an irrefutable column at TY, with STACK beneath it.
This is the branch that decides whether a match can be complete at
all, and it goes two ways.  ENV says which constructors TY has.  When
every one of them is named somewhere in MATRIX, whether each one's
fields are covered is a finite question, asked once per constructor.
When some constructor is not named, coverage rests solely on the rows
that make no demand of the column, so the question falls through to
`D(P)' over the remaining columns."
  (let* ((ctors (tl-exh--constructors-of env ty))
         (openp (not (listp ctors)))
         (mentioned (tl-exh--mentioned matrix))
         (absent (unless openp
                   (cl-remove-if (lambda (c) (memq (car c) mentioned)) ctors))))
    (cond
     ((or openp absent)
      ;; A value led by a constructor no row mentions is one no row can
      ;; match, so the forgotten constructor goes in front of the witness
      ;; the remainder produces.  With no constructor to name -- an `Int'
      ;; column, or a variable -- a wildcard stands in its place.  That
      ;; says the same thing less usefully, which is the whole of what is
      ;; known there, and rendering nothing at all would come out as an
      ;; empty witness rather than as the blank it is.
      (let ((sig rest)
            (head (if absent
                      (let ((c (car absent)))
                        (cons 'con (cons (car c)
                                         (make-list (length (nth 1 c)) '_))))
                    '_)))
        (tl-exh--check-decrease measure sig)
        (cons (list 'useful env (tl-exh--default matrix) sig
                    (tl-exh--measure sig) ancestors)
              (cons (list 'wrap ancestors 'head nil head) stack))))
     ;; Every constructor is named, so this expansion asks the same shape
     ;; of question about each of their fields.  That is where an
     ;; equirecursive datatype would ask about `Tree' by asking about
     ;; `Tree', and the ancestor set is what ends it.
     ((tl-exh--already-expanded-p ty) (cons (tl-exh--unknown nil) stack))
     (t (tl-exh--step-ctors env matrix ctors ty rest measure ancestors stack)))))

(defun tl-exh--step-ctors (env matrix ctors ty rest measure ancestors stack)
  "Descend into the constructors of TY in turn, with STACK beneath it.
CTORS is a list of `(NAME FIELDS RESULT)', the constructors of TY as
ENV reports them; each is a separate question about a copy of MATRIX
specialised to that constructor, so one `:yes' settles the lot and an
undecided one is merely remembered.  TY is recorded as expanded for the
duration, which is what bounds a recursive datatype.  MEASURE is
accepted to keep the signature uniform but deliberately not consulted,
for the reason below: this is the one branch where a wildcard column
becomes the constructor's field columns, so the measure is expected to
grow, and the pushed ancestors are what bound it."
  (ignore measure)
  (let ((pushed (tl-exh--push-expansion ty ancestors)))
    (if (null ctors)
        (cons (tl-exh--no) stack)
      (let* ((c (car ctors))
             (name (car c))
             (fields (nth 1 c))
             (arity (length fields))
             (sig (append (tl-exh--wild-columns arity fields) rest)))
        (cons (list 'useful env (tl-exh--specialize matrix name arity fields)
                    sig (tl-exh--measure sig) pushed)
              ;; The sub-question is asked about the constructor's
              ;; fields, so its witness is a witness for them and says
              ;; nothing about the constructor.  The wrap above the join
              ;; puts the name back before the join ever reads the
              ;; answer; above it, because a frame answers to the one on
              ;; top of it, and the join must see the answer rebuilt.
              ;; It sits above the join for the other reason the machine
              ;; keeps the two apart: a rebuild is not a decision, and
              ;; only the join is allowed to make one.
              (cons (list 'wrap pushed 'con arity name)
                    (cons (list 'join pushed 'ctors (cdr ctors) nil
                                env matrix rest measure ty)
                          stack)))))))

(defun tl-exh--resume (frame answer stack)
  "Hand ANSWER to FRAME, with STACK beneath it.
Return `(NEW-CONTROL . NEW-STACK)'.  A frame consumes an answer and
yields either that answer rebuilt or a *smaller* question -- never the
one it was waiting on -- so a frame cannot re-enter itself and the
stack cannot grow on the way back down.  That is the whole termination
argument, and it is now a property of two data shapes rather than of
whatever the closures happened to have captured."
  (pcase (car frame)
    ;; Rebuild a `:yes' witness and pass everything else through
    ;; untouched: `:no' carries no witness and `:unknown' must keep the
    ;; one it reached on its own, un-rebuilt, or a caller reading it
    ;; would be reading a claim this frame added.
    ('wrap
     (cons (if (eq (car answer) :yes)
               (tl-exh--yes (tl-exh--wrap-witness frame (cdr answer)))
             answer)
           stack))
    ('join
     (let ((kind (nth 2 frame))
           (pending (nth 3 frame))
           (unknown (nth 4 frame))
           (env (nth 5 frame))
           (matrix (nth 6 frame))
           (rest (nth 7 frame))
           (measure (nth 8 frame))
           (ty (nth 9 frame))
           (ancestors (nth 1 frame)))
       (cond
        ;; One alternative proved useful and that settles the lot.
        ((eq (car answer) :yes) (cons answer stack))
        (t
         (when (eq (car answer) :unknown) (setq unknown (cdr answer)))
         (if (null pending)
             (cons (if unknown (tl-exh--unknown unknown) (tl-exh--no)) stack)
           (if (eq kind 'or)
               (tl-exh--step-or env matrix pending rest measure ancestors stack)
             (tl-exh--step-ctors env matrix pending ty rest measure
                                 ancestors stack)))))))
    ;; A frame is one of those two.  Anything else means the machine
    ;; state was corrupted, and answering from it would be a coverage
    ;; claim that no computation produced.
    (_ (signal 'termlisp-type-error
               (list (format "Coverage: unknown frame %S" (car frame)))))))

(defun tl-exh--wrap-witness (frame witness)
  "Rebuild WITNESS with FRAME's column standing in front of it.
There are three shapes and the difference between them is the point of
having a KIND.  A literal, and an irrefutable column's forgotten
constructor -- or the `_' that stands in when there is none -- each
stand for the whole column and simply go in front.  A constructor's
witness is unlike them: the sub-question was asked about the
constructor's *fields*, so the first ARITY entries of WITNESS belong
inside the constructor and the rest stand after it.  Splicing them in
by hand at every call site is how this used to be spelled, and getting
the arity wrong there moved a witness column without saying so."
  (let ((kind (nth 2 frame))
        (arity (nth 3 frame))
        (data (nth 4 frame)))
    (cond
     ((eq kind 'con)
      (append (list (cons 'con (cons data (cl-subseq witness 0 arity))))
              (cl-subseq witness arity)))
     ((eq kind 'lit) (cons (list 'lit data) witness))
     (t (cons data witness)))))

(defun tl-exh--useful-col (env matrix sig)
  "Answer whether SIG is useful against MATRIX in ENV, running the machine."
  (tl-exh-run (list 'useful env matrix sig (tl-exh--measure sig)
                    tl-exh-ancestors)))

;;; Queries

(defun tl-exh-exhaustive (env rows types)
  "Ask whether ROWS covers every value at TYPES in ENV.
Return `(STATUS . WITNESS)'.  `:no' means the rows are exhaustive;
`:yes' means they are not, and WITNESS names a value no row matches;
`:unknown' means the question could not be decided.  The query vector is
one irrefutable column per parameter, so \"useful\" reads as \"there is
something left uncovered\"."
  (tl-exh--useful-col
   env
   (mapcan #'tl-exh--expand-row rows)
   (tl-exh--wild-columns (length types) types)))

(defun tl-exh-redundant (env rows)
  "Indices, most recent first, of ROWS in ENV that cannot match anything new.
A row is redundant when every value it matches is already matched by the
rows before it.  An `or' is expanded first, exactly as the
exhaustiveness query expands it, so a row carrying a union is credited
with covering each of its alternatives rather than with covering none of
them; one alternative still reachable is enough to keep the row.  Rows
the checker cannot reason about -- guarded ones, ones carrying `rest'
patterns -- are never reported, because an undecided question is not
evidence of redundancy."
  (let ((acc nil)
        (above nil)
        (i 0))
    (dolist (row rows)
      ;; A clause keeps its own index however many rows its alternatives
      ;; expand to, so the report names what the user wrote.
      (let ((variants (tl-exh--expand-row row)))
        (unless (cl-some (lambda (variant)
                           (not (eq (car (tl-exh--useful-col env above variant))
                                    :no)))
                         variants)
          (push i acc))
        (setq above (append above variants))
        (setq i (1+ i))))
    acc))

;;; Reporting

(cl-defstruct (tl-exh-report (:constructor tl-exh-report--make))
  "What a coverage check found for one definition.
MISSING lists column witnesses for values no clause reaches, REDUNDANT
lists clause indices nothing new can match, and UNKNOWDS records the
columns where the checker could not decide.  The last is kept separate
on purpose: a caller wanting a coverage guarantee must see where the
guarantee stopped rather than find it silently widened."
  missing redundant unknowns name)

(defun tl-exh--render (col)
  "Render one column witness COL as surface syntax.
Wildcards print as `_'; a literal prints as itself; a constructor prints
applied to its fields.  The witness is the whole value of the message --
it names the case the program forgot -- so it is rendered rather than
dumped as compiled patterns."
  (cond ((not (consp col)) '_)
        ((eq (car col) 'lit) (cadr col))
        ((eq (car col) 'con)
         ;; `col' is (con NAME SUB...), so the sub-column witnesses start
         ;; after the name: taking `cdr' would render the name as one of
         ;; its own arguments and print an extra wildcard for it.
         (let ((args (mapcar #'tl-exh--render (cddr col))))
           (if args (cons (cadr col) args) (cadr col))))
        (t '_)))

(defun tl-exh-redundant-list (report)
  "Redundant clause indices in REPORT, in source order."
  (reverse (tl-exh-report-redundant report)))

(defun tl-exh-report-lines (report)
  "Human-readable lines describing REPORT, empty when it found nothing."
  (let ((lines nil))
    (when (tl-exh-report-missing report)
      (push (format "%s: match is not exhaustive; no case for %s"
                    (tl-exh-report-name report)
                    (mapconcat (lambda (witness)
                                 (mapconcat (lambda (col)
                                              (format "%S" (tl-exh--render col)))
                                            witness " "))
                               (tl-exh-report-missing report)
                               " or "))
            lines))
    (dolist (i (tl-exh-redundant-list report))
      (push (format "%s: clause %d is unreachable"
                    (tl-exh-report-name report) (1+ i))
            lines))
    (when (tl-exh-report-unknowns report)
      (push (format "%s: coverage undecidable here (%s)"
                    (tl-exh-report-name report)
                    (mapconcat #'identity (tl-exh-report-unknowns report) "; "))
            lines))
    (nreverse lines)))

(defun tl-exh-analyze (env name rows types)
  "Check the clauses ROWS of NAME at TYPES in ENV.
Return a `tl-exh-report'.  Guarded rows are never credited with covering
anything, because a guard is a runtime predicate that can only make a
clause match less: counting one as covering would credit the program with
cases its guards reject.  They need no special handling here -- a guard in
a column is neither a constructor nor irrefutable, so both `S' and `D'
already drop such a row."
  (let ((ex (tl-exh-exhaustive env rows types))
        (red (tl-exh-redundant env rows))
        (guarded (cl-count-if (lambda (row)
                                (cl-some (lambda (col)
                                           (eq (car-safe (car col)) 'guard))
                                         row))
                              rows)))
    (tl-exh-report--make
     :name name
     :missing (and (eq (car ex) :yes) (list (cdr ex)))
     :redundant red
     :unknowns (delq nil
                     (list (and (eq (car ex) :unknown) "the checker could not enumerate this type")
                           (and (> guarded 0)
                                (format "%d clause%s guarded, so the guard is never known to hold"
                                        guarded (if (= guarded 1) "" "s"))))))))

(defun tl-check-exhaustiveness (env name rows types)
  "Signal unless the clauses ROWS of NAME at TYPES cover ENV's type.
Both non-exhaustive matches and unreachable clauses are errors, and so
is an undecidable column: this entry point exists for callers who want
the guarantee, and a guarantee that quietly shrinks where the checker
loses its footing is not one.  The runtime is the second line of
defence behind this check -- `tl-match' signals \"No matching clause\"
for a value no clause reaches -- so a miss this checker does not catch
still fails loudly rather than silently taking another branch."
  (let ((report (tl-exh-analyze env name rows types)))
    (when (or (tl-exh-report-missing report)
              (tl-exh-report-redundant report)
              (tl-exh-report-unknowns report))
      (signal 'termlisp-type-error
              (list (mapconcat #'identity (tl-exh-report-lines report) "; "))))
    report))

(defun tl-exh-check-one (env name type)
  "Coverage-check the clauses of NAME, whose registered type is TYPE in ENV.
The parameter types come from TYPE's arrows, which is the only place
they are known and the reason the check cannot run any earlier."
  (let ((clauses (gethash name (tl-env-clauses env)))
        (argtypes (tl-exh--field-types type)))
    ;; The pattern count must match the arrow count, or the types being
    ;; checked against are not the ones the patterns were read at -- an
    ;; indexed signature whose binders went implicit, say.  Checking
    ;; anyway would report coverage of a type the function does not have,
    ;; so the check is skipped rather than misaimed.
    (when (and clauses
               (cl-every (lambda (c) (= (length (car c)) (length argtypes)))
                         clauses))
      (let ((ctor-p (lambda (s) (gethash s (tl-env-constructors env)))))
        (tl-check-exhaustiveness
         env name
         ;; Each row is a list of (PATTERN TYPE) columns.  The types are
         ;; what the recursion reads to decide which constructors a
         ;; column can hold at all, so a row of bare patterns would be
         ;; answering a question about values it cannot tell apart.
         (mapcar (lambda (clause)
                   (tl-exh--zip
                    (mapcar (lambda (p) (tl-pattern-parse p ctor-p))
                            (car clause))
                    argtypes))
                 clauses)
         argtypes)))))

(defun tl-exh-check-batch (announced)
  "Coverage-check every definition in ANNOUNCED, once per name.
ANNOUNCED is `tl-coverage-announcements': (ENV NAME TYPE) entries in
definition order.  A function defined clause by clause appears there
once per clause, and only the last of those sees all of them, so the
earlier entries are dropped rather than checked against a
half-written function."
  (let ((latest (make-hash-table :test #'eq)))
    (dolist (entry announced)
      (puthash (nth 1 entry) entry latest))
    (maphash (lambda (_ entry)
               (tl-exh-check-one (nth 0 entry) (nth 1 entry) (nth 2 entry)))
             latest)))

(defun tl-exh--install ()
  "Make `tl-exh-check-batch' the post-batch hook.
Installed here rather than required from `termlisp-types', because this
file already depends on that one; installing rather than being installed
is the same shape as `termlisp-nbe' supplying `tl-unify-reduce'."
  (setq tl-post-batch-hook #'tl-exh-check-batch))

(tl-exh--install)

(provide 'termlisp-exhaust)
;;; termlisp-exhaust.el ends here
