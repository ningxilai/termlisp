;;; setup-typed.el --- A typed setup DSL (cl-lib-only, composite types, comp-aware) -*- lexical-binding: t; -*-

;;; Commentary:
;;
;; Prototype replacement for your `setup.el'. This file:
;;  - does not require EIEIO;
;;  - builds a type registry from builtin sorts and `comp-known-predicates' when present;
;;  - supports composite type descriptors: (list-of X), (or X Y), (and X Y), (maybe X), (literal V);
;;  - performs type checks at macro-expansion time;
;;  - keeps the original keyword registry API (setup-define) and the IR/emitter
;;    shape compatible with your existing setup.el; it is intended as a drop-in
;;    replacement after you verify it with the provided tests.
;;
;;; Notes:
;;  - This file defines the macro `setup-typed' (so it won't hijack your current
;;    `setup' automatically). After you validate it, we can rename it to `setup'
;;    and replace the repository file.
;;  - Composite type handling is intentionally conservative: it compiles
;;    descriptors into predicate functions evaluated at macro-expansion time.
;;
;;; Code:

(require 'cl-lib)
(require 'subr-x)

;;;; Errors

(define-error 'setup-error "Setup error")

;;;; Type registry and composite type constructors -------------------------

(defvar setup--type-table (make-hash-table :test #'eq)
  "Mapping from type symbol -> predicate function (fn of one arg).")

(defun setup--define-type (name pred)
  "Register type NAME with predicate function PRED.
PRED can be a function or a symbol naming a function. Returns NAME."
  (puthash name (if (symbolp pred) (symbol-function pred) pred)
           setup--type-table)
  name)

(defun setup--get-raw-pred (name)
  "Return predicate function for type NAME, or nil if unknown.
This looks up `setup--type-table'."
  (gethash name setup--type-table))

(defun setup--build-type-table ()
  "Populate `setup--type-table' from builtin sorts and comp-known-predicates.
Safe to call multiple times." 
  (clrhash setup--type-table)
  (let ((builtin
         `((Feature  . (lambda (v) (and v (symbolp v))))
           (Mode     . (lambda (v) (and v (symbolp v))))
           (Map      . (lambda (v) (and v (or (symbolp v) (consp v)))))
           (Hook     . (lambda (v) (and v (symbolp v))))
           (Function . (lambda (v) (or (symbolp v)
                                       (and (consp v) (memq (car v) '(quote function lambda))))))
           (Key      . (lambda (v) (or (stringp v) (vectorp v))))
           (Boolean  . (lambda (v) (memq v '(t nil))))
           (Number   . #'numberp)
           (Text     . #'stringp)
           (Opaque   . (lambda (_) t)))))
    (dolist (p builtin)
      (setup--define-type (car p) (cdr p)))

    ;; Integrate comp-known-predicates when available: expose each predicate symbol as a type
    (when (and (boundp 'comp-known-predicates) comp-known-predicates)
      (condition-case _
          (progn
            (cond
             ((listp comp-known-predicates)
              (dolist (entry comp-known-predicates)
                (let ((sym (cond
                            ((symbolp entry) entry)
                            ((consp entry) (car entry))
                            (t nil))))
                  (when (and sym (fboundp sym))
                    (unless (setup--get-raw-pred sym)
                      (setup--define-type sym sym))))))
             (t nil)))
        (error nil)))))

;; initialize
(setup--build-type-table)

(defun setup--make-pred (sort)
  "Return a predicate function for SORT.
SORT may be:
  - a symbol naming a registered type or a predicate symbol
  - a function (used directly)
  - a composite descriptor: (list-of X), (or X Y...), (and X Y...), (maybe X), (literal V)
The returned predicate is a function of one argument.
"
  (cond
   ;; direct function
   ((functionp sort) sort)
   ;; symbol -> lookup in table or fallback to symbol-function
   ((symbolp sort)
    (or (setup--get-raw-pred sort)
        (and (fboundp sort) (symbol-function sort))
        (lambda (_v) (signal 'setup-error (list (format "Unknown type/predicate: %S" sort))))))
   ;; composite descriptors
   ((consp sort)
    (pcase (car sort)
      ('list-of
       (let ((sub (setup--make-pred (cadr sort))))
         (lambda (v) (and (listp v) (cl-every sub v)))))
      ('maybe
       (let ((sub (setup--make-pred (cadr sort))))
         (lambda (v) (or (null v) (funcall sub v)))) )
      ('or
       (let ((subs (mapcar #'setup--make-pred (cdr sort))))
         (lambda (v) (cl-some (lambda (p) (funcall p v)) subs))))
      ('and
       (let ((subs (mapcar #'setup--make-pred (cdr sort))))
         (lambda (v) (cl-every (lambda (p) (funcall p v)) subs))))
      ('literal
       (let ((val (cadr sort)))
         (lambda (v) (equal v val))))
      (_ (error "Unknown composite type descriptor: %S" sort))))
   (t (error "Invalid sort descriptor: %S" sort))))

;;;; Public helper to compile sort descriptor (for tests & introspection)
(defun setup-typed-compile-sort-to-pred (sort)
  "Compile SORT descriptor to a predicate function.
See `setup--make-pred' for supported forms." 
  (setup--make-pred sort))

;;;; Small compatibility helper: allow user to extend types at runtime
(defun setup-typed-add-type (name pred)
  "Public: add TYPE NAME with PRED (fn or symbol)."
  (setup--define-type name pred))

;;;; IR (keeps original shapes) ------------------------------------------

(defconst setup--ir-sorts
  '(require also-load autoload bind unbind rebind global hook set face
            mode-assoc defer seq opaque install)
  "Closed set of primitive IR node sorts.")

(defun setup--ir (sort &rest args) (cons sort args))
(defun setup--ir-p (x) (and (consp x) (memq (car x) setup--ir-sorts)))
(defun setup--ir-seq (nodes) (cons 'seq nodes))

;;;; Emitter (copied/adapted from your original setup.el) -----------------

(defun setup--emit-seq (nodes)
  "Emit a sequence of IR NODES as a single form."
  (pcase nodes
    (`nil nil)
    (`(,one) (setup--emit one))
    (_ (cons 'progn (mapcar #'setup--emit nodes)))))

(defun setup--emit (node)
  "Render IR NODE as Emacs Lisp."
  (pcase node
    (`(seq . ,ns) (setup--emit-seq ns))
    (`(opaque ,form) form)
    (`(require ,f) `(unless (require ',f nil t) (throw 'setup-quit nil)))
    (`(also-load ,f) `(require ',f))
    (`(autoload ,fn ,feature)
     `(unless (fboundp ',fn)
        (autoload (function ,fn) ,(symbol-name feature) nil t)))
    (`(bind ,map ,key ,fn)
     (if (vectorp key) `(define-key ,map ,key ,fn) `(keymap-set ,map ,key ,fn)))
    (`(unbind ,map ,key)
     (if (vectorp key) `(define-key ,map ,key nil) `(keymap-unset ,map ,key)))
    (`(rebind ,map ,key ,fn)
     `(progn
        (dolist (old-key (where-is-internal ',fn ,map))
          (if (vectorp old-key)
              (define-key ,map old-key nil)
            (keymap-unset ,map old-key)))
        ,(if (vectorp key)
             `(define-key ,map ,key ,fn)
           `(keymap-set ,map ,key ,fn))))
    (`(global ,key ,fn)
     (if (vectorp key)
         `(define-key (current-global-map) ,key ,fn)
       `(keymap-global-set ,key ,fn)))
    (`(hook ,hook ,fn) `(add-hook ',hook ,fn))
    (`(set option ,var ,val)
     `(funcall (or (get ',var 'custom-set) #'set-default-toplevel-value) ',var ,val))
    (`(set custom ,var ,val) `(customize-set-variable ',var ,val))
    (`(face ,face ,spec) `(custom-set-faces '(,face ,spec)))
    (`(mode-assoc ,alist ,pattern ,mode) `(add-to-list ',alist '(,pattern . ,mode)))
    (`(defer ,arg ,feature ,body-node)
     (let ((body (setup--emit body-node)))
       (cond ((or (null arg) (eq arg t))
              `(with-eval-after-load ',feature ,body))
             ((numberp arg)
              `(run-with-idle-timer ,arg nil (lambda () ,body)))
             (t `(if ,arg
                     ,body
                   (with-eval-after-load ',feature ,body))))))
    (`(install ,spec) (list 'setup--install spec))
    (_ (error "Unknown IR node: %S" node))))

;;;; Typed keyword registry (same API as original) ------------------------

(cl-defstruct (setup--kw (:constructor setup--kw))
  sorts fn repeat doc)

(defvar setup--keywords (make-hash-table :test #'eq)
  "Registry mapping a keyword symbol to a `setup--kw' descriptor.")

(defun setup-define (name sorts fn &rest opts)
  "Define setup keyword NAME.
SORTS is the list of argument sorts (or t for unchecked).  FN is called as
\(FN CTX CHUNK) and returns either IR (primitives) or a surface form made of
other keywords (derived).  OPTS: :repeat N (split args into N), :doc STRING."
  (puthash name
           (setup--kw :sorts (or sorts t)
                      :fn fn
                      :repeat (plist-get opts :repeat)
                      :doc (plist-get opts :doc))
           setup--keywords)
  name)

(defun setup--keyword-p (sym)
  (and (symbolp sym) (gethash sym setup--keywords)))

;;;; Expander (uses composite type predicates) ----------------------------

(defun setup--compile-sort (sort)
  "Return a predicate function for SORT descriptor or symbol.
SORT may be t (meaning no check), a symbol naming a type, a function, or a
composite descriptor supported by `setup--make-pred'." 
  (cond ((eq sort t) (lambda (_v) t))
        ((functionp sort) sort)
        ((symbolp sort)
         (or (setup--get-raw-pred sort)
             (and (fboundp sort) (symbol-function sort))
             (lambda (_v) (signal 'setup-error (list (format "Unknown type/predicate: %S" sort))))))
        ((consp sort) (setup--make-pred sort))
        (t (error "Invalid sort: %S" sort))))

(defun setup--arg-sorts (kw chunk)
  "Check CHUNK against KW's declared sorts; return coerced chunk.
SORT entries in the registration may be either a symbol, t, or a composite
sort form (a list)."
  (let ((sorts (setup--kw-sorts (gethash kw setup--keywords))))
    (if (eq sorts t)
        chunk
      (cl-mapcar
       (lambda (sort value)
         (let ((pred (setup--compile-sort sort)))
           (unless (funcall pred value)
             (signal 'setup-error (list (format "%s: invalid %S argument %S" kw sort value))))
           (setup--coerce sort value)))
       (append sorts (make-list (max 0 (- (length chunk) (length sorts))) 'Opaque))
       chunk))))

(defun setup--chunks (args n)
  "Split ARGS into chunks of N." 
  (if (or (null args) (null n))
      (list args)
    (let (out)
      (while args
        (let ((chunk (cl-subseq args 0 (min n (length args)))))
          (push chunk out)
          (setq args (nthcdr n args))))
      (nreverse out))))

(defun setup--run-keyword (ctx form)
  "Expand the keyword FORM (head registered) under CTX; return IR."
  (let* ((kw (car form))
         (args (cdr form))
         (entry (gethash kw setup--keywords))
         (fn (setup--kw-fn entry))
         (repeat (setup--kw-repeat entry)))
    (if repeat
        (let ((results (mapcar (lambda (chunk)
                                 (funcall fn ctx (setup--arg-sorts kw chunk)))
                               (setup--chunks args repeat))))
          (if (cl-every #'setup--ir-p results)
              (setup--ir-seq results)
            (setup--expand ctx (cons 'progn results))))
      (let ((result (funcall fn ctx (setup--arg-sorts kw args))))
        (if (setup--ir-p result)
            result
          (setup--expand ctx result))))))

(defun setup--reject-unknown (form)
  "Signal when FORM is headed by a `:keyword' that is not registered." 
  (when (and (consp form) (keywordp (car form))
             (not (gethash (car form) setup--keywords)))
    (signal 'setup-error (list (format "Unknown setup keyword: %S" (car form))))))

(defun setup--expand (ctx form)
  "Expand FORM under CTX into IR." 
  (cond
   ((not (consp form)) (setup--ir 'opaque form))
   ((eq (car form) 'quote) (setup--ir 'opaque form))
   ((setup--keyword-p (car form)) (setup--run-keyword ctx form))
   ((keywordp (car form)) (setup--reject-unknown form))
   (t (setup--ir 'opaque (setup--expand-inside ctx form)))))

(defun setup--expand-inside (ctx form)
  "Expand nested setup keywords inside non-keyword FORM, returning Lisp.
Recurses over the ELEMENTS of FORM (like `macroexpand-all'), so a plist key
such as `:global' in `(define-minor-mode ... :global t)' is not mistaken for
a keyword form." 
  (cond
   ((not (consp form)) form)
   ((eq (car form) 'quote) form)
   ((setup--keyword-p (car form))
    (setup--emit (setup--run-keyword ctx form)))
   (t (setup--expand-elements ctx form))))

(defun setup--expand-elements (ctx lst)
  "Expand each element of LST (a list or dotted list) under CTX." 
  (cond
   ((not (consp lst)) lst)
   (t (cons (setup--expand-inside ctx (car lst))
            (setup--expand-elements ctx (cdr lst))))))

(defun setup--expand-body (ctx forms)
  "Expand FORMS under CTX into an IR sequence." 
  (setup--ir-seq (mapcar (lambda (f) (setup--expand ctx f)) forms)))

;;;; Scoping primitives --------------------------------------------------

(defun setup--define-scoper (name key)
  "Define a scoping keyword NAME that sets context KEY to its first argument." 
  (puthash name
           (setup--kw
            :sorts '(Opaque)
            :fn (lambda (ctx args)
                  (let ((value (car args))
                        (body (cdr args)))
                    (setup--expand-body
                     (if (null value) ctx (setup--ctx-put ctx key value))
                     body))))
           setup--keywords))

(setup--define-scoper :with-feature :feature)
(setup--define-scoper :with-hook :hook)
(setup--define-scoper :with-function :function)

;;;; Keyword definitions (migrated from original setup.el) ---------------

;;; Loading

(setup-define :require '(Feature) (lambda (_ctx chunk)
                                    (setup--ir 'require (car chunk)))
              :repeat 1 :doc "Require FEATURE or quit the block.")
(setup-define :also-load '(Feature) (lambda (_ctx chunk)
                                      (setup--ir 'also-load (car chunk)))
              :repeat 1 :doc "Require FEATURE with the body.")
(setup-define :autoload t (lambda (ctx chunk)
                            (setup--ir 'autoload (setup--unquote (car chunk))
                                       (setup--ctx ctx :feature 'autoload)))
              :repeat 1 :doc "Autoload the current function.")
(setup-define :autoload-this t (lambda (ctx _chunk)
                                 (list :autoload (setup--ctx ctx :function 'autoload-this)))
              :doc "Autoload the context function.")
(setup-define :defer t (lambda (ctx args)
                         (let ((arg (car args))
                               (body (cdr args)))
                           (setup--ir 'defer arg
                                      (setup--ctx ctx :feature 'defer)
                                      (setup--ir-seq
                                       (mapcar (lambda (f) (setup--expand ctx f)) body)))))
              :doc "Defer BODY.")
(setup-define :when-loaded t (lambda (_ctx args)
                               (cons :defer (cons t args)))
              :doc "Evaluate BODY when the feature is loaded.")
(setup-define :delay t (lambda (_ctx args)
                         (cons :defer args))
              :doc "Evaluate BODY after idle time.")
(setup-define :commands t (lambda (_ctx args)
                            (let ((commands (car args))
                                  (body (cdr args)))
                              (cons 'progn
                                    (cons (cons 'progn
                                                (mapcar (lambda (c) (list :autoload c)) commands))
                                          (list (cons :when-loaded body))))))
              :doc "Autoload COMMANDS then defer BODY.")
(setup-define :init t (lambda (ctx body)
                        (setup--ir 'opaque
                                   (cons 'progn
                                         (mapcar (lambda (f) (setup--expand-inside ctx f)) body))))
              :doc "Evaluate BODY immediately.")

;;; After-load

(setup-define :after t (lambda (_ctx args)
                         (let ((spec (car args))
                               (body (cdr args)))
                           (cond
                            ((symbolp spec)
                             (list :with-feature spec (cons :when-loaded body)))
                            ((eq (car-safe spec) :all)
                             (let ((fs (cdr spec)))
                               (if (null fs)
                                   (cons 'progn body)
                                 (let ((result (list :with-feature (car (last fs))
                                                     (cons :when-loaded body))))
                                   (dolist (f (reverse (butlast fs)))
                                     (setq result (list :with-feature f (cons :when-loaded (list result)))))
                                   result))))
                            ((listp spec)
                             (let ((guard (make-symbol "setup--after-guard")))
                               (cons 'let
                                     (cons (list guard)
                                           (mapcar (lambda (f)
                                                     (list 'with-eval-after-load (list 'quote f)
                                                           (list 'unless guard
                                                                 (list 'setq guard t)
                                                                 (cons :with-feature (cons f body)))))
                                                   spec)))))
                            (t (signal 'setup-error (list (format ":after: invalid spec %S" spec)))))))
              :doc "Evaluate BODY after FEATURE loads.")

;;; Bindings

(defun setup--bind-map (ctx)
  (setup--ctx ctx :map 'bind))

(setup-define :bind* '(Map Key Function) (lambda (ctx chunk)
                                       (setup--ir 'bind (setup--bind-map ctx)
                                                  (nth 0 chunk) (nth 1 chunk)))
              :repeat 2 :doc "Bind KEY to COMMAND in the current map.")
(setup-define :bind t (lambda (_ctx args) (list :when-loaded (cons :bind* args)))
              :doc "Bind KEY to COMMAND after the feature loads.")
(setup-define :unbind t (lambda (_ctx args) (list :when-loaded (cons :unbind* args)))
              :doc "Unbind KEY in the current map.")
(setup-define :unbind* '(Key) (lambda (ctx chunk)
                                (setup--ir 'unbind (setup--bind-map ctx) (car chunk)))
              :repeat 1 :doc "Unbind KEY immediately.")
(setup-define :rebind t (lambda (_ctx args) (list :when-loaded (cons :rebind* args)))
              :doc "Rebind COMMAND to KEY in the current map.")
(setup-define :rebind* '(Key Function) (lambda (ctx chunk)
                                         (setup--ir 'rebind (setup--bind-map ctx)
                                                    (nth 0 chunk) (nth 1 chunk)))
              :repeat 2 :doc "Rebind COMMAND to KEY immediately.")
(setup-define :global '(Key Function) (lambda (_ctx chunk)
                                        (setup--ir 'global (nth 0 chunk) (nth 1 chunk)))
              :repeat 2 :doc "Bind KEY to COMMAND globally.")
(setup-define :bind-into t (lambda (_ctx args)
                             (let ((map (car args)))
                               (list :with-map map (cons :bind (cdr args)))))
              :doc "Bind into MAP.")
(setup-define :bind-to t (lambda (ctx args)
                           (list :global (car args) (setup--ctx ctx :function 'bind-to)))
              :repeat 1 :doc "Bind the context function to KEY globally.")

;;; Hooks

(setup-define :hook '(Function) (lambda (ctx chunk)
                                  (setup--ir 'hook (setup--ctx ctx :hook 'hook) (car chunk)))
              :repeat 1 :doc "Add FUNCTION to the current hook.")
(setup-define :hooks t (lambda (_ctx args)
                         (list :with-hook (car args) (cons :hook (cdr args))))
              :repeat 2 :doc "Add FUNCTION to HOOK.")
(setup-define :hook-into t (lambda (ctx args)
                             (list :with-hook (car args)
                                   (list :hook (setup--ctx ctx :function 'hook-into))))
              :repeat 1 :doc "Add the context function to HOOK.")
(setup-define :local-hook '(Hook Function) (lambda (_ctx chunk)
                                             (list :hook (list 'function
                                                               (list 'lambda nil
                                                                     (list 'add-hook
                                                                           (list 'quote (nth 0 chunk))
                                                                           (nth 1 chunk) nil t)))))
              :repeat 2 :doc "Add FUNCTION to HOOK locally.")
(setup-define :local-set t (lambda (_ctx chunk)
                             (let ((name (car chunk)) (val (nth 1 chunk)))
                               (list :hook
                                     (list 'function
                                           (list 'lambda nil
                                                 (list 'setq-local name val))))))
              :repeat 2 :doc "Set NAME locally to VAL.")

;;; Variables and faces

(setup-define :option* t (lambda (_ctx chunk)
                           (setup--ir 'set 'option (nth 0 chunk) (nth 1 chunk)))
              :repeat 2 :doc "Set option NAME to VAL immediately.")
(setup-define :option t (lambda (_ctx args) (list :when-loaded (cons :option* args)))
              :doc "Set option NAME to VAL after load.")
(setup-define :custom* t (lambda (_ctx chunk)
                           (setup--ir 'set 'custom (nth 0 chunk) (nth 1 chunk)))
              :repeat 2 :doc "Set variable NAME to VAL immediately.")
(setup-define :custom t (lambda (_ctx args) (list :when-loaded (cons :custom* args)))
              :doc "Set variable NAME to VAL after load.")
(setup-define :customs* t (lambda (_ctx chunk)
                            (let* ((nsv (car chunk))
                                   (names (car nsv))
                                   (val (cdr nsv)))
                              (cons 'progn
                                    (mapcar (lambda (n) (list :custom* n val))
                                            (if (listp names) names (list names))))))
              :repeat 1 :doc "Set several names to VAL immediately.")
(setup-define :customs t (lambda (_ctx args) (list :when-loaded (cons :customs* args)))
              :doc "Set several names to VAL after load.")

(defun setup--face-spec (args)
  "Normalize ARGS into a face spec."
  (cond ((and (listp (car args)) (listp (car (car args)))) (car args))
        ((and (listp (car args)) (keywordp (car (car args)))) (list (list t (car args))))
        (t (car args))))

(setup-define :custom-face* t (lambda (_ctx chunk)
                                (setup--ir 'face (nth 0 chunk)
                                           (setup--face-spec (list (nth 1 chunk)))))
              :repeat 2 :doc "Set FACE to SPEC immediately.")
(setup-define :custom-face t (lambda (_ctx args)
                               (list :when-loaded (cons :custom-face* args)))
              :doc "Set FACE to SPEC after load.")

;;; Mode association

(defun setup--process-arg (arg mode kind)
  "Return (PATTERN . MODE) cells for :KIND from ARG."
  (cond
   ((stringp arg) (list (cons arg (funcall mode))))
   ((and (consp arg) (symbolp (cdr arg)))
    (if (listp (car arg))
        (mapcar (lambda (p) (cons p (cdr arg))) (car arg))
      (list arg)))
   ((listp arg) (mapcar (lambda (p) (cons p (funcall mode))) arg))
   (t (signal 'setup-error (list (format "Invalid :%s argument: %S" kind arg))))))

(defun setup--alist-mode (ctx alist arg kind)
  "Associate ARG in ALIST; resolve the default MODE from CTX lazily."
  (setup--ir-seq
   (mapcar (lambda (pair)
             (setup--ir 'mode-assoc alist (car pair) (cdr pair)))
           (setup--process-arg arg (lambda () (setup--ctx ctx :mode kind)) kind))))

(setup-define :mode '(Opaque) (lambda (ctx chunk)
                                (setup--alist-mode ctx 'auto-mode-alist (car chunk) 'mode))
              :repeat 1 :doc "Associate current mode with files.")
(setup-define :interpreter '(Opaque) (lambda (ctx chunk)
                                       (setup--alist-mode ctx 'interpreter-mode-alist
                                                          (car chunk) 'interpreter))
              :repeat 1 :doc "Associate current mode with interpreters.")
(setup-define :magic '(Opaque) (lambda (ctx chunk)
                                 (setup--alist-mode ctx 'magic-mode-alist (car chunk) 'magic))
              :repeat 1 :doc "Associate current mode with magic strings.")
(setup-define :magic-fallback '(Opaque) (lambda (ctx chunk)
                                          (setup--alist-mode ctx 'magic-fallback-mode-alist
                                                             (car chunk) 'magic-fallback))
              :repeat 1 :doc "Like :magic, with fallback.")

;;; Backend

(setup-define :elpaca t (lambda (ctx args)
                          (let ((order (car args)) (recipe (cdr args)))
                            (setup--ir 'install
                                       (cond ((eq order t) (setup--ctx ctx :feature 'elpaca))
                                             ((eq order nil) nil)
                                             (t (cons order recipe))))))
              :doc "Install ORDER with elpaca.")

;;; Location (internal)

(setup-define :at-location t (lambda (_ctx args) (nth 1 args))
              :doc "Internal: FORM at its source location.")

;;;; Mode/map scoping with inference ------------------------------------

(setup-define :with-map t (lambda (ctx args)
                            (let ((map (car args)))
                              (setup--expand-body
                               (if (null map) ctx (setup--ctx-put ctx :map map))
                               (cdr args))))
              :doc "Re-scope BODY to MAP.")
(setup-define :with-mode t (lambda (ctx args)
                             (let ((mode (car args)))
                               (setup--expand-body
                                (if (null mode) ctx (setup--ctx-put ctx :mode mode))
                                (cdr args))))
              :doc "Re-scope BODY to MODE.")

;;;; Block compiler -----------------------------------------------------

(defconst setup--shorthands
  '(":elpaca" . cadr)
  "Shorthand head = feature extractor. (simplified for typed version)")

(defun setup--shorthand-feature (name)
  "Return the feature named by the shorthand cons NAME." 
  (let ((entry (assoc (symbol-name (car name)) setup--shorthands)))
    (when entry (funcall (cdr entry) name))))

(defun setup--ir-contains-p (nodes sort)
  "Return non-nil if IR NODES contain a node of SORT.
Only IR nodes are traversed; opaque payloads are left untouched." 
  (let (found)
    (cl-labels ((go (n)
                  (when (setup--ir-p n)
                    (if (eq (car n) sort)
                        (setq found t)
                      (mapc #'go (cdr n))))))
      (mapc #'go nodes))
    found))

(defun setup--install-spec (nodes)
  "Return (SPEC . REST) if NODES contain an install node, else (nil . NODES)."
  (let (spec rest)
    (dolist (node nodes)
      (if (and (consp node) (eq (car node) 'install))
          (setq spec (cadr node))
        (push node rest)))
    (cons spec (nreverse rest))))

(defmacro setup-typed (name &rest body)
  "Typed setup macro. NAME may be a cons shorthand.
This macro expands like the original `setup' but runs typed checks." 
  (declare (indent 1))
  (let* ((cons-name (consp name))
         (feature (and cons-name (setup--shorthand-feature name)))
         (ctx (if feature (list :feature feature) nil))
         (forms (if cons-name (cons name body) body))
         (ir (setup--expand-body ctx forms))
         (nodes (cdr ir))
         (installed (setup--install-spec nodes))
         (spec (car installed))
         (rest (cdr installed))
         (needs-quit (setup--ir-contains-p rest 'require))
         (emitted (setup--emit-seq rest))
         (block (if needs-quit `(catch 'setup-quit ,emitted) emitted)))
    (if spec
        `(when (fboundp 'elpaca) (elpaca ,spec ,block))
      block)))

;;;; Context helpers ----------------------------------------------------

(defun setup--ctx-put (ctx key value)
  "Return CTX with KEY set to VALUE." 
  (let ((copy (copy-sequence ctx)))
    (setq copy (plist-put copy key value))
    copy))

(defun setup--ctx (ctx key kw)
  "Return value of KEY in CTX; signal if absent." 
  (or (plist-get ctx key)
      (signal 'setup-error (list (format "%s: cannot deduce %s from context" kw key)))))

;;;; Utilities re-exported for tests/debugging ---------------------------

(provide 'setup-typed)
;;; setup-typed.el ends here
