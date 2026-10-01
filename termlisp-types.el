;;; termlisp-types.el --- HM type inference -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Types are either a type variable (a `tl-lvar') or a type constructor
;; application `tl-tcon'.  Substitutions are alists tvar -> type.  The type
;; unifier shares `tl-deref' with the term kernel and uses `tl-occurs-type' to
;; walk type constructors; like ACL2's one-way unifier, it leaves bindings
;; unchanged on failure.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-unify)
(require 'termlisp-reader)

(declare-function tl-eval-datatype "termlisp-eval" (env form))
(declare-function tl-eval-datatype-extension "termlisp-eval" (env form))
(declare-function tl-desugar-do "termlisp-eval" (form))

(cl-defstruct (tl-tcon (:constructor tl-tcon (name args))) name args)
(cl-defstruct (tl-tscheme (:constructor tl-tscheme (vars type &optional constraints)))
  vars type (constraints nil))
(cl-defstruct (tl-constraint (:constructor tl-constraint (class type))) class type)
(cl-defstruct (tl-cclass (:constructor tl-cclass (name params supers methods))) name params supers methods)
(cl-defstruct (tl-instance (:constructor tl-instance (class head context methods))) class head context methods)

(defun tl-tvar-p (x) (tl-lvar-p x))
(defun tl-type-p (x) (or (tl-tvar-p x) (tl-tcon-p x)))

;; LEVEL is intentionally unused in Plan 2 (generalization uses tvars not free in the environment); reserved for level-based generalization in a later plan.
(defun tl-fresh-tvar (&optional level)
  "Return a fresh type variable."
  (tl-make-lvar (gensym "t") (or level 0)))

(defun tl-tarrow (a b) (tl-tcon '-> (list a b)))
(defun tl-tint () (tl-tcon 'Int nil))
(defun tl-tstring () (tl-tcon 'String nil))
(defun tl-tbool () (tl-tcon 'Bool nil))

(defun tl-tfun-args (ty)
  "If TY is `(-> a b)', return (a b), else nil."
  (when (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
    (tl-tcon-args ty)))

(defun tl-occurs-type (var type bindings)
  "Return non-nil if VAR occurs in TYPE under BINDINGS.
Like `tl-occurs', but traverses the argument types of a `tl-tcon'."
  (let ((work (list type)) (found nil))
    (while (and work (not found))
      (let ((t0 (tl-deref (pop work) bindings)))
        (cond ((eq t0 var) (setq found t))
              ((tl-tcon-p t0)
               (dolist (a (tl-tcon-args t0)) (push a work))))))
    found))

(defun tl-unify-types (a b bindings)
  "Unify types A and B under BINDINGS.  Return `(ok . bindings)'.
On failure returns `(nil . nil)'."
  (let ((pending (list (cons a b))) (ok t))
    (while (and pending ok)
      (let* ((pair (pop pending))
             (x (tl-deref (car pair) bindings))
             (y (tl-deref (cdr pair) bindings)))
        (cond
         ((eq x y))
         ((tl-tvar-p x)
          (if (tl-occurs-type x y bindings) (setq ok nil)
            (setq bindings (cons (cons x y) bindings))))
         ((tl-tvar-p y)
          (if (tl-occurs-type y x bindings) (setq ok nil)
            (setq bindings (cons (cons y x) bindings))))
         ((and (tl-tcon-p x) (tl-tcon-p y))
          (if (and (eq (tl-tcon-name x) (tl-tcon-name y))
                   (= (length (tl-tcon-args x)) (length (tl-tcon-args y))))
              (let ((ax (tl-tcon-args x)) (ay (tl-tcon-args y)))
                (while ax
                  (push (cons (car ax) (car ay)) pending)
                  (setq ax (cdr ax) ay (cdr ay))))
            (setq ok nil)))
         (t (setq ok nil)))))
    (if ok (cons t bindings) (cons nil nil))))

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

(defun tl-type-parse-segment (segment)
  "Parse SEGMENT, one arrow operand's token list, into a type.
A single-token SEGMENT is that token; otherwise it is a constructor
application."
  (if (cdr segment)
      (tl-tcon (car segment) (mapcar #'tl-type-parse* (cdr segment)))
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
    (tl-tcon (car sexp) (mapcar #'tl-type-parse* (cdr sexp))))
   (t (signal 'termlisp-type-error (list (format "Bad type: %S" sexp))))))

(defun tl-type-parse (sexp)
  "Parse surface type expression SEXP into a type."
  (let ((tl-type-parse-vars nil))
    (tl-type-parse* sexp)))

(defun tl-free-tvars (type)
  "Return the list of type variables occurring in TYPE."
  (let ((acc nil))
    (cl-labels ((walk (node)
                  (cond ((tl-tvar-p node) (cl-pushnew node acc :test #'eq))
                        ((tl-tcon-p node) (mapc #'walk (tl-tcon-args node))))))
      (walk type))
    acc))

(defun tl-type-parse-scheme (sexp)
  "Parse SEXP into a type scheme, quantifying its free variables."
  (let ((ty (tl-type-parse sexp)))
    (tl-tscheme (tl-free-tvars ty) ty)))

(defun tl-type-subst (type sub)
  "Apply substitution SUB (alist tvar -> type) to TYPE."
  (cond
   ((tl-tvar-p type)
    (let ((cell (assq type sub))) (if cell (cdr cell) type)))
   ((tl-tcon-p type)
    (tl-tcon (tl-tcon-name type)
             (mapcar (lambda (arg) (tl-type-subst arg sub)) (tl-tcon-args type))))
   (t type)))

(defun tl-apply-bindings (type bindings)
  "Fully apply BINDINGS to TYPE."
  (let ((ty (tl-deref type bindings)))
    (if (tl-tcon-p ty)
        (tl-tcon (tl-tcon-name ty)
                 (mapcar (lambda (arg) (tl-apply-bindings arg bindings))
                         (tl-tcon-args ty)))
      ty)))

(defun tl-generalize (type env-tvars)
  "Generalize TYPE into a scheme, quantifying tvars not in ENV-TVARS."
  (let* ((ftv (tl-free-tvars type))
         (vars (cl-remove-if (lambda (v) (memq v env-tvars)) ftv)))
    (tl-tscheme vars type)))

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

(defun tl-instantiate (scheme)
  "Instantiate SCHEME (a `tl-tscheme') with fresh type variables."
  (if (tl-tscheme-p scheme)
      (let ((sub (mapcar (lambda (v) (cons v (tl-fresh-tvar)))
                         (tl-tscheme-vars scheme))))
        (tl-type-subst (tl-tscheme-type scheme) sub))
    scheme))

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

(defun tl-compose-bindings (b1 b2)
  "Compose substitutions B1 and B2 (apply B2 after B1).
Result is first-wins for `tl-deref' (assq); duplicate keys from B2 and
self-bindings are removed."
  (let ((composed
         (mapcar (lambda (cell)
                   (cons (car cell) (tl-apply-bindings (cdr cell) b2)))
                 b1))
        (rest (cl-remove-if (lambda (cell) (assq (car cell) b1)) b2)))
    (cl-remove-if (lambda (cell) (eq (car cell) (cdr cell)))
                  (append composed rest))))

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
   ((consp expr) (tl-infer-application env expr))
   (t (signal 'termlisp-type-error (list (format "Cannot infer: %S" expr))))))

(defun tl-infer-symbol (env sym)
  "Infer the type of a bare symbol SYM."
  (let ((cell (assq sym (tl-tenv-locals env)))
        (base (tl-tenv-base env)))
    (cond
     (cell (cons (cdr cell) nil))
     ((and base (gethash sym (tl-env-type-env base)))
      (cons (tl-instantiate (gethash sym (tl-env-type-env base))) nil))
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

(defun tl-infer-application (env expr)
  "Infer a function application EXPR = (F A1 ... AN)."
  (let* ((head (car expr))
         (args (cdr expr))
         (rh (tl-infer env head))
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
          (unless (car u)
            (signal 'termlisp-type-error
                    (list (format "Cannot apply %S to %S" head arg))))
          (setq bindings (cdr u))
          (setq ftype (tl-apply-bindings res bindings)))))
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

(defun tl-infer-define-clauses (env name clauses)
  "Infer NAME from CLAUSES (list of `(PARAMS . BODY)'); register a scheme."
  (let* ((placeholder (tl-fresh-tvar))
         (tyenv (tl-env-type-env env))
         (sig (and (gethash name (tl-env-sig-env env))
                   (gethash name tyenv))))
    (puthash name (tl-tscheme nil placeholder) tyenv)
    (let ((bindings nil))
      (dolist (clause clauses)
        (let* ((params (car clause))
               (body (cdr clause))
               (ptypes (mapcar (lambda (_) (tl-fresh-tvar)) params))
               (binds nil)
               (ps params)
               (pts ptypes))
          (while ps
            (let ((r (tl-infer-pattern (tl-zonk-env (cons nil env) bindings)
                                       (car ps) (car pts))))
              (setq binds (append (car r) binds)
                    bindings (tl-compose-bindings bindings (cdr r)))
              (setq ps (cdr ps) pts (cdr pts))))
          (let* ((binds-z (mapcar (lambda (cell)
                                    (cons (car cell)
                                          (tl-apply-bindings (cdr cell) bindings)))
                                  binds))
                 (env2 (tl-tenv-extend (cons nil env) binds-z))
                 (rb (tl-infer (tl-zonk-env env2 bindings) body)))
            (setq bindings (tl-compose-bindings bindings (cdr rb)))
            (let ((ctype (tl-apply-bindings (car rb) bindings)))
              (dolist (pt (reverse (mapcar (lambda (p)
                                             (tl-apply-bindings p bindings))
                                           ptypes)))
                (setq ctype (tl-tarrow pt ctype)))
              (let ((u (tl-unify-types placeholder ctype bindings)))
                (unless (car u)
                  (signal 'termlisp-type-error
                          (list (format "Clause of %S has inconsistent type" name))))
                (setq bindings (cdr u)))))))
      (let ((final (tl-apply-bindings placeholder bindings)))
        (if sig
            (let ((u (tl-unify-types final (tl-skolemize-scheme sig) nil)))
              (unless (car u)
                (signal 'termlisp-type-error
                        (list (format "Definition of %S does not match its signature" name))))
              (puthash name sig tyenv))
          (puthash name (tl-generalize final (tl-env-free-tvars env)) tyenv))))))

(defun tl-syntactic-value-p (expr)
  "Return non-nil if EXPR is a syntactic value (value restriction)."
  (or (atom expr)
      (and (consp expr) (eq (car expr) 'lambda))))

(defun tl-infer-constant (env name expr)
  "Infer a constant binding NAME = EXPR."
  (let ((r (tl-infer (cons nil env) expr)))
    (let ((ty (tl-apply-bindings (car r) (cdr r))))
      (if (gethash name (tl-env-sig-env env))
          (let* ((sig (gethash name (tl-env-type-env env)))
                 (u (tl-unify-types ty (tl-skolemize-scheme sig) nil)))
            (unless (car u)
              (signal 'termlisp-type-error
                      (list (format "Definition of %S does not match its signature" name))))
            (puthash name sig (tl-env-type-env env))
            ty)
        (puthash name
                 (if (tl-syntactic-value-p expr)
                     (tl-generalize ty (tl-env-free-tvars env))
                   (tl-tscheme nil ty))
                 (tl-env-type-env env))
        ty))))

(defun tl-register-signature (env form)
  "Register a `(: NAME TYPE)' signature in ENV."
  (let ((name (cadr form))
        (sc (tl-type-parse-scheme (caddr form))))
    (puthash name sc (tl-env-type-env env))
    (puthash name t (tl-env-sig-env env))
    name))

(defun tl-typecheck-define (env form)
  "Typecheck a `define' FORM, registering it in ENV."
  (let ((target (cadr form)))
    (if (consp target)
        (let* ((name (car target))
               (params (cdr target))
               (body (caddr form))
               (clauses (append (gethash name (tl-env-clauses env))
                                (list (cons params body)))))
          (puthash name clauses (tl-env-clauses env))
          (tl-infer-define-clauses env name clauses))
      (tl-infer-constant env target (caddr form)))))

(defun tl-register-class (env form)
  "Register `(class NAME (PARAM) SUPERS METHOD-DECL...)' in ENV."
  (let* ((name (nth 1 form))
         (param (car (nth 2 form)))
         (supers (nth 3 form))
         (method-decls (nthcdr 4 form))
         (methods nil))
    (dolist (md method-decls)
      (let* ((mname (car md))
             (ty (tl-type-parse (cadr md)))
             (cparam (tl-fresh-tvar)))
        (push (cons mname
                    (tl-tscheme (list cparam)
                                ty
                                (list (tl-constraint name cparam))))
              methods)))
    (setq methods (nreverse methods))
    (puthash name (tl-cclass name (list param) supers methods)
             (tl-env-class-env env))
    (dolist (m methods)
      (puthash (car m) (cdr m) (tl-env-method-env env)))
    name))

(defun tl-register-instance (env form)
  "Register `(instance (CLASS TYPE))' in ENV (methods defined separately)."
  (let* ((head (nth 1 form))
         (cname (car head))
         (ty (tl-type-parse (cadr head)))
         (inst (tl-instance cname ty nil nil)))
    (puthash cname (append (gethash cname (tl-env-instance-env env)) (list inst))
             (tl-env-instance-env env))
    cname))

(defun tl-typecheck-form (env form)
  "Typecheck one top-level FORM in ENV."
  (cond
   ((and (consp form) (eq (car form) 'datatype)) (tl-eval-datatype env form))
   ((and (consp form) (eq (car form) 'datatype-extension))
    (tl-eval-datatype-extension env form))
   ((and (consp form) (eq (car form) ':)) (tl-register-signature env form))
   ((and (consp form) (eq (car form) 'define)) (tl-typecheck-define env form))
   ((and (consp form) (eq (car form) 'class)) (tl-register-class env form))
   ((and (consp form) (eq (car form) 'instance)) (tl-register-instance env form))
   (t (car (tl-infer (cons nil env) form)))))

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
