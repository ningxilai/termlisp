;;; termlisp-numeric.el --- Exact arithmetic backend over Calc -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; The primitive arithmetic in `termlisp-builtins' works on native Elisp
;; numbers, which model Aldor's `Integer'/`DoubleFloat' and the fixed-width
;; machine integers.  Three domains are not representable that way: exact
;; rationals (`Fraction'), complex numbers (`Complex') and arbitrary
;; precision floats (`Float').  This module implements them on top of
;; Emacs Calc:
;;
;;   Fraction  a normalised Calc fraction `(frac NUM DEN)'
;;   Complex   a Calc rectangular complex     `(cplx RE IM)'
;;   Bigfloat  a normalised Calc bigfloat     `(float MANT EXPT)'
;;
;; Native values are handled by the ordinary Elisp operators, so the fast
;; path used by the corpus is untouched; `tl-exact-number-p' tells the two
;; apart.  Calc is an optional dependency, loaded lazily on the first
;; tower operation so that merely loading termlisp stays cheap.
;;
;; Using Calc as a library means carrying none of Calc's session state:
;; every entry point runs inside `tl-calc-pure', which pins the variables
;; a computation would otherwise read (progress chatter, angle mode,
;; exact-vs-float division, symbolic mode, working precision), so a
;; Calc-backed operation is a function of its arguments alone.  Calc's
;; inexact type is the bigfloat -- an Elisp float is not a Calc number --
;; so the bridge in this module moves doubles through their exact finite
;; decimal expansion.
;;
;; The type-directed Aldor lowering (`tl-aldor--exact-op-target') selects
;; these operations for the `Fraction'/`Complex' domains; nothing changes
;; for `Integer'/`DoubleFloat'/machine integers.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-builtins)

(declare-function math-add "calc" (a b))
(declare-function math-sub "calc" (a b))
(declare-function math-mul "calc" (a b))
(declare-function math-div "calc" (a b))
(declare-function math-normalize "calc" (a))
(declare-function math-make-float "calc" (m e))
(declare-function math-trunc "calc" (a))
(declare-function math-lessp "calc-ext" (a b))

;; Calc options honoured dynamically; declared here so the binds below are
;; dynamic under lexical-binding.
(defvar calc-prefer-frac)
(defvar calc-display-working-message)
(defvar calc-angle-mode)
(defvar calc-symbolic-mode)
(defvar calc-internal-prec)

(defun tl-calc-ensure ()
  "Load Calc and its extensions on first use.  Return non-nil.
`math-lessp' lives in `calc-ext', which Calc loads when the calculator
starts; a library user never starts it."
  (require 'calc)
  (require 'calc-ext))

(defmacro tl-calc-pure (prec &rest body)
  "Evaluate BODY as a pure Calc computation with pinned ambient state.
Calc reads session variables while computing; binding them all here in
one place is what lets this module promise that a Calc-backed operation
is a function of its arguments alone: no `Working...' chatter, radians,
exact results preferred, no symbolic mode, and the working precision
bound to PREC when PREC is non-nil (nil keeps Calc's default, 12
significant digits)."
  (declare (indent 1) (debug t))
  ;; The precision override lives in `calc-internal-prec''s own init:
  ;; a `let' binds in parallel, so init forms see only the enclosing
  ;; environment -- a sibling binding would still be void there.
  `(progn
     (tl-calc-ensure)
     (let ((calc-display-working-message nil)
           (calc-angle-mode 'rad)
           (calc-prefer-frac t)
           (calc-symbolic-mode nil)
           (calc-internal-prec (or ,prec calc-internal-prec)))
       ,@body)))

(defun tl-exact-number-p (x)
  "Return non-nil when X is a value of the Calc-backed tower.
A fraction (a `frac' cons), a complex (a `cplx' cons) or a bigfloat (a
`float' cons).  Native Elisp numbers stay on the fast path: Elisp
bignums are exact integers and Doubles are the `DoubleFloat' model."
  (and (consp x) (memq (car x) '(frac cplx float))))

;;;; Fractions

(defun tl-fraction (n d)
  "Return the exact fraction N/D, normalised.
N and D are integers (a `Fraction' is over `Integer'); a non-integer
operand or a zero D signals `termlisp-eval-error'."
  (unless (and (integerp n) (integerp d))
    (signal 'termlisp-eval-error '("Fraction operands must be integers")))
  (when (zerop d)
    (signal 'termlisp-eval-error '("Division by zero constructing a Fraction")))
  (tl-calc-pure nil (math-normalize (list 'frac n d))))

(defun tl-fraction-p (x)
  "Return non-nil when X is an exact fraction."
  (and (consp x) (eq (car x) 'frac)))

(defun tl-fraction-numerator (x)
  "Return the numerator of the fraction X."
  (nth 1 x))

(defun tl-fraction-denominator (x)
  "Return the denominator of the fraction X."
  (nth 2 x))

;;;; Complex numbers

(defun tl-complex (re im)
  "Return the complex number with real part RE and imaginary part IM.
An Elisp float part is converted to the Calc bigfloat of its exact
value, so the result is a well-formed Calc value whatever the parts."
  (tl-calc-pure nil
    (math-normalize (list 'cplx (tl--to-calc re) (tl--to-calc im)))))

(defun tl-complex-p (x)
  "Return non-nil when X is a complex number."
  (and (consp x) (eq (car x) 'cplx)))

(defun tl-complex-real (x)
  "Return the real part of the complex number X."
  (nth 1 x))

(defun tl-complex-imag (x)
  "Return the imaginary part of the complex number X."
  (nth 2 x))

;;;; Bigfloats

(defun tl-bigfloat-p (x)
  "Return non-nil when X is a Calc bigfloat."
  (and (consp x) (eq (car x) 'float)))

(defun tl-bigfloat->string (x)
  "Render the bigfloat X as a decimal string.
A bigfloat is the finite decimal MANT times ten to the EXPT, so the
rendering is exact."
  (let ((m (nth 1 x)) (e (nth 2 x)))
    (if (zerop m)
        "0"
      (let* ((neg (< m 0))
             (digits (number-to-string (abs m)))
             (n (length digits)))
        (concat (if neg "-" "")
                (cond ((>= e 0)
                       (concat digits (make-string e ?0)))
                      ((<= (- e) n)
                       (let ((head (substring digits 0 (+ n e))))
                         (concat (if (zerop (length head)) "0" head) "."
                                 (substring digits (+ n e)))))
                      (t
                       (concat "0." (make-string (- (- e) n) ?0) digits))))))))

(defun tl-bigfloat (x prec)
  "Return X as a Calc bigfloat rounded to PREC significant digits.
X may be an integer, an Elisp float, a fraction or a bigfloat.  The
value is converted exactly where it is finite (an integer is whole, a
double's decimal expansion is finite, a bigfloat already carries its
digits) and PREC then rounds it: 12345 at PREC 2 is 1.2e4, and a
fraction divides at PREC, so an inexact quotient is carried to PREC
significant digits.  Normalisation strips trailing zeros, so a value
representable in fewer digits keeps the short form.  A complex X, a
non-finite float or a PREC below one signals `termlisp-eval-error'."
  (unless (and (integerp prec) (> prec 0))
    (signal 'termlisp-eval-error
            '("bigfloat precision must be a positive integer")))
  (when (tl-complex-p x)
    (signal 'termlisp-eval-error
            '("cannot convert a complex number to a bigfloat")))
  (tl-calc-pure prec
    (cond ((integerp x) (math-normalize (math-make-float x 0)))
          ((floatp x) (math-normalize (tl--double->bigfloat x)))
          ((tl-fraction-p x)
           (math-div (math-make-float (nth 1 x) 0) (nth 2 x)))
          ((tl-bigfloat-p x) (math-normalize x))
          (t (signal 'termlisp-eval-error
                     (list (format "bigfloat expects a number, got %S" x)))))))

;; The bigfloat owns its printed form (see `tl-value-printers'); the
;; renderers in `termlisp-builtins' and `termlisp-eval' consult it.
(add-to-list 'tl-value-printers (cons #'tl-bigfloat-p #'tl-bigfloat->string))

;;;; The Elisp-double bridge
;;
;; Calc's inexact type is the bigfloat; an Elisp float is not a Calc
;; number, and a Calc function that meets one dies of
;; `wrong-type-argument' (on Emacs 32, `(math-float 0.5)' is
;; `(car 0.5)').  A double is a finite decimal, so `format' prints its
;; exact expansion and parsing that expansion loses nothing.

(defun tl--double->bigfloat (x)
  "Return the exact value of the Elisp float X as a normalised bigfloat.
Signal `termlisp-eval-error' when X is not finite.  Normalisation runs
at a precision above any expansion, so it only strips trailing zeros."
  (cond ((= x 0.0) '(float 0 0))
        ((or (isnan x) (= (abs x) 1.0e+INF))
         (signal 'termlisp-eval-error
                 '("cannot build a bigfloat from a non-finite number")))
        (t
         (let* ((spec (format "%.1769e" x))
                (split (string-match "e" spec))
                (mant (substring spec 0 split))
                (exp10 (string-to-number (substring spec (1+ split))))
                (neg (string-prefix-p "-" mant))
                (digits (replace-regexp-in-string "[-.]" "" mant))
                (m (string-to-number digits)))
           (let ((calc-internal-prec (1+ (length digits))))
             (math-normalize
              (math-make-float (if neg (- m) m)
                               (- exp10 (1- (length digits))))))))))

(defun tl--to-calc (x)
  "Return X in a representation Calc's arithmetic accepts.
An Elisp float becomes the bigfloat of its exact value; integers,
fractions, complex numbers and bigfloats pass through unchanged."
  (if (floatp x) (tl--double->bigfloat x) x))

(defun tl--bigfloat->exact (x)
  "Return the exact fraction equal to the bigfloat X.
A bigfloat is a finite decimal, so M times ten to the EXPT is exactly
M divided by ten to the -EXPT while EXPT is negative."
  (let ((m (nth 1 x)) (e (nth 2 x)))
    (math-normalize
     (if (>= e 0)
         (list 'frac (* m (expt 10 e)) 1)
       (list 'frac m (expt 10 (- e)))))))

(defun tl--to-exact (x)
  "Return X as an exact Calc number: an integer or a fraction.
Doubles and bigfloats are finite decimals, so the conversion loses
nothing; integers and fractions are unchanged.  Comparisons run on
this form because Calc's own mixed bigfloat/fraction comparison
rounds instead of comparing exactly (on Emacs 32, `math-equal' of
0.1 and 1/10 is nil)."
  (cond ((floatp x) (tl--bigfloat->exact (tl--double->bigfloat x)))
        ((tl-bigfloat-p x) (tl--bigfloat->exact x))
        (t x)))

;;;; Arithmetic: dispatch to Calc when a tower operand is involved

(defun tl--exact-op (calc-op native-op a b)
  "Apply CALC-OP to A and B when either is on the tower, else NATIVE-OP.
An Elisp double operand is converted first, because Calc's inexact
type is the bigfloat; both operators are binary and no complex/real
ordering is implied."
  (if (or (tl-exact-number-p a) (tl-exact-number-p b))
      (tl-calc-pure nil (funcall calc-op (tl--to-calc a) (tl--to-calc b)))
    (funcall native-op a b)))

(defun tl-num-add (a b)
  "Add A and B, exactly when either is exact, natively otherwise."
  (tl--exact-op #'math-add #'+ a b))

(defun tl-num-sub (a b)
  "Subtract B from A, exactly when either is exact, natively otherwise."
  (tl--exact-op #'math-sub #'- a b))

(defun tl-num-mul (a b)
  "Multiply A and B, exactly when either is exact, natively otherwise."
  (tl--exact-op #'math-mul #'* a b))

(defun tl-num-div (a b)
  "Divide A by B exactly, as a fraction.
Used for the `Fraction'/`Complex' domains, where `/` is exact division.
An inexact operand (bigfloat or double) carries the quotient at Calc's
working precision (12 significant digits)."
  (when (tl-num-zero-p b)
    (signal 'termlisp-eval-error '("Division by zero")))
  (tl-calc-pure nil (math-div (tl--to-calc a) (tl--to-calc b))))

(defun tl-num-quo (a b)
  "Truncating integer quotient of A and B (Aldor `quo')."
  (if (or (tl-exact-number-p a) (tl-exact-number-p b))
      (tl-calc-pure nil (math-trunc (math-div (tl--to-calc a) (tl--to-calc b))))
    (truncate a b)))

(defun tl-num-zero-p (x)
  "Return non-nil when X is numerically zero."
  (cond ((tl-fraction-p x) (zerop (tl-fraction-numerator x)))
        ((tl-complex-p x) (and (tl-num-zero-p (tl-complex-real x))
                               (tl-num-zero-p (tl-complex-imag x))))
        ((tl-bigfloat-p x) (zerop (nth 1 x)))
        (t (and (numberp x) (zerop x)))))

(defun tl-num-less-p (a b)
  "Return non-nil when A is numerically less than B.
The order covers the whole tower across representations -- fractions,
bigfloats, doubles and integers compare by exact value -- because a
tower operand sends both sides to Calc as exact fractions.  A complex
operand has no order and signals `termlisp-eval-error'."
  (when (or (tl-complex-p a) (tl-complex-p b))
    (signal 'termlisp-eval-error '("Complex numbers have no order")))
  (if (and (numberp a) (numberp b))
      (< a b)
    (tl-calc-pure nil (math-lessp (tl--to-exact a) (tl--to-exact b)))))

;;;; Builtins

(tl-register-builtin
 'tl-fraction
 (lambda (args) (tl-fraction (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-complex
 (lambda (args) (tl-complex (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-num-add (lambda (args) (tl-num-add (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-num-sub (lambda (args) (tl-num-sub (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-num-mul (lambda (args) (tl-num-mul (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-num-div (lambda (args) (tl-num-div (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-num-quo (lambda (args) (tl-num-quo (nth 0 args) (nth 1 args))))
(tl-register-builtin
 'tl-num-zero? (lambda (args) (tl-bool (tl-num-zero-p (nth 0 args)))))
(tl-register-builtin
 'tl-num-less? (lambda (args) (tl-bool (tl-num-less-p (nth 0 args) (nth 1 args)))))
(tl-register-builtin
 'tl-bigfloat (lambda (args) (tl-bigfloat (nth 0 args) (nth 1 args))))

(provide 'termlisp-numeric)
;;; termlisp-numeric.el ends here
