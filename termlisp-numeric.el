;;; termlisp-numeric.el --- Exact arithmetic backend over Calc -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; The primitive arithmetic in `termlisp-builtins' works on native Elisp
;; numbers, which model Aldor's `Integer'/`DoubleFloat' and the fixed-width
;; machine integers.  Two domains are not representable that way: exact
;; rationals (`Fraction') and complex numbers (`Complex').  This module
;; implements them on top of Emacs Calc:
;;
;;   Fraction  a normalised Calc fraction `(frac NUM DEN)'
;;   Complex   a Calc rectangular complex     `(cplx RE IM)'
;;
;; Native values are handled by the ordinary Elisp operators, so the fast
;; path used by the corpus is untouched; `tl-exact-number-p' tells the two
;; apart.  Calc is an optional dependency, loaded lazily on the first exact
;; operation so that merely loading termlisp stays cheap.
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
(declare-function math-big-p "calc" (a))
(declare-function math-trunc "calc" (a))

;; Calc options honoured dynamically; declared here so the binds below are
;; dynamic under lexical-binding.
(defvar calc-prefer-frac)

(defun tl-calc-ensure ()
  "Load Calc on first use.  Return non-nil."
  (require 'calc))

(defun tl-exact-number-p (x)
  "Return non-nil when X is a value of the exact (Calc-backed) tower.
A fraction (a `frac' cons), a complex (a `cplx' cons) or a Calc bignum."
  (or (and (consp x) (memq (car x) '(frac cplx)))
      (and (fboundp 'math-big-p) (math-big-p x))))

;;;; Fractions

(defun tl-fraction (n d)
  "Return the exact fraction N/D, normalised.
Signal `termlisp-eval-error' when D is zero."
  (tl-calc-ensure)
  (when (zerop d)
    (signal 'termlisp-eval-error '("Division by zero constructing a Fraction")))
  (math-normalize (list 'frac n d)))

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
  "Return the complex number with real part RE and imaginary part IM."
  (tl-calc-ensure)
  (math-normalize (list 'cplx re im)))

(defun tl-complex-p (x)
  "Return non-nil when X is a complex number."
  (and (consp x) (eq (car x) 'cplx)))

(defun tl-complex-real (x)
  "Return the real part of the complex number X."
  (nth 1 x))

(defun tl-complex-imag (x)
  "Return the imaginary part of the complex number X."
  (nth 2 x))

;;;; Arithmetic: dispatch to Calc when an exact operand is involved

(defun tl--exact-op (calc-op native-op a b)
  "Apply CALC-OP to A and B when either is exact, else NATIVE-OP.
No complex/real ordering is implied; both operators are binary."
  (if (or (tl-exact-number-p a) (tl-exact-number-p b))
      (progn (tl-calc-ensure) (funcall calc-op a b))
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
Used for the `Fraction'/`Complex' domains, where `/` is exact division."
  (tl-calc-ensure)
  (when (tl-num-zero-p b)
    (signal 'termlisp-eval-error '("Division by zero")))
  (let ((calc-prefer-frac t))
    (math-div a b)))

(defun tl-num-quo (a b)
  "Truncating integer quotient of A and B (Aldor `quo')."
  (if (or (tl-exact-number-p a) (tl-exact-number-p b))
      (progn (tl-calc-ensure) (math-trunc (math-div a b)))
    (truncate a b)))

(defun tl-num-zero-p (x)
  "Return non-nil when X is numerically zero."
  (cond ((tl-fraction-p x) (zerop (tl-fraction-numerator x)))
        ((tl-complex-p x) (and (tl-num-zero-p (tl-complex-real x))
                               (tl-num-zero-p (tl-complex-imag x))))
        (t (and (numberp x) (zerop x)))))

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

(provide 'termlisp-numeric)
;;; termlisp-numeric.el ends here
