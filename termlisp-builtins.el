;;; termlisp-builtins.el --- Primitive functions -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Builtins receive a list of already-forced argument values.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)
(require 'termlisp-machine)

(declare-function tl-force "termlisp-eval" (value))

(defun tl-force-or-identity (v)
  "Force V with `tl-force' when available, else return V."
  (if (and (tl-thunk-p v) (fboundp 'tl-force))
      (tl-force v)
    v))

(defvar tl-builtins (make-hash-table :test #'eq)
  "Registry mapping builtin names to functions of a list of values.")

(defun tl-builtin-p (name)
  "Return non-nil if NAME is a builtin."
  (gethash name tl-builtins))

(defun tl-register-builtin (name fn)
  "Register builtin NAME implemented by FN."
  (puthash name fn tl-builtins))

(defun tl-bool (b) (if b 'True 'False))

(defun tl-check-numbers (args name)
  "Signal `termlisp-type-error' unless ARGS is two numbers."
  (unless (= (length args) 2)
    (signal 'termlisp-type-error
            (list (format "%s expects 2 arguments, got %d" name (length args)))))
  (dolist (a args)
    (unless (numberp a)
      (signal 'termlisp-type-error
              (list (format "%s expects numbers, got %S" name a))))))

(tl-register-builtin 'eq
  (lambda (args)
    (tl-bool (tl-value-equal (nth 0 args) (nth 1 args) #'tl-force-or-identity))))
(tl-register-builtin '+
  (lambda (args) (tl-check-numbers args '+) (+ (nth 0 args) (nth 1 args))))
(tl-register-builtin '-
  (lambda (args)
    (unless (memq (length args) '(1 2))
      (signal 'termlisp-type-error
              (list (format "- expects 1 or 2 arguments, got %d"
                            (length args)))))
    (dolist (a args)
      (unless (numberp a)
        (signal 'termlisp-type-error
                (list (format "- expects numbers, got %S" a)))))
    (if (cdr args)
        (- (nth 0 args) (nth 1 args))
      (- (nth 0 args)))))
(tl-register-builtin '*
  (lambda (args) (tl-check-numbers args '*) (* (nth 0 args) (nth 1 args))))
(tl-register-builtin '<
  (lambda (args) (tl-check-numbers args '<) (tl-bool (< (nth 0 args) (nth 1 args)))))
(tl-register-builtin '<=
  (lambda (args) (tl-check-numbers args '<=) (tl-bool (<= (nth 0 args) (nth 1 args)))))
(tl-register-builtin '>
  (lambda (args) (tl-check-numbers args '>) (tl-bool (> (nth 0 args) (nth 1 args)))))
(tl-register-builtin '>=
  (lambda (args) (tl-check-numbers args '>=) (tl-bool (>= (nth 0 args) (nth 1 args)))))

(defun tl-list-cons-p (v)
  "Return non-nil if V is a termlisp Cons cell."
  (and (consp v) (eq (car v) 'Cons)))

(defun tl-vector-to-list (v)
  "Convert vector V into the termlisp Cons chain of its elements."
  (let ((r 'Nil)
        (i (1- (length v))))
    (while (>= i 0)
      (setq r (list 'Cons (aref v i) r))
      (setq i (1- i)))
    r))

(defun tl-elements (v)
  "Return a Cons chain of the elements of V (a vector or a Cons list).
Used to iterate a value whose static type is unknown, so an Array and a
List are walkable by the same code."
  (if (vectorp v) (tl-vector-to-list v) v))

(defun tl-list-to-vector (l)
  "Convert the termlisp Cons chain L into a vector."
  (let ((n 0)
        (p l))
    (while (tl-list-cons-p p)
      (setq n (1+ n))
      (setq p (caddr p)))
    (let ((v (make-vector n nil))
          (i 0))
      (setq p l)
      (while (tl-list-cons-p p)
        (aset v i (cadr p))
        (setq i (1+ i))
        (setq p (caddr p)))
      v)))

(defun tl-check-one-arg (args name)
  "Signal `termlisp-type-error' unless ARGS holds exactly one value."
  (unless (= (length args) 1)
    (signal 'termlisp-type-error
            (list (format "%s expects 1 argument, got %d"
                          name (length args))))))

(tl-register-builtin 'first
  (lambda (args)
    (tl-check-one-arg args 'first)
    (let ((v (nth 0 args)))
      (if (tl-list-cons-p v)
          (cadr v)
        (signal 'termlisp-type-error
                (list (format "first expects a Cons, got %S" v)))))))

(tl-register-builtin 'rest
  (lambda (args)
    (tl-check-one-arg args 'rest)
    (let ((v (nth 0 args)))
      (if (tl-list-cons-p v)
          (caddr v)
        (signal 'termlisp-type-error
                (list (format "rest expects a Cons, got %S" v)))))))

(tl-register-builtin 'empty?
  (lambda (args)
    (tl-check-one-arg args 'empty?)
    (tl-bool (eq (nth 0 args) 'Nil))))

;;; Aldor output runtime ------------------------------------------------
;; The Aldor prelude's `stdout'/`newline'/`<<' have no termlisp
;; equivalent; emitted programs resolve them to these runtime values.
;; A program that defines its own `<<' (an OutputType method) keeps
;; that name -- only the prelude operator is renamed.

(defvar tl-gen-done (list 'tl-gen-done)
  "Unique value a lazy generator returns when exhausted.")

(defvar tl-stdout 'tl-stdout
  "Stand-in for Aldor's `stdout' TextWriter.")

(defvar tl-newline 10
  "Aldor's `newline' Character code.")

(defun tl-output--list-items (l)
  "Return the elements of the termlisp Cons chain L."
  (let (items)
    (while (tl-list-cons-p l)
      (push (cadr l) items)
      (setq l (caddr l)))
    (nreverse items)))

(defun tl-output--format (value)
  "Render VALUE the way Aldor's basic OutputType instances print."
  (cond ((tl-list-cons-p value)
         (concat "[" (mapconcat #'tl-output--format
                                (tl-output--list-items value) ",") "]"))
        ;; Arrays, records and unions are vectors; print them like
        ;; Aldor's `[a,b,c]'.
        ((vectorp value)
         (concat "[" (mapconcat #'tl-output--format (append value nil) ",")
                 "]"))
        ((eq value 'Nil) "[]")
        ((eq value t) "true")
        ((eq value nil) "false")
        ((stringp value) value)
        (t (format "%s" value))))

(defun tl-output-value (value)
  "Print VALUE the way the prelude `<<' prints a basic OutputType."
  (princ (tl-output--format value)))

(defun tl-output-<< (writer value)
  "Print VALUE for the prelude output operator, returning WRITER."
  (tl-output-value value)
  writer)

(defun tl-format (value)
  "Format VALUE as a String (unary `<<')."
  (tl-output--format value))

(defun %guard (test body)
  "Runtime backing for a parameter type guard emitted by the lowering."
  (if test body (error "No applicable method (guard failed)")))

(defun tl-print (fmt)
  "FormattedOutput `print': return a function taking the format args.
Supports `~a' (consume an argument), `~n' (newline) and `~~'."
  (lambda (&rest args)
    (let ((i 0) (out "") (s fmt))
      (while (string-match "~\\([an~]\\)" s)
        (setq out (concat out (substring s 0 (match-beginning 0))))
        (pcase (match-string 1 s)
          ("a" (setq out (concat out (format "%s" (nth i args))))
               (setq i (1+ i)))
          ("n" (setq out (concat out "\n")))
          ("~" (setq out (concat out "~"))))
        (setq s (substring s (match-end 0))))
      (princ (concat out s)))))

(defun nputs (n text)
  "Stand-in for the C foreign function `nputs': print TEXT N times."
  (terpri)
  (dotimes (_ n n)
    (princ text)
    (terpri)))

;;; Aldor step operations ----------------------------------------------
;; `prev'/`next' are the predecessor/successor operations of the
;; prelude's integer StepType.

(defun tl-prev (n) (1- n))
(defun tl-next (n) (1+ n))

;; `explode r' returns the fields of a record/union value as a tuple;
;; records are vectors, so this is the identity.
(defun tl-explode (v) v)

(defun tl-copy (v) v)

(defun tl-sort! (l)
  "Sort the termlisp Cons-list L, returning a fresh sorted list.
The comparison is chosen by the element type; the corpus uses
strings and integers."
  (let ((items nil)
        (p l))
    (while (tl-list-cons-p p)
      (push (cadr p) items)
      (setq p (caddr p)))
    (setq items (sort (nreverse items)
                      (lambda (a b)
                        (cond ((and (stringp a) (stringp b)) (string< a b))
                              ((and (numberp a) (numberp b)) (< a b))
                              (t (string< (format "%s" a)
                                          (format "%s" b)))))))
    (let ((r 'Nil))
      (dolist (i (reverse items) r)
        (setq r (list 'Cons i r))))))

;; `nil? p' tests a Pointer for null; the null pointer is `Nil'.
(defun tl-pointer-null-p (p) (or (null p) (eq p 'Nil)))

(provide 'termlisp-builtins)
;;; termlisp-builtins.el ends here
