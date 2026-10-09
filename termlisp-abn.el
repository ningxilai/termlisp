;;; termlisp-abn.el --- Reader for Aldor annotated ABN trees -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Reads the S-expression emitted by `aldor -Fabn', a triple
;; (TREE SYMES SEFOS).  Id nodes in TREE carry (|syme| |ref| . N)
;; annotations indexing SYMES; syme entries carry (|type| |ref| . N)
;; annotations indexing SEFOS.  `tl-abn-resolve' splices the indexed
;; syme entry into each Id node so downstream code can read names
;; directly, and keeps the tables for type lookups.

;;; Code:

(require 'cl-lib)
(require 'termlisp-base)

(cl-defstruct (tl-abn (:constructor tl-abn--make)
                      (:copier nil))
  "An Aldor annotated tree with its symbol and type expression tables."
  (tree nil :documentation "Resolved annotated tree.")
  (symes [] :documentation "Vector of syme alists.")
  (sefos [] :documentation "Vector of type expression trees."))

(defun tl-abn-read-file (file)
  "Read the Aldor ABN FILE and return a resolved `tl-abn' struct."
  (with-temp-buffer
    (insert (tl-abn--escape-pipes
             (with-temp-buffer
               (insert-file-contents file)
               (buffer-string))))
    (goto-char (point-min))
    (let* ((max-lisp-eval-depth (max (* 4 max-lisp-eval-depth) 65536))
           (form (condition-case err
                     (read (current-buffer))
                  (end-of-file
                   (signal 'termlisp-abn-error
                           (list (format "%s: truncated ABN data" file))))
                  (error
                   (signal 'termlisp-abn-error
                           (list (format "%s: %s" file (error-message-string err))))))))
      (unless (and (consp form) (null (cdddr form)))
        (signal 'termlisp-abn-error
                (list (format "%s: not an ABN (TREE SYMES SEFOS) triple" file))))
      (tl-abn-resolve form))))

(defun tl-abn--escape-pipes (text)
  "Rewrite Aldor |...| symbol escapes in TEXT for the Emacs reader.
The Emacs reader does not treat vertical bars as symbol escapes, and
characters such as # ; \" ( ) inside a token break reading.  Every
character between a pair of bars is backslash-escaped and the bars are
dropped, so the reader recovers the raw name.  Bars inside string
literals are left untouched.  Raw ? outside strings and bars is escaped:
? starts an Elisp character literal that swallows the following
parenthesis.  A raw \\ followed by another character is copied as an
Aldor digit-name escape (\\1 means the name 1); Elisp's own backslash
escape then recovers the name."
  (let ((i 0) (n (length text)) (out nil))
    (while (< i n)
      (let ((c (aref text i)))
        (cond
         ((eq c ?\")
          (let ((start i))
            (setq i (1+ i))
            (while (and (< i n) (not (eq (aref text i) ?\")))
              (setq i (+ i (if (eq (aref text i) ?\\) 2 1))))
            (setq i (min (1+ i) n))
            (push (substring text start i) out)))
         ((eq c ?|)
          (let ((close (cl-position ?| text :start (1+ i))))
            (if close
                (progn
                  (let ((k (1+ i)))
                    (while (< k close)
                      (push (string ?\\ (aref text k)) out)
                      (setq k (1+ k))))
                  (setq i (1+ close)))
              (push "|" out)
              (setq i (1+ i)))))
         ((eq c ?\\)
          (push (string c) out)
          (when (< (1+ i) n)
            (push (string (aref text (1+ i))) out))
          (setq i (+ i 2)))
         ((eq c ??)
          (push (string ?\\ c) out)
          (setq i (1+ i)))
         (t (push (string c) out) (setq i (1+ i))))))
    (apply #'concat (nreverse out))))

(defun tl-abn-resolve (form)
  "Resolve ABN triple FORM into a `tl-abn' struct.
Pipe-escaped symbols (Aldor writes |foo|) are normalized to their
unescaped names first, because the Emacs Lisp reader does not treat
vertical bars as symbol escapes."
  (unless (and (consp form) (consp (cdr form)) (consp (cddr form)))
    (signal 'termlisp-abn-error (list (format "Not an ABN triple: %S" form))))
  (let* ((tree (tl-abn--strip-pipes (car form)))
         (symes (vconcat (tl-abn--strip-pipes (cadr form))))
         (sefos (vconcat (tl-abn--strip-pipes (caddr form)))))
    (tl-abn--make :tree (tl-abn--resolve-node tree symes)
                  :symes symes
                  :sefos sefos)))

(defun tl-abn--strip-pipes (x)
  "Recursively unescape |foo|-style symbols in X."
  (cond ((symbolp x)
         (let* ((name (symbol-name x))
                (len (length name)))
           (if (and (> len 2)
                    (eq (aref name 0) ?|)
                    (eq (aref name (1- len)) ?|))
               (intern (substring name 1 -1))
             x)))
        ((vectorp x) (vconcat (mapcar #'tl-abn--strip-pipes x)))
        ((consp x) (cons (tl-abn--strip-pipes (car x))
                         (tl-abn--strip-pipes (cdr x))))
        (t x)))

(defun tl-abn-node-p (node &optional tag)
  "Return non-nil if NODE is an annotated node, optionally tagged TAG."
  (and (consp node)
       (if tag (eq (car node) tag) t)))

(defun tl-abn-id-syme (id)
  "Return the resolved syme alist of Id node ID, or nil.
An unresolved (syme ref . N) annotation -- as carried by ids inside
raw sefos -- is not a syme alist, so it yields nil; use
`tl-aldor--raw-id-syme' (termlisp-aldor) to follow raw refs."
  (let ((ann (assq 'syme (cdr id))))
    (when (consp ann)
      (let ((syme (cdr ann)))
        (and (consp syme)
             (not (and (eq (car syme) 'ref) (integerp (cdr syme))))
             syme)))))

(defun tl-abn-syme-name (syme)
  "Return the name symbol of syme alist SYME, or nil."
  (let ((ann (assq 'name syme)))
    (and ann (cdr ann))))

(defun tl-abn-id-name-cell (id)
  "Return the (name . SYM) annotation cell of resolved Id node ID, or nil.
Distinguishes an absent name annotation from a present one whose value
is the symbol nil (Aldor's nil constant)."
  (let ((syme (tl-abn-id-syme id)))
    (if syme
        (assq 'name syme)
      (assq 'name (cdr id)))))

(defun tl-abn-id-name (id)
  "Return the name symbol of resolved Id node ID, or nil.
Works both for nodes carrying a syme and for state-only nodes
carrying a bare (|name| . SYM) annotation.  Use
`tl-abn-id-name-cell' when the name may itself be nil."
  (let ((cell (tl-abn-id-name-cell id)))
    (and cell (cdr cell))))

(defun tl-abn-syme-type (abn syme)
  "Return the type expression of SYME in ABN, or nil.
The type annotation is spliced from the sefo table of ABN."
  (let ((ty (cdr (assq 'type syme))))
    (cond ((null ty) nil)
          ((and (consp ty) (eq (car ty) 'ref))
           (aref (tl-abn-sefos abn) (cdr ty)))
          (t ty))))

(defun tl-abn-id-srcpos (id)
  "Return the (FILE LINE COL) srcpos list of Id node ID, or nil."
  (cdr (assq 'srcpos (cdr id))))

(defun tl-abn--resolve-node (node symes)
  (cond ((not (consp node)) node)
        ((eq (car node) 'Id)
         (cons 'Id
               (mapcar (lambda (ann) (tl-abn--resolve-ann ann symes))
                       (cdr node))))
        (t (cons (car node)
                 (mapcar (lambda (x) (tl-abn--resolve-node x symes))
                         (cdr node))))))

(defun tl-abn--resolve-ann (ann symes)
  (if (and (consp ann) (eq (car ann) 'syme)
           (consp (cdr ann)) (eq (cadr ann) 'ref)
           (integerp (cddr ann)))
      (let ((idx (cddr ann)))
        (unless (< idx (length symes))
          (signal 'termlisp-abn-error (list (format "syme ref %d out of range" idx))))
        (cons 'syme (aref symes idx)))
    ann))

(define-error 'termlisp-abn-error "Aldor ABN read error" 'termlisp-error)

(provide 'termlisp-abn)
;;; termlisp-abn.el ends here
