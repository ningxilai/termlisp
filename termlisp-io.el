;;; termlisp-io.el --- State-monad I/O runtime -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Runtime support for Aldor's TextReader/TextWriter/File/Character/String
;; operations, built on a State monad.
;;
;; The world is threaded through a `State' computation `s -> (a . s)'.
;; A TextReader is a *box* holding the remaining input -- the state `s'
;; of the reader monad is an input string -- and `read!' is a State
;; action that pops one Character off the front and commits the rest.
;; Characters are character codes (integers); `eof' is -1.  Strings are
;; Emacs strings.  Readers and writers are the same box type so the
;; erasing `f::TextReader' / `f::TextWriter' coercions are the identity.

;;; Code:

(defvar tl-eof -1
  "The end-of-file Character code.")

(defvar tl-space 32
  "The space Character code.")

(defvar tl-newline 10
  "The newline Character code.")

;;; Store: handles are integer ids into a global object table.
;;; A handle is thus a plain value whose copy is the same handle, so
;;; substitutions never duplicate the underlying object.

(defvar tl-store (make-hash-table :test #'eql)
  "Global store mapping handle ids to their objects.")

(defvar tl-store-next 0
  "Next handle id to hand out.")

(defun tl-store-alloc (object)
  "Store OBJECT and return a fresh handle id."
  (let ((id (cl-incf tl-store-next)))
    (puthash id object tl-store)
    id))

(defun tl-store-ref (id)
  "Return the object stored under handle ID."
  (gethash id tl-store))

(defun tl-handle (x)
  "Resolve handle X (an id, or an object used directly) to its object."
  (if (integerp x)
      (or (tl-store-ref x) (error "Bad handle: %S" x))
    x))

;;; State monad: a computation is s -> (a . s).

(defun tl-st-return (v)
  "Return monadic value V."
  (lambda (s) (cons v s)))

(defun tl-st-bind (m k)
  "Bind monadic value M to continuation K."
  (lambda (s)
    (let ((p (funcall m s)))
      (funcall (funcall k (car p)) (cdr p)))))

(defun tl-st-get ()
  "Return the current state."
  (lambda (s) (cons s s)))

(defun tl-st-put (v)
  "Replace the state with V."
  (lambda (_s) (cons nil v)))

(defun tl-st-run (m s)
  "Run monadic computation M in initial state S."
  (funcall m s))

;;; Readers.

(defun tl-make-reader (string)
  "Make a TextReader over STRING."
  (list (or string "")))

(defun tl-reader (x)
  "Coerce X to a TextReader (the identity)."
  x)

(defun tl--stdin-string ()
  "Return the initial standard-input text."
  (let ((f (getenv "TL_STDIN_FILE")))
    (cond ((and f (file-readable-p f))
           (with-temp-buffer (insert-file-contents f) (buffer-string)))
          ((and f (string= f "-")) "")
          (t ""))))

(defvar tl-stdin (tl-store-alloc (tl-make-reader (tl--stdin-string)))
  "Standard input as a TextReader handle.")

(defun tl-read! (handle)
  "Pop and return the next Character from the reader HANDLE, or `tl-eof'."
  (let* ((box (tl-handle handle))
         (s (car box))
         (p (tl-st-run
             (tl-st-bind
              (tl-st-get)
              (lambda (state)
                (if (= (length state) 0)
                    (tl-st-return tl-eof)
                  (tl-st-bind
                   (tl-st-put (substring state 1))
                   (lambda (_ignored) (tl-st-return (aref state 0)))))))
             s)))
    (setcar box (cdr p))
    (car p)))

(defun tl-read-line (box)
  "Read and return the rest of the current line from reader BOX."
  (let ((out "") (c (tl-read! box)))
    (while (and (/= c tl-eof) (/= c tl-newline))
      (setq out (concat out (string c)))
      (setq c (tl-read! box)))
    out))

;;; Writers.

(defun tl-write! (c handle)
  "Write Character C to the writer HANDLE; return C."
  (let ((box (tl-handle handle)))
    (cond ((eq box 'tl-stdout) (princ (string c)))
          ((consp box) (setcdr box (concat (cdr box) (string c))))
          (t (princ (string c)))))
  c)

(defun tl-output-char (writer c)
  "Print Character C for the prelude `<<', returning WRITER."
  (cond ((eq writer 'tl-stdout) (princ (string c)))
        ((consp writer) (setcdr writer (concat (cdr writer) (string c))))
        (t (princ (string c))))
  writer)

(defun tl-lines (handle)
  "Return a generator closure over the lines of reader HANDLE."
  (let* ((box (tl-handle handle))
         (s (car box))
         (parts (split-string s "\n"))
         (lines (if (and parts (string= (car (last parts)) "") (> (length parts) 0))
                    (butlast parts)
                  parts)))
    (setcar box "")
    (lambda ()
      (if (null lines)
          'tl-gen-done
        (let ((line (car lines)))
          (setq lines (cdr lines))
          line)))))

;;; Characters and strings.

(defun tl-char (s)
  "Return the Character code of the first character of string S."
  (aref s 0))

(defun tl-length (s)
  "Return the length of string S."
  (length s))

(defun tl-substring (s i n)
  "Return the N-character substring of S starting at I.

Aldor's String is 0-based, so indices map directly onto Emacs strings."
  (substring s i (+ i n)))

(defun tl-concat (a b)
  "Concatenate strings A and B."
  (concat a b))

(defun tl-right-trim (s c)
  "Remove trailing Character C from string S."
  (let ((ch (string c)))
    (while (and (> (length s) 0) (string= (substring s -1) ch))
      (setq s (substring s 0 -1)))
    s))

(defun tl-new-string (n c)
  "Return a string of N copies of Character C."
  (make-string n c))

;;; Files.

;; The Aldor library's file-mode constants.  The lowerer maps the Aldor
;; names `fileRead'/`fileWrite' onto these prefixed variables, so no
;; unprefixed global is needed.
(defconst tl-file-read 'fileRead
  "Value of the Aldor `fileRead' file-mode constant.")
(defconst tl-file-write 'fileWrite
  "Value of the Aldor `fileWrite' file-mode constant.")

(defun tl-open (path mode)
  "Open PATH for reading (MODE `tl-file-read') or writing.
Return a store handle for the file."
  (tl-store-alloc
   (if (eq mode tl-file-read)
       (list (if (file-readable-p path)
                 (with-temp-buffer (insert-file-contents path) (buffer-string))
               ""))
     (cons path ""))))

(defun tl-close! (handle)
  "Close the file HANDLE, flushing a writer's buffer to disk."
  (let ((f (tl-handle handle)))
    (when (and (consp f) (stringp (car f)) (stringp (cdr f)))
      (with-temp-file (car f) (insert (cdr f)))))
  handle)

(provide 'termlisp-io)
;;; termlisp-io.el ends here
