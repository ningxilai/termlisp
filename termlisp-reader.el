;;; termlisp-reader.el --- Read term-lisp source -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Top-level forms are ordinary S-expressions read with the Emacs reader.
;;
;; Trust boundary: this reader accepts the full Emacs Lisp reader grammar
;; (vectors, records, `#1=' labels, and so on) and is intended for trusted
;; term-lisp source, not arbitrary untrusted input.  Circular `#1='
;; structures are rejected by binding `read-circle' to nil, and read-time
;; evaluation is disabled on Emacsen where `read-eval' is bound.

;;; Code:

(require 'termlisp-base)

(defconst termlisp--reader-whitespace
  (concat "\000-\040" (string #xa0))
  "Characters the Emacs reader skips as whitespace.
The reader treats all C0 controls (0x00-0x20) and NBSP (0xA0) as
trivia.  `termlisp-parse' skips the same set before each read so that a
buffer ending in such whitespace is not mistaken for an unterminated
form; the reader would otherwise consume the trivia, hit end of file,
and signal a spurious `end-of-file'.")

(defun termlisp--skip-trivia ()
  "Skip whitespace and `;' line comments.  Return non-nil if a form follows."
  (skip-chars-forward termlisp--reader-whitespace)
  (while (and (not (eobp)) (eq (char-after) ?\;))
    (end-of-line)
    (skip-chars-forward termlisp--reader-whitespace))
  (not (eobp)))

(defun termlisp-parse (string)
  "Read all top-level forms from STRING and return them as a list."
  (with-temp-buffer
    (insert string)
    (goto-char (point-min))
    ;; `read-eval' was removed in Emacs 32, where `#.' is invalid syntax;
    ;; on older Emacsen it defaults to t, so turn it off buffer-locally.
    (when (boundp 'read-eval)
      (set (make-local-variable 'read-eval) nil))
    (let ((read-circle nil)
          (forms nil))
      (condition-case err
          (while (termlisp--skip-trivia)
            (push (read (current-buffer)) forms))
        (end-of-file
         (signal 'termlisp-parse-error
                 (list "Unbalanced parentheses: unexpected end of input")))
        (error
         (signal 'termlisp-parse-error
                 (list (format "Parse error at %d: %s"
                               (point) (error-message-string err))))))
      (nreverse forms))))

(defun termlisp-parse-file (file)
  "Read all top-level forms from FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (termlisp-parse (buffer-string))))

(provide 'termlisp-reader)
;;; termlisp-reader.el ends here
