;;; termlisp-reader.el --- Read term-lisp source -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; Top-level forms are ordinary S-expressions read with the Emacs reader.

;;; Code:

(require 'termlisp-base)

(defun termlisp-parse (string)
  "Read all top-level forms from STRING and return them as a list."
  (with-temp-buffer
    (insert string)
    (goto-char (point-min))
    (let (forms form)
      (condition-case err
          (while (progn (skip-chars-forward " \t\n\r\f")
                        (not (eobp)))
            (setq form (read (current-buffer)))
            (push form forms))
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
