;;; termlisp.el --- Lazy term-rewriting language -*- lexical-binding: t; -*-

;;; Commentary:
;; Embedded library API for term-lisp.

;;; Code:

(defvar termlisp--root
  (file-name-directory (or load-file-name buffer-file-name))
  "Root directory of the termlisp package.")

(add-to-list 'load-path (expand-file-name "vendor/cats" termlisp--root))

(dolist (feature '(termlisp-base termlisp-reader termlisp-unify
                   termlisp-machine termlisp-pattern termlisp-builtins
                   termlisp-eval))
  (when (locate-library (symbol-name feature))
    (require feature)))

(provide 'termlisp)
;;; termlisp.el ends here
