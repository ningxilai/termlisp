;;; termlisp-repl.el --- Interactive REPL for term-lisp -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A comint-driven REPL for term-lisp, modelled on IELM.  Evaluation runs in
;; the running Emacs, so definitions made at the prompt stay in the session
;; and can be inspected from ordinary Emacs Lisp.
;;
;; The buffer is the whole front-end: comint does the line editing, history
;; and echo, and every question about term-lisp itself is answered through
;; the library's API -- `termlisp-read-complete-p' says whether an input may
;; be sent, `termlisp-eval-submission' evaluates it as one unit and returns
;; the printed value.  No interpreter wiring lives in this file; it formats
;; what comes back.
;;
;; The buffer hosts a placeholder process: comint insists on one, but it never
;; receives input.  `comint-input-sender' is replaced by
;; `termlisp-repl--send', which evaluates the input comint just echoed and
;; writes the answer back with `comint-output-filter'.
;;
;; RET sends the input only when it reads as a sequence of complete top-level
;; forms; an unfinished form moves to the next line instead, so a form can be
;; typed across several lines without an escape character.  An input of
;; `exit' or `quit' closes the REPL.
;;
;; The environment starts from `termlisp-repl-options', plus the prelude when
;; `termlisp-repl-load-prelude' is non-nil, plus every file named by
;; `termlisp-repl-load-files'.  The banner lists the journal of loads the
;; environment kept, so it names what is actually loaded.

;;; Code:

(require 'comint)
(require 'termlisp-eval)
(require 'termlisp-load)
(require 'termlisp-reader)

(defgroup termlisp-repl nil
  "Interactive REPL for term-lisp."
  :group 'termlisp
  :prefix "termlisp-repl-")

(defcustom termlisp-repl-buffer-name "*termlisp-repl*"
  "Name of the buffer created by `termlisp-repl'."
  :type 'string
  :group 'termlisp-repl)

(defcustom termlisp-repl-prompt "λ> "
  "Prompt printed before each read."
  :type 'string
  :group 'termlisp-repl)

(defcustom termlisp-repl-options '(:type-check t)
  "Option plist used to build the environment of a new REPL buffer.
Passed to `termlisp-make-env'.  An existing buffer keeps the options it
was created with; see `termlisp-repl-toggle-type-check' and
`termlisp-repl-restart'."
  :type 'plist
  :group 'termlisp-repl)

(defcustom termlisp-repl-load-prelude t
  "When non-nil, load `termlisp-prelude.tls' into a fresh environment."
  :type 'boolean
  :group 'termlisp-repl)

(defcustom termlisp-repl-load-files nil
  "Files loaded into a fresh REPL environment after the prelude.
Each entry goes through `termlisp-load'; a file that fails to load
signals, so a typo in this list is loud rather than silently absent
from the banner.  The banner names what the environment actually
holds -- its `tl-env-loads' journal, these files included -- not what
was asked for."
  :type '(repeat file)
  :group 'termlisp-repl)

(defconst termlisp-repl-font-lock-keywords
  `(("\\_<\\(?:define\\|datatype-extension\\|datatype\\|class\\|instance\\|lambda\\|do\\)\\_>"
     . font-lock-keyword-face)
    ("\\(?:\\`\\|[() \t\n]\\)\\(:[[:alnum:]+*/_<>!?=.-]*\\)"
     (1 font-lock-builtin-face)))
  "Font-lock keywords used by `termlisp-repl-mode'.")

(defvar termlisp-repl-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; The second character of a descriptor names the partner, and it is
    ;; from there that `matching-paren' answers -- electric-pair asks it
    ;; what a typed opener should be paired with.  Classes alone pair
    ;; nothing, and a nil answer pairs the character with itself.
    (modify-syntax-entry ?\( "()" table)
    (modify-syntax-entry ?\) ")(" table)
    (modify-syntax-entry ?\[ "(]" table)
    (modify-syntax-entry ?\] ")[" table)
    (modify-syntax-entry ?\{ "(}" table)
    (modify-syntax-entry ?\} "){" table)
    (modify-syntax-entry ?\; "<" table)
    (modify-syntax-entry ?\n ">" table)
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?\\ "\\" table)
    (dolist (char '(?\' ?\` ?\,))
      (modify-syntax-entry char "'" table))
    (dolist (char (string-to-list "!#$%&|*+-/:<=>?@^_.~"))
      (modify-syntax-entry char "_" table))
    table)
  "Syntax table for `termlisp-repl-mode'.")

(defvar-local termlisp-repl--env nil
  "Term-lisp environment evaluated by the current REPL buffer.")

(defvar-local termlisp-repl--options nil
  "Option plist `termlisp-repl--env' was built from.")

;;; Environment

(defun termlisp-repl--reset-env ()
  "Give the current REPL buffer a fresh environment."
  (setq termlisp-repl--env (termlisp-make-env termlisp-repl--options))
  (when termlisp-repl-load-prelude
    (termlisp-load-prelude termlisp-repl--env))
  (dolist (file termlisp-repl-load-files)
    (termlisp-load file termlisp-repl--env)))

(defun termlisp-repl--banner ()
  "Return the text written when a REPL buffer is created.
The welcome line names what the environment holds -- the journal of
loads in `tl-env-loads', in the order they were loaded -- rather
than what the options asked for, so what is listed and what is
loaded cannot disagree."
  (let ((loads (mapcar (lambda (record)
                         (file-name-nondirectory
                          (tl-load-record-file record)))
                       (reverse (tl-env-loads termlisp-repl--env)))))
    (concat
     (format "Welcome to term-lisp%s.\n"
             (if loads
                 (format " (loaded: %s)" (string-join loads ", "))
               " (empty environment)"))
     (format "Options: %S.  Type `exit' to quit, %s to continue a form on the next line.\n"
             termlisp-repl--options
             (substitute-command-keys "\\[termlisp-repl-newline]")))))

(defun termlisp-repl--start ()
  "Create the placeholder process, environment, banner and prompt."
  (unless (comint-check-proc (current-buffer))
    (let ((proc (make-pipe-process :name "termlisp-repl"
                                   :buffer (current-buffer)
                                   :noquery t
                                   :filter #'ignore
                                   :sentinel #'ignore)))
      (set-process-filter proc #'comint-output-filter)
      (set-marker (process-mark proc) (point-max))
      (setq-local comint-inhibit-carriage-motion t)
      (setq termlisp-repl--options (copy-sequence termlisp-repl-options))
      (termlisp-repl--reset-env)
      (goto-char (point-max))
      (when (zerop (buffer-size))
        (comint-output-filter proc (termlisp-repl--banner)))
      (comint-output-filter proc termlisp-repl-prompt)
      (set-marker comint-last-input-start
                  (marker-position (process-mark proc))))))

(defun termlisp-repl--teardown ()
  "Delete the placeholder process of the current buffer."
  (let ((proc (get-buffer-process (current-buffer))))
    (when (and proc (process-live-p proc))
      (set-process-query-on-exit-flag proc nil)
      (delete-process proc))))

;;; Input and output

(defun termlisp-repl--pending-input ()
  "Return the input between the process mark and point, or nil.
Nil means point is not in the input, in which case comint decides what
to send."
  (let ((proc (get-buffer-process (current-buffer))))
    (when proc
      (let ((beg (marker-position (process-mark proc))))
        (when (>= (point) beg)
          (buffer-substring-no-properties beg (point)))))))

(defun termlisp-repl--exit-p (input)
  "Return non-nil if INPUT is the REPL `exit' or `quit' command."
  (string-match-p "\\`[ \t\n]*\\(?:exit\\|quit\\)[ \t\n]*\\'" input))

(defun termlisp-repl--error-message (err)
  "Return a short display string for condition ERR."
  (let ((data (cdr-safe err)))
    (if (and (= (length data) 1) (stringp (car data)))
        (car data)
      (error-message-string err))))

(defun termlisp-repl--write (string)
  "Insert STRING as output of the current REPL buffer's process."
  (let ((proc (get-buffer-process (current-buffer))))
    (when proc
      (comint-output-filter proc string))))

(defun termlisp-repl--send (_proc input)
  "Evaluate INPUT and write the answer back to the buffer.
This is the value of `comint-input-sender'; comint has already echoed
INPUT and advanced the process mark."
  (if (termlisp-repl--exit-p input)
      (termlisp-repl--write "Bye.\n")
    (unwind-protect
        (condition-case err
            (let ((result (termlisp-eval-submission input termlisp-repl--env)))
              (when result
                (termlisp-repl--write (concat result "\n"))))
          (quit (termlisp-repl--write "Quit\n"))
          ;; Goals are not an error: they are the answer to what the
          ;; program left open, and saying so plainly is the whole point
          ;; of writing `_' in the first place.
          (termlisp-hole
           (termlisp-repl--write
            (concat (mapconcat #'identity (cadr err) "\n") "\n")))
          (error (termlisp-repl--write
                  (concat "error: " (termlisp-repl--error-message err) "\n"))))
      (termlisp-repl--write termlisp-repl-prompt))))

;;; Commands

(defun termlisp-repl-return ()
  "Send the input after the prompt, or move an unfinished form down a line.
The input is sent when it reads as a sequence of complete top-level
forms; otherwise a newline and an indentation are inserted."
  (interactive)
  (let ((input (termlisp-repl--pending-input)))
    (cond
     ((and input (termlisp-repl--exit-p input))
      (comint-send-input)
      (termlisp-repl-exit))
     ((or (null input) (termlisp-read-complete-p input))
      (comint-send-input))
     (t
      (newline-and-indent)))))

(defun termlisp-repl-newline ()
  "Insert a newline without sending the input."
  (interactive)
  (newline-and-indent))

(defun termlisp-repl-exit ()
  "Close the term-lisp REPL, killing its buffer."
  (interactive)
  (unless (derived-mode-p 'termlisp-repl-mode)
    (user-error "Not in a term-lisp REPL buffer"))
  (termlisp-repl--teardown)
  (kill-buffer (current-buffer)))

(defun termlisp-repl-restart ()
  "Discard every definition and load a fresh environment.
The buffer, its history and the output above the prompt are kept, and
so are the environment's options."
  (interactive)
  (unless (derived-mode-p 'termlisp-repl-mode)
    (user-error "Not in a term-lisp REPL buffer"))
  (termlisp-repl--reset-env)
  (termlisp-repl--write "\nFresh environment loaded.\n")
  (termlisp-repl--write termlisp-repl-prompt))

(defun termlisp-repl-toggle-type-check ()
  "Toggle type checking of the current REPL environment.
The change takes effect immediately; it is kept by
`termlisp-repl-restart'."
  (interactive)
  (unless (derived-mode-p 'termlisp-repl-mode)
    (user-error "Not in a term-lisp REPL buffer"))
  (let* ((env termlisp-repl--env)
         (on (not (tl-env-option env :type-check))))
    (setq termlisp-repl--options
          (plist-put termlisp-repl--options :type-check on))
    (setf (tl-env-options env)
          (plist-put (tl-env-options env) :type-check on))
    (message "term-lisp :type-check %s" (if on "on" "off"))))

;;; Mode and entry point

(define-derived-mode termlisp-repl-mode comint-mode "term-lisp REPL"
  "Major mode for interactively evaluating term-lisp expressions.

The environment is created by `termlisp-repl', which loads the prelude,
every file in `termlisp-repl-load-files', and applies
`termlisp-repl-options'.  Definitions made at the prompt are
kept until `termlisp-repl-restart' rebuilds the environment.

\\{termlisp-repl-mode-map}"
  (setq-local comint-prompt-regexp (concat "^" (regexp-quote termlisp-repl-prompt)))
  (setq-local comint-prompt-read-only t)
  (setq-local comint-input-sender #'termlisp-repl--send)
  (setq-local paragraph-start comint-prompt-regexp)
  (setq-local paragraph-separate "\\'")
  (setq-local comment-start ";")
  (setq-local comment-use-syntax t)
  (setq-local indent-line-function #'lisp-indent-line)
  (setq-local font-lock-defaults '(termlisp-repl-font-lock-keywords))
  (add-hook 'kill-buffer-hook #'termlisp-repl--teardown nil t)
  (termlisp-repl--start))

(define-key termlisp-repl-mode-map (kbd "RET") #'termlisp-repl-return)
(define-key termlisp-repl-mode-map (kbd "C-j") #'termlisp-repl-newline)
(define-key termlisp-repl-mode-map (kbd "C-c C-t") #'termlisp-repl-toggle-type-check)
(define-key termlisp-repl-mode-map (kbd "C-c C-k") #'termlisp-repl-restart)

;;;###autoload
(defun termlisp-repl (&optional buffer-name)
  "Start a term-lisp REPL, or switch to the one that is already running.
Input is evaluated in the running Emacs, so definitions persist for the
rest of the session.  BUFFER-NAME defaults to `termlisp-repl-buffer-name'."
  (interactive)
  (let ((name (or buffer-name termlisp-repl-buffer-name)))
    (unless (comint-check-proc name)
      (with-current-buffer (get-buffer-create name)
        (termlisp-repl-mode)))
    (pop-to-buffer-same-window name)))

(provide 'termlisp-repl)
;;; termlisp-repl.el ends here
