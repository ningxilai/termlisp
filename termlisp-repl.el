;;; termlisp-repl.el --- Interactive REPL for term-lisp -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;; A comint-driven REPL for term-lisp, modelled on IELM.  Evaluation runs in
;; the running Emacs, so definitions made at the prompt stay in the session
;; and can be inspected from ordinary Emacs Lisp.
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
;; `termlisp-repl-load-prelude' is non-nil.

;;; Code:

(require 'comint)
(require 'termlisp-eval)
(require 'termlisp-load)

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

(defconst termlisp-repl-font-lock-keywords
  `(("\\_<\\(?:define\\|datatype-extension\\|datatype\\|class\\|instance\\|lambda\\|do\\)\\_>"
     . font-lock-keyword-face)
    ("\\(?:\\`\\|[() \t\n]\\)\\(:[[:alnum:]+*/_<>!?=.-]*\\)"
     (1 font-lock-builtin-face)))
  "Font-lock keywords used by `termlisp-repl-mode'.")

(defvar termlisp-repl-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\( "(" table)
    (modify-syntax-entry ?\) ")" table)
    (modify-syntax-entry ?\[ "(" table)
    (modify-syntax-entry ?\] ")" table)
    (modify-syntax-entry ?\{ "(" table)
    (modify-syntax-entry ?\} ")" table)
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
    (termlisp-load-prelude termlisp-repl--env)))

(defun termlisp-repl--banner ()
  "Return the text written when a REPL buffer is created."
  (concat
   (format "Welcome to term-lisp%s.\n"
           (if termlisp-repl-load-prelude " (prelude loaded)" " (empty environment)"))
   (format "Options: %S.  Type `exit' to quit, %s to continue a form on the next line.\n"
           termlisp-repl--options
           (substitute-command-keys "\\[termlisp-repl-newline]"))))

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

;;; Reading and evaluating

(defun termlisp-repl--complete-p (input)
  "Return non-nil when INPUT ends after a complete top-level form.
Whitespace and comments are skipped.  Hitting the end of file while
reading a form means more input is needed; any other read error does
not, and is reported when the input is evaluated."
  (with-temp-buffer
    (insert input)
    (goto-char (point-min))
    (when (boundp 'read-eval)
      (set (make-local-variable 'read-eval) nil))
    (let ((read-circle nil))
      (condition-case nil
          (progn
            (while (termlisp--skip-trivia)
              (read (current-buffer)))
            t)
        (end-of-file nil)
        (error t)))))

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

(defun termlisp-repl--eval-string (input)
  "Evaluate INPUT in the REPL environment and return its printed value.
A form with holes never reaches here: the checker signals `termlisp-hole'
with its goals before anything is run, and `termlisp-repl--send' shows
them.  Return nil when INPUT holds no top-level forms."
  (let* ((env termlisp-repl--env)
         (value nil)
         (forms (termlisp-parse input))
         ;; One REPL submission is one unit, so a line may declare a
         ;; name it uses earlier in that same line.
         (tl-infer-forward-names (termlisp-collect-forward-names forms)))
    (when forms
      (unwind-protect
          (prog1
              (progn
                (dolist (form forms value)
                  (setq value (termlisp-eval-form form env)))
                (termlisp-value->string value))
            ;; A submission is this driver's batch, so this is the first
            ;; moment every clause of a function typed in on this line is
            ;; present and a coverage check can mean anything.
            (tl-run-post-batch))
        ;; A submission that failed partway left a function holding only
        ;; some of its clauses.  Reporting it now would name a clause the
        ;; user has not typed yet, so the queue is dropped instead -- the
        ;; same half-written state `tl-run-post-batch' refuses to report.
        (setq tl-coverage-announcements nil)))))

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
            (let ((result (termlisp-repl--eval-string input)))
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
     ((or (null input) (termlisp-repl--complete-p input))
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

The environment is created by `termlisp-repl', which loads the prelude
and applies `termlisp-repl-options'.  Definitions made at the prompt are
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
