;;; aldor-test.el --- tests for the Aldor frontend and emitter -*- lexical-binding: t; -*-
;; This file is part of termlisp.
;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Code:

(require 'ert)
(require 'termlisp)

;; Generated programs redefine elisp builtins (`cons', `apply', `sort'
;; ...).  Letting `defalias' install byte-compiler trampolines then
;; re-enters code that already calls the shadowed name.  Skip
;; trampolines while evaluating generated forms; interpreted eval
;; needs none.
(when (fboundp 'comp-subr-trampoline-install)
  (advice-add 'comp-subr-trampoline-install :override #'ignore))

(defun tl-test--triple ()
  "An ABN triple for: f(n: Integer): Integer == if n < 0 then 1 else n"
  (list
   '(|Define|
     (|Declare| (|Id| (|syme| |ref| . 0)) (|Id| (|syme| |ref| . 1)))
     (|Lambda|
      (|Comma| (|Declare| (|Id| (|syme| |ref| . 2)) (|Id| (|syme| |ref| . 1))))
      (|Id| (|syme| |ref| . 1))
      (|If|
       (|Test| (|Apply| (|Id| (|syme| |ref| . 3))
                        (|Id| (|syme| |ref| . 2))
                        (|LitInteger| "0")))
       (|LitInteger| "1")
       (|Id| (|syme| |ref| . 2)))))
   (vector '((|name| . |f|) (|type| |ref| . 0))
           '((|name| . |Integer|))
           '((|name| . |n|) (|type| |ref| . 0))
           '((|name| . <)))
   (vector '(|Id| (|state| . "tposs") (|name| . |Integer|)))))

(ert-deftest tl-abn-resolve-splices-syme ()
  (let* ((abn (tl-abn-resolve (tl-test--triple)))
         (tree (tl-abn-tree abn))
         (decl (nth 1 tree))
         (id (nth 1 decl)))
    (should (eq (car tree) 'Define))
    (should (eq (tl-abn-id-name id) 'f))
    (should (= (length (tl-abn-symes abn)) 4))
    (should (eq (car (tl-abn-syme-type abn (tl-abn-id-syme id)))
                'Id))))

(ert-deftest tl-aldor-lower-define ()
  (let ((forms (tl-aldor-lower (tl-abn-resolve (tl-test--triple)))))
    (should (equal forms '((define (f n) (if (< n 0) 1 n)))))))

(ert-deftest tl-emit-eval-lowered ()
  (let ((el (tl-emit-program (tl-aldor-lower (tl-abn-resolve (tl-test--triple))))))
    (should (equal el '((defun f (n) (if (< n 0) 1 n)))))
    (eval (car el) t)
    (should (equal (funcall 'f 5) 5))
    (should (equal (funcall 'f -5) 1))))

(ert-deftest tl-emit-constructors ()
  (let ((el (tl-emit-program
             '((datatype Maybe (Nothing) (Just a))
               (define none Nothing)
               (define (wrap v) (Just v))
               (define two (Just 2))))))
    (should (equal el '((defconst none 'Nothing)
                        (defun wrap (v) (list 'Just v))
                        (defconst two (list 'Just 2)))))))

(ert-deftest tl-emit-boolean-and-ops ()
  (let ((el (tl-emit-program
             '((define (testop x) (if (<= x 0) True False))
               (define (loopy x) (and (not (= x 1)) (or (< x 5) True)))))))
    (should (equal el '((defun testop (x) (if (<= x 0) t nil))
                        (defun loopy (x)
                          (and (not (= x 1)) (or (< x 5) t))))))))

(ert-deftest tl-emit-recursion ()
  (let ((el (tl-emit-program
             '((define (tlfib n) (if (< n 2) n (+ (tlfib (- n 1)) (tlfib (- n 2)))))))))
    (eval (car el) t)
    (should (equal (funcall 'tlfib 10) 55))))

(ert-deftest tl-aldor-e2e-fib ()
  (skip-unless (tl-aldor-available-p))
  (let* ((dir (make-temp-file "tl-aldor-e2e" t))
         (as-file (expand-file-name "fib.as" dir))
         (el-file (expand-file-name "fib.el" dir)))
    (unwind-protect
        (progn
          (with-temp-file as-file
            (insert "#include \"fricas\"\n"
                    "import from Integer, Boolean;\n"
                    "\n"
                    "fib(n: Integer): Integer ==\n"
                    "    if n < 2 then n else fib(n - 1) + fib(n - 2);\n"
                    "\n"
                    "sumTo(n: Integer): Integer ==\n"
                    "    if n <= 0 then 0 else n + sumTo(n - 1);\n"))
          (let ((source (tl-aldor-compile-file as-file :output el-file)))
            (should (file-exists-p el-file))
            (should (string-match-p "(defun fib " source))
            (should (string-match-p "(defun sumTo " source))
            (with-temp-buffer
              (insert-file-contents el-file)
              (condition-case nil
                  (while t (eval (read (current-buffer)) t))
                (end-of-file nil)))
            (should (equal (funcall 'fib 10) 55))
            (should (equal (funcall 'fib 15) 610))
            (should (equal (funcall 'sumTo 100) 5050))))
      (delete-directory dir t))))

(ert-deftest tl-aldor-e2e-tail ()
  "Self tail calls from real .as compile to loops with constant stack."
  (skip-unless (tl-aldor-available-p))
  (let* ((dir (make-temp-file "tl-aldor-tail" t))
         (as-file (expand-file-name "tail.as" dir))
         (el-file (expand-file-name "tail.el" dir)))
    (unwind-protect
        (progn
          (with-temp-file as-file
            (insert "#include \"fricas\"\n"
                    "import from Integer, Boolean;\n"
                    "\n"
                    "tailSum(n: Integer, acc: Integer): Integer ==\n"
                    "    if n <= 0 then acc else tailSum(n - 1, acc + n);\n"))
          (let ((source (tl-aldor-compile-file as-file :output el-file)))
            (should (string-match-p "(defun tailSum " source))
            (should (string-match-p "tl-tco-args" source))
            (with-temp-buffer
              (insert-file-contents el-file)
              (condition-case nil
                  (while t (eval (read (current-buffer)) t))
                (end-of-file nil))))
          (should (equal (funcall 'tailSum 100 0) 5050))
          (should (equal (funcall 'tailSum 100000 0) 5000050000)))
      (delete-directory dir t))))

(ert-deftest tl-aldor-e2e-byte-compile ()
  (skip-unless (tl-aldor-available-p))
  (let* ((dir (make-temp-file "tl-aldor-elc" t))
         (as-file (expand-file-name "cnt.as" dir))
         (el-file (expand-file-name "cnt.el" dir)))
    (unwind-protect
        (progn
          (with-temp-file as-file
            (insert "#include \"fricas\"\n"
                    "import from Integer, Boolean;\n"
                    "countdown(n: Integer): Integer ==\n"
                    "    if n <= 0 then 0 else countdown(n - 1);\n"))
          (tl-aldor-compile-file as-file :output el-file :byte-compile t)
          (should (file-exists-p (concat el-file "c")))
          (load (concat el-file "c") nil t)
          (should (equal (funcall 'countdown 50) 0)))
      (delete-directory dir t))))

(ert-deftest tl-aldor-lower-error-on-sequence ()
  (let* ((triple (list '(|Define|
                          (|Declare| (|Id| (|syme| |ref| . 0))
                                     (|Id| (|syme| |ref| . 1)))
                          (|Lambda|
                           (|Comma|)
                           (|Id| (|syme| |ref| . 1))
                           (|Sequence|
                            (|LitInteger| "1")
                            (|LitInteger| "2"))))
                       (vector '((|name| . |f|) (|type| |ref| . 0))
                               '((|name| . |Integer|)))
                       (vector '(|Id| (|state| . "tposs") (|name| . |Integer|))))))
    (should-error (tl-aldor-lower (tl-abn-resolve triple))
                  :type 'termlisp-aldor-error)))

;;; Reader

(ert-deftest tl-abn-escape-pipes ()
  (let ((form (read (tl-abn--escape-pipes "(|name| . |#1|)"))))
    (should (eq (car form) 'name))
    (should (symbolp (cdr form)))
    (should (equal (symbol-name (cdr form)) "#1")))
  (should (equal (read (tl-abn--escape-pipes "(|syme| |ref| . 3)"))
                 '(syme ref . 3)))
  ;; Bars inside string literals are not escapes.
  (should (equal (read (tl-abn--escape-pipes "(\"a|b\" |x|)"))
                 (list "a|b" 'x)))
  ;; Raw ? starts an Elisp character literal that eats the closing paren.
  (should (equal (read (tl-abn--escape-pipes "(|Declare| () (|Blank| ?))"))
                 (list 'Declare nil (list 'Blank (intern "?")))))
  ;; Aldor digit-name escapes (\1 = name 1) read via Elisp's backslash.
  (let ((form (read (tl-abn--escape-pipes "(|name| . \\1)"))))
    (should (equal (symbol-name (cdr form)) "1"))))

;;; Sequence lowering: early exits, locals by substitution

(defun tl-test--block-triple ()
  "An ABN triple for a classify function with two early exits."
  (list
   '(|Define|
     (|Declare| (|Id| (|syme| |ref| . 0)) (|Id| (|syme| |ref| . 1)))
     (|Lambda|
      (|Comma| (|Declare| (|Id| (|syme| |ref| . 2)) (|Id| (|syme| |ref| . 1))))
      (|Id| (|syme| |ref| . 1))
      (|Sequence|
       (|Exit|
        (|Test| (|Apply| (|Id| (|syme| |ref| . 3))
                         (|Id| (|syme| |ref| . 2))
                         (|LitInteger| "10")))
        (|LitInteger| "2"))
       (|Exit|
        (|Test| (|Apply| (|Id| (|syme| |ref| . 4))
                         (|Id| (|syme| |ref| . 2))
                         (|LitInteger| "0")))
        (|Apply| (|Id| (|syme| |ref| . 5)) (|LitInteger| "1")))
       (|LitInteger| "0"))))
   (vector '((|name| . |g|) (|type| |ref| . 0))
           '((|name| . |Integer|))
           '((|name| . |n|) (|type| |ref| . 0))
           '((|name| . >))
           '((|name| . <))
           '((|name| . -)))
   (vector '(|Id| (|state| . "tposs") (|name| . |Integer|)))))

(ert-deftest tl-aldor-lower-exit-chain ()
  (let ((forms (tl-aldor-lower (tl-abn-resolve (tl-test--block-triple)))))
    (should (equal forms
                   '((define (g n)
                       (if (> n 10) 2 (if (< n 0) (- 1) 0))))))))

(ert-deftest tl-aldor-lower-local-substitution ()
  "local s := 0; s := s + n; s  lowers to  (+ 0 n)."
  (let* ((triple
          (list
           '(|Define|
             (|Declare| (|Id| (|syme| |ref| . 0)) (|Id| (|syme| |ref| . 1)))
             (|Lambda|
              (|Comma|
               (|Declare| (|Id| (|syme| |ref| . 2)) (|Id| (|syme| |ref| . 1))))
              (|Id| (|syme| |ref| . 1))
              (|Sequence|
               (|Local|
                (|Assign|
                 (|Declare| (|Id| (|syme| |ref| . 3))
                            (|Id| (|syme| |ref| . 1)))
                 (|LitInteger| "0")))
               (|Assign|
                (|Id| (|syme| |ref| . 3))
                (|Apply| (|Id| (|syme| |ref| . 4))
                         (|Id| (|syme| |ref| . 3))
                         (|Id| (|syme| |ref| . 2))))
               (|Id| (|syme| |ref| . 3)))))
           (vector '((|name| . |g|) (|type| |ref| . 0))
                   '((|name| . |Integer|))
                   '((|name| . |n|) (|type| |ref| . 0))
                   '((|name| . |s|))
                   '((|name| . +)))
           (vector '(|Id| (|state| . "tposs") (|name| . |Integer|))))))
    (should (equal (tl-aldor-lower (tl-abn-resolve triple))
                   '((define (g n) (+ 0 n)))))))

(ert-deftest tl-aldor-lower-assign-to-parameter ()
  "A parameter is an assignable local: `n := 1; n' writes the argument."
  (let* ((triple
          (list
           '(|Define|
             (|Declare| (|Id| (|syme| |ref| . 0)) (|Id| (|syme| |ref| . 1)))
             (|Lambda|
              (|Comma|
               (|Declare| (|Id| (|syme| |ref| . 2)) (|Id| (|syme| |ref| . 1))))
              (|Id| (|syme| |ref| . 1))
              (|Sequence|
               (|Assign|
                (|Id| (|syme| |ref| . 2))
                (|LitInteger| "1"))
               (|Id| (|syme| |ref| . 2)))))
           (vector '((|name| . |g|) (|type| |ref| . 0))
                   '((|name| . |Integer|))
                   '((|name| . |n|) (|type| |ref| . 0)))
           (vector '(|Id| (|state| . "tposs") (|name| . |Integer|))))))
    (let ((forms (tl-aldor-lower (tl-abn-resolve triple))))
      (should (equal forms '((define (g n) (Seq (Setq n 1) n)))))
      (let ((el (tl-emit-program forms)))
        (should (equal el '((defun g (n) (progn (setq n 1) n)))))
        (eval (car el) t)
        (should (= (funcall 'g 5) 1))))))

(ert-deftest tl-aldor-lower-bracket ()
  "[1, 2] lowers to (Cons 1 (Cons 2 Nil))."
  (let* ((triple
          (list
           '(|Define|
             (|Declare| (|Id| (|syme| |ref| . 0)) (|Id| (|syme| |ref| . 1)))
             (|Lambda|
              (|Comma|)
              (|Id| (|syme| |ref| . 1))
              (|Apply| (|Id| (|syme| |ref| . 2))
                       (|LitInteger| "1")
                       (|LitInteger| "2"))))
           (vector '((|name| . |g|) (|type| |ref| . 0))
                   '((|name| . |Integer|))
                   '((|name| . bracket)))
           (vector '(|Id| (|state| . "tposs") (|name| . |Integer|))))))
    (should (equal (tl-aldor-lower (tl-abn-resolve triple))
                   '((define (g) (Cons 1 (Cons 2 Nil))))))))

;;; Emitter: list operations, applied parameters, default constructors

(ert-deftest tl-emit-list-ops ()
  (should (equal (tl-emit-program
                  '((define (hd l) (first l))
                    (define (tlf l) (rest l))
                    (define (emp l) (empty? l))))
                 '((defun hd (l) (cadr l))
                   (defun tlf (l) (caddr l))
                   (defun emp (l) (eq l 'Nil))))))

(ert-deftest tl-emit-internal-list-ops ()
  "ListFirst/ListRest/ListEmpty are the internal Cons-list walks:
always inlined, whatever the program defines."
  (should (equal (tl-emit-program
                  '((define (first l) (my-first l))
                    (define (revwalk l)
                      (Seq (Setq l (ListRest l))
                           (Setq l (ListFirst l))
                           (ListEmpty l)))))
                 '((defun first (l) (my-first l))
                   (defun revwalk (l)
                     (progn (setq l (caddr l))
                            (setq l (cadr l))
                            (eq l 'Nil)))))))

(ert-deftest tl-emit-user-list-ops-win ()
  "A program that defines first/rest/empty? itself keeps its own
definitions at call sites; the emitter's inlining stays off."
  (should (equal (tl-emit-program
                  '((define (first l) (my-first l))
                    (define (rest l) (my-rest l))
                    (define (empty? l) (my-empty l))
                    (define (use l)
                      (Seq (first l) (rest l) (empty? l)))))
                 '((defun first (l) (my-first l))
                   (defun rest (l) (my-rest l))
                   (defun empty? (l) (my-empty l))
                   (defun use (l)
                     (progn (first l) (rest l) (empty? l)))))))

(ert-deftest tl-emit-type-guard-dispatch ()
  "Two same-arity clauses dispatch on the lowering's %guard tests.
The %p<i> placeholders become bound to the actual arguments."
  (let* ((el (tl-emit-program
              '((define (pick t) (%guard (vectorp %p0) 'tuple-hit))
                (define (pick g)
                  (%guard (or (eq %p0 'Nil) (consp %p0)) 'gen-hit)))))
         (fn (car el)))
    (should (eq (car fn) 'defun))
    (should (string-match-p "vectorp %p0" (format "%S" fn)))
    (eval fn t)
    (should (equal (funcall 'pick (vector 1 2)) 'tuple-hit))
    (should (equal (funcall 'pick (list 'Cons 1 'Nil)) 'gen-hit))
    (should-error (funcall 'pick 7))))

(ert-deftest tl-emit-applied-parameter ()
  (let ((el (tl-emit-program '((define (twice f x) (f (f x)))))))
    (should (equal el '((defun twice (f x) (funcall f (funcall f x))))))
    (eval (car el) t)
    (should (equal (funcall 'twice (lambda (x) (+ x 1)) 5) 7))))

(ert-deftest tl-emit-default-constructors ()
  (should (equal (tl-emit-program
                  '((define none Nil)
                    (define (cons2 a b) (Cons a b))))
                 '((defconst none 'Nil)
                   (defun cons2 (a b) (list 'Cons a b))))))

;;; End to end: blocks with early exits and locals

(defun tl-test--compile-load (name source)
  "Compile Aldor SOURCE named NAME in a temp dir; load the result.
Return the generated source string."
  (let* ((dir (make-temp-file (format "tl-%s" name) t))
         (as-file (expand-file-name (concat name ".as") dir))
         (el-file (expand-file-name (concat name ".el") dir)))
    (unwind-protect
        (progn
          (with-temp-file as-file (insert source))
          (let ((generated (tl-aldor-compile-file as-file :output el-file)))
            (with-temp-buffer
              (insert-file-contents el-file)
              (condition-case nil
                  (while t (eval (read (current-buffer)) t))
                (end-of-file nil)))
            generated))
      (delete-directory dir t))))

(ert-deftest tl-aldor-e2e-block ()
  (skip-unless (tl-aldor-available-p))
  (let ((source
         (tl-test--compile-load
          "blk"
          (concat "#include \"fricas\"\n"
                  "import from Integer, Boolean;\n"
                  "\n"
                  "classify(n: Integer): Integer == {\n"
                  "  n > 10 => 2;\n"
                  "  n < 0 => -1;\n"
                  "  0\n"
                  "};\n"
                  "\n"
                  "acc(n: Integer): Integer == {\n"
                  "  local s: Integer := 0;\n"
                  "  s := s + n;\n"
                  "  s := s + n;\n"
                  "  s\n"
                  "};\n"))))
    (should (string-match-p "(defun classify " source))
    (should (equal (funcall 'classify 12) 2))
    (should (equal (funcall 'classify -3) -1))
    (should (equal (funcall 'classify 7) 0))
    (should (equal (funcall 'acc 5) 10))))

(ert-deftest tl-aldor-e2e-list ()
  (skip-unless (tl-aldor-available-p))
  (let ((source
         (tl-test--compile-load
          "lst"
          (concat "#include \"fricas\"\n"
                  "import from Integer, Boolean, List Integer;\n"
                  "\n"
                  "sumList(l: List Integer): Integer ==\n"
                  "  if empty? l then 0 else first l + sumList(rest l);\n"
                  "\n"
                  "mk(): List Integer == cons(1, cons(2, nil));\n"
                  "lit(): List Integer == [1, 2];\n"
                  "app(): Integer == twice((x: Integer): Integer +-> x + 1, 5);\n"
                  "twice(f: (Integer -> Integer), x: Integer): Integer == f(f x);\n"))))
    (should (string-match-p "(defun sumList " source))
    (should (equal (funcall 'sumList (funcall 'mk)) 3))
    (should (equal (funcall 'lit) (list 'Cons 1 (list 'Cons 2 'Nil))))
    (should (equal (funcall 'app) 7))))

;;; Records and unions

(ert-deftest tl-emit-record-union ()
  (let ((el (tl-emit-program
             '((define (mk a b) (Record a b))
               (define (fst r) (Field r 0))
               (define (setfst r v) (FieldSet r 0 v))
               (define (uin v) (Union 0 v))
               (define (ucase u) (UnionCase u 1))))))
    (should (equal el '((defun mk (a b) (vector a b))
                        (defun fst (r) (aref r 0))
                        (defun setfst (r v)
                          (let ((rec r))
                            (aset rec 0 v)
                            rec))
                        (defun uin (v) (vector 0 v))
                        (defun ucase (u) (eq (aref u 0) 1)))))))

(ert-deftest tl-aldor-e2e-record ()
  (skip-unless (tl-aldor-available-p))
  (let ((source
         (tl-test--compile-load
          "rec"
          (concat "#include \"fricas\"\n"
                  "import from Integer, Boolean;\n"
                  "\n"
                  "testA(): Integer == {\n"
                  "  local r: Record(a: Integer, b: Boolean) := [7, true];\n"
                  "  r.a\n"
                  "};\n"
                  "\n"
                  "testB(): Boolean == {\n"
                  "  local r: Record(a: Integer, b: Boolean) := [7, true];\n"
                  "  r.b\n"
                  "};\n"
                  "\n"
                  "testC(): Integer == {\n"
                  "  local r: Record(a: Integer, b: Boolean) := [7, true];\n"
                  "  r.a := 9;\n"
                  "  r.a\n"
                  "};\n"))))
    (should (string-match-p "(defun testA " source))
    (should (equal (funcall 'testA) 7))
    (should (equal (funcall 'testB) t))
    (should (equal (funcall 'testC) 9))))

(ert-deftest tl-aldor-e2e-union ()
  (skip-unless (tl-aldor-available-p))
  (let ((source
         (tl-test--compile-load
          "uni"
          (concat "#include \"fricas\"\n"
                  "import from Integer, Boolean;\n"
                  "\n"
                  "testD(): Boolean == {\n"
                  "  local u: Union(i: Integer, b: Boolean) := [3];\n"
                  "  u case i\n"
                  "};\n"
                  "\n"
                  "testE(): Integer == {\n"
                  "  local u: Union(i: Integer, b: Boolean) := [3];\n"
                  "  u.i\n"
                  "};\n"
                  "\n"
                  "testF(): Boolean == {\n"
                  "  local u: Union(i: Integer, b: Boolean) := [true];\n"
                  "  u case b\n"
                  "};\n"))))
    (should (string-match-p "(defun testD " source))
    (should (eq (funcall 'testD) t))
    (should (equal (funcall 'testE) 3))
    (should (eq (funcall 'testF) t))))

(ert-deftest tl-aldor-e2e-union-branch ()
  "union v picks the branch from the payload's static type, even
when the payload is an untyped literal."
  (skip-unless (tl-aldor-available-p))
  (let ((source
         (tl-test--compile-load
          "unb"
          (concat "#include \"fricas\"\n"
                  "import from Integer, Boolean;\n"
                  "\n"
                  "uA(): Boolean == {\n"
                  "  local u: Union(i: Integer, b: Boolean) := union 3;\n"
                  "  u case i\n"
                  "};\n"
                  "\n"
                  "uB(): Integer == {\n"
                  "  local u: Union(i: Integer, b: Boolean) := union 3;\n"
                  "  u.i\n"
                  "};\n"))))
    (should (string-match-p "(defun uA " source))
    (should (eq (funcall 'uA) t))
    (should (equal (funcall 'uB) 3))))

(ert-deftest tl-aldor-e2e-generate ()
  "generate/yield, for-in over a Generator, tuple assignment, bare
local declarations, and a program-defined `cons' shadowing the
builtin operator mapping."
  (skip-unless (tl-aldor-available-p))
  (let ((cons-cell (and (fboundp 'cons) (symbol-function 'cons)))
        (gen-src nil)
        (main-val nil))
    (unwind-protect
        (progn
          (setq gen-src
                (tl-test--compile-load
                 "genT"
                 (concat "#include \"fricas\"\n"
                         "import from Integer, Boolean;\n"
                         "\n"
                         "genSum(): Integer == {\n"
                         "  s: Integer := 0;\n"
                         "  g: Generator Integer := generate { yield 1; yield 2; yield 3 };\n"
                         "  for x in g repeat s := s + x;\n"
                         "  s\n"
                         "};\n"
                         "\n"
                         "tup(): Integer == {\n"
                         "  local a: Integer := 0;\n"
                         "  local b: Integer := 0;\n"
                         "  (a, b) := (10, 32);\n"
                         "  a + b\n"
                         "};\n"
                         "\n"
                         "cons(a: Integer, b: Integer): Integer == a * 100 + b;\n"
                         "shadow(): Integer == cons(3, 4);\n"
                         "\n"
                         "main(): Integer == genSum() + tup() + shadow();\n")))
          ;; The program defines `cons', shadowing the elisp builtin;
          ;; main needs it, but the rest of the session needs the real
          ;; one back afterwards.
          (setq main-val (funcall 'main)))
      (if cons-cell (fset 'cons cons-cell) (fmakunbound 'cons)))
    (should (string-match-p "(defun genSum " gen-src))
    (should (string-match-p "(defun cons " gen-src))
    ;; A Generator is a resumable closure pulled one element at a time.
    (should (string-match-p "funcall %gen" gen-src))
    (should (string-match-p "tl-gen-yield" gen-src))
    ;; 1+2+3 from the generator, 10+32 from the tuple assignment,
    ;; 3*100+4 from the program's own cons.
    (should (equal main-val 352))))

;;; Loops

(ert-deftest tl-emit-loop-forms ()
  (let ((el (tl-emit-program
             '((define (sumto n)
                 (Let ((i 1) (acc 0))
                   (While (<= i n)
                     (Setq acc (+ acc i))
                     (Setq i (+ i 1)))
                   acc))
               (define (stop x)
                 (Catch tl-loop-break
                   (While True
                     (Seq (if x (Break) nil) 1))))
               (define (adv x)
                 (Catch tl-loop-next
                   (While True
                     (Seq (if x (Iterate) nil) (Setq x nil)))))))))
    (should (equal el '((defun sumto (n)
                          (let* ((i 1) (acc 0))
                            (while (<= i n)
                              (setq acc (+ acc i))
                              (setq i (+ i 1)))
                            acc))
                        (defun stop (x)
                          (catch 'tl-loop-break
                            (while t
                              (progn (if x (throw 'tl-loop-break nil) nil)
                                     1))))
                        (defun adv (x)
                          (catch 'tl-loop-next
                            (while t
                              (progn (if x (throw 'tl-loop-next nil) nil)
                                     (setq x nil))))))))
    (eval (nth 0 el) t)
    (eval (nth 1 el) t)
    (eval (nth 2 el) t)
    (should (equal (funcall 'sumto 5) 15))
    (should (equal (funcall 'sumto 10) 55))
    (should (null (funcall 'stop t)))
    (should (null (funcall 'adv t)))))

(ert-deftest tl-emit-tail-call ()
  (let ((el (tl-emit-program
             '((define (tcosum n acc)
                 (if (< n 1) acc (tcosum (- n 1) (+ acc n))))
               (define (tcofib n)
                 (if (< n 2) n (+ (tcofib (- n 1)) (tcofib (- n 2)))))))))
    (should (equal (nth 3 (nth 0 el))
                   '(let ((tl-tco-args (vector n acc)) (tl-tco-ret nil))
                      (while tl-tco-args
                        (setq tl-tco-ret
                              (let ((n (aref tl-tco-args 0))
                                    (acc (aref tl-tco-args 1)))
                                (setq tl-tco-args nil)
                                (if (< n 1)
                                    acc
                                  (setq tl-tco-args
                                        (vector (- n 1) (+ acc n)))))))
                      tl-tco-ret)))
    ;; No tail self call: emitted unchanged.
    (should (equal (nth 3 (nth 1 el))
                   '(if (< n 2) n (+ (tcofib (- n 1)) (tcofib (- n 2))))))
    (eval (nth 0 el) t)
    (eval (nth 1 el) t)
    (should (equal (funcall 'tcosum 10 0) 55))
    (should (equal (funcall 'tcofib 10) 55))
    ;; Constant stack: 100000 tail iterations succeed.
    (should (equal (funcall 'tcosum 100000 0) 5000050000))))

(ert-deftest tl-aldor-lower-break-outside-loop-error ()
  (let* ((triple (list '(|Define|
                          (|Declare| (|Id| (|syme| |ref| . 0))
                                     (|Id| (|syme| |ref| . 1)))
                          (|Lambda|
                           (|Comma|)
                           (|Id| (|syme| |ref| . 1))
                           (|Sequence|
                            (|Break| nil)
                            (|LitInteger| "1"))))
                       (vector '((|name| . |f|) (|type| |ref| . 0))
                               '((|name| . |Integer|)))
                       (vector '(|Id| (|state| . "tposs") (|name| . |Integer|))))))
    (should-error (tl-aldor-lower (tl-abn-resolve triple))
                  :type 'termlisp-aldor-error)))

(ert-deftest tl-aldor-e2e-loop ()
  "Segment and list iterators, while, repeat, break, mutation."
  (skip-unless (tl-aldor-available-p))
  (let* ((dir (make-temp-file "tl-aldor-loop" t))
         (as-file (expand-file-name "loop.as" dir))
         (el-file (expand-file-name "loop.el" dir)))
    (unwind-protect
        (progn
          (with-temp-file as-file
            (insert "#include \"fricas\"\n"
                    "import from Integer, Boolean, List Integer;\n"
                    "\n"
                    "sumSeg(n: Integer): Integer == {\n"
                    "  local s: Integer := 0;\n"
                    "  for i in 1..n repeat s := s + i;\n"
                    "  s\n"
                    "};\n"
                    "\n"
                    "sumDown(n: Integer): Integer == {\n"
                    "  local s: Integer := 0;\n"
                    "  for i in n..1 by -1 repeat s := s + i;\n"
                    "  s\n"
                    "};\n"
                    "\n"
                    "sumL(l: List Integer): Integer == {\n"
                    "  local s: Integer := 0;\n"
                    "  for x in l repeat s := s + x;\n"
                    "  s\n"
                    "};\n"
                    "\n"
                    "cd(n: Integer): Integer == {\n"
                    "  local k: Integer := n;\n"
                    "  local c: Integer := 0;\n"
                    "  while k > 0 repeat {\n"
                    "    c := c + k;\n"
                    "    k := k - 1;\n"
                    "  };\n"
                    "  c\n"
                    "};\n"
                    "\n"
                    "brk(n: Integer): Integer == {\n"
                    "  local k: Integer := 0;\n"
                    "  local c: Integer := 0;\n"
                    "  repeat {\n"
                    "    k := k + 1;\n"
                    "    if k > n then break;\n"
                    "    c := c + k;\n"
                    "  };\n"
                    "  c\n"
                    "};\n"))
          (tl-aldor-compile-file as-file :output el-file :byte-compile t)
          (should (file-exists-p (concat el-file "c")))
          (load (concat el-file "c") nil t)
          (should (equal (funcall 'sumSeg 10) 55))
          (should (equal (funcall 'sumSeg 0) 0))
          (should (equal (funcall 'sumDown 5) 15))
          (should (equal (funcall 'sumL '(Cons 1 (Cons 2 (Cons 3 Nil)))) 6))
          (should (equal (funcall 'cd 5) 15))
          (should (equal (funcall 'brk 10) 55))
          (should (equal (funcall 'brk 0) 0)))
      (delete-directory dir t))))

(ert-deftest tl-aldor-e2e-iterate ()
  "Break/iterate with catch tags, and `|' generator filters."
  (skip-unless (tl-aldor-available-p))
  (let ((source
         (tl-test--compile-load
          "it"
          (concat "#include \"fricas\"\n"
                  "import from Integer, Boolean;\n"
                  "\n"
                  "it(n: Integer): Integer == {\n"
                  "  local k: Integer := 0;\n"
                  "  local c: Integer := 0;\n"
                  "  repeat {\n"
                  "    k := k + 1;\n"
                  "    if k > n then break;\n"
                  "    if even? k then iterate;\n"
                  "    c := c + k;\n"
                  "  };\n"
                  "  c\n"
                  "};\n"
                  "\n"
                  "filt(n: Integer): Integer == {\n"
                  "  local s: Integer := 0;\n"
                  "  for i in 1..n | even? i repeat s := s + i;\n"
                  "  s\n"
                  "};\n"
                  "\n"
                  "filtLe(n: Integer): Integer == {\n"
                  "  local s: Integer := 0;\n"
                  "  for i in 1..n | i <= 3 repeat s := s + i;\n"
                  "  s\n"
                  "};\n"))))
    (should (string-match-p "(defun it " source))
    (should (equal (funcall 'it 5) 9))
    (should (equal (funcall 'it 1) 1))
    (should (equal (funcall 'filt 10) 30))
    (should (equal (funcall 'filtLe 10) 6))))

;;; Typing the lowering IR

(ert-deftest tl-ir-typecheck-defines ()
  "The HM inferencer types emitted IR forms (not just termlisp source)."
  (let* ((env (tl-typecheck-ir
               '((define (f x) (+ x 1))
                 (define (g n)
                   (Let ((i 1) (acc 0))
                     (While (<= i n)
                       (Setq acc (+ acc i))
                       (Setq i (+ i 1)))
                     acc)))))
         (sc (gethash 'f (tl-env-type-env env))))
    (should (equal (tl-tscheme-type sc) (tl-tarrow (tl-tint) (tl-tint))))
    (should (equal (tl-tscheme-type (gethash 'g (tl-env-type-env env)))
                   (tl-tarrow (tl-tint) (tl-tint))))))

(ert-deftest tl-ir-typecheck-data-forms ()
  "Records, arrays and lists in the IR get structural types."
  (cl-flet ((result (ty)
              (while (and (tl-tcon-p ty) (eq (tl-tcon-name ty) '->))
                (setq ty (nth 1 (tl-tcon-args ty))))
              ty))
    (let ((env (tl-typecheck-ir
                '((define (mk a b) (Record a b))
                  (define (init n) (NewArray n 0))
                  (define (hd l) (ListFirst l))))))
      (should (eq (tl-tcon-name
                   (result (tl-tscheme-type (gethash 'mk (tl-env-type-env env)))))
                  'Record))
      (should (eq (tl-tcon-name
                   (result (tl-tscheme-type
                            (gethash 'init (tl-env-type-env env)))))
                  'Array))
      (should (eq (tl-tcon-name
                   (tl-tscheme-type (gethash 'hd (tl-env-type-env env))))
                  '->)))))

(ert-deftest tl-ir-handle-types ()
  "The oracle classifies handle/reference types apart from values."
  (should (tl-ir-handle-type-p (tl-tcon 'File nil)))
  (should (tl-ir-handle-type-p (tl-tcon 'TextReader nil)))
  (should (tl-ir-handle-type-p (tl-tcon 'Array (list (tl-tint)))))
  (should (tl-ir-handle-type-p (tl-tcon 'SomeDomain nil)))
  (should-not (tl-ir-handle-type-p (tl-tint)))
  (should-not (tl-ir-handle-type-p (tl-tcon 'List (list (tl-tint)))))
  (should-not (tl-ir-handle-type-p (tl-tstring))))

(ert-deftest tl-io-store-handles ()
  "Files are store handles; operations resolve them by id."
  (let* ((path (make-temp-file "termlisp-io-"))
         (id (tl-open path 'fileWrite)))
    (should (integerp id))
    (tl-write! ?a id)
    (tl-write! ?b id)
    (tl-close! id)
    (let ((rid (tl-open path 'fileRead)))
      (should (equal (tl-read! rid) ?a))
      (should (equal (tl-read! rid) ?b))
      (should (equal (tl-read! rid) tl-eof)))
    (delete-file path)))

;;; Graph unification

(ert-deftest tl-graph-unify-basic ()
  "Unifying two List applications links their element variables."
  (let* ((a (tl-make-var-node 'a))
         (b (tl-make-var-node 'b))
         (l1 (tl-make-node 'List (list a) t))
         (l2 (tl-make-node 'List (list b) t)))
    (should (tl-gnode-unify l1 l2))
    (should (eq (tl-gnode-deref a) (tl-gnode-deref b)))))

(ert-deftest tl-graph-unify-mismatch-rolls-back ()
  "A structural mismatch fails and leaves no bindings behind."
  (let* ((a (tl-make-var-node 'a))
         (b (tl-make-var-node 'b))
         (f (tl-make-node 'F (list a) t))
         (g (tl-make-node 'G (list b) t)))
    (should-not (tl-gnode-unify f g))
    (should (null (tl-node-bind a)))
    (should (null (tl-node-bind b)))))

(ert-deftest tl-graph-unify-occurs ()
  "The occurs check is optional; the default is equirecursive."
  (let* ((a (tl-make-var-node 'a))
         (l (tl-make-node 'List (list a) t)))
    (should-not (tl-gnode-unify a l t))
    (should (null (tl-node-bind a)))
    (should (tl-gnode-unify a l))))       ; cyclic/recursive allowed

(ert-deftest tl-graph-unify-shares ()
  "Unioning variables shares the whole structural class."
  (let* ((a (tl-make-var-node 'a))
         (b (tl-make-var-node 'b))
         (c (tl-make-var-node 'c)))
    (should (tl-gnode-unify a b))
    (should (tl-gnode-unify b c))
    (should (eq (tl-gnode-deref a) (tl-gnode-deref c)))))

(ert-deftest tl-unify-types-infinite ()
  "With the occurs check on, a cyclic unify reports an infinite type."
  (let* ((a (tl-fresh-tvar))
         (l (tl-tcon 'List (list a)))
         (tl-occurrence-check t))
    (should-error (tl-unify-types a l nil) :type 'termlisp-type-error)
    ;; The default remains equirecursive (no signal, cycle allowed).
    (let ((tl-occurrence-check nil))
      (should (car (tl-unify-types a l nil)))))
  ;; `tl-type-to-datum' renders a cycle with a finite back-reference.
  (let* ((a (tl-fresh-tvar))
         (l (tl-tcon 'List (list a))))
    (tl-unify-types a l nil)
    (should (string-match-p "!" (format "%S" (tl-type-to-datum l))))))

(ert-deftest tl-graph-decompose-crosscheck ()
  "The generic unifier traverses graph nodes via tl-decompose."
  (let* ((a (tl-make-var-node 'a))
         (b (tl-make-var-node 'b))
         (l1 (tl-make-node 'List (list a) t))
         (l2 (tl-make-node 'List (list b) t)))
    (should (car (tl-unify-generic l1 l2 nil #'tl-node-var-p nil)))
    (should-not (car (tl-unify-generic
                      l1 (tl-make-node 'Vector (list b) t)
                      nil #'tl-node-var-p nil)))))

;;; Graph-backed HM types

(ert-deftest tl-gtype-basics ()
  "Surface types convert to nodes and unify in place."
  (let* ((a (tl-fresh-tvar))
         (na (tl-gtype-from-tcon (tl-tcon 'List (list a))))
         (nn (tl-gtype-from-tcon (tl-tcon 'List (list (tl-tint))))))
    (should (tl-gtype-unify na nn))
    (should (equal (tl-gtype-to-tcon na)
                   (tl-tcon 'List (list (tl-tint)))))))

(ert-deftest tl-gtype-mismatch-rolls-back ()
  "A mismatched constructor fails and unbinds."
  (let* ((a (tl-fresh-tvar))
         (na (tl-gtype-from-tcon (tl-tcon 'List (list a))))
         (nn (tl-gtype-from-tcon (tl-tcon 'Vector (list (tl-tint))))))
    (should-not (tl-gtype-unify na nn))
    (should (tl-node-var-p (tl-gnode-deref (car (tl-node-children na)))))))

(ert-deftest tl-gtype-recursive-unify ()
  "The occurs check is off by default: equirecursive types are allowed."
  (let* ((a (tl-fresh-tvar))
         (na (tl-gtype-from-tcon a))
         (nl (tl-gtype-from-tcon (tl-tcon 'List (list a)))))
    (should (tl-gtype-unify na nl))
    (should (eq (tl-gnode-deref na) (tl-gnode-deref nl)))))

(ert-deftest tl-gtype-instantiate-fresh ()
  "Instantiating a scheme yields fresh variables each time."
  (let* ((a (tl-fresh-tvar))
         (na (tl-gtype-from-tcon (tl-tcon 'List (list a))))
         (q (tl-gtype-quantify na)))
    (let ((i1 (tl-gtype-instantiate (car q) (cdr q)))
          (i2 (tl-gtype-instantiate (car q) (cdr q))))
      (should-not (eq (car (tl-node-children i1))
                      (car (tl-node-children i2))))
      (should-not (eq (tl-gnode-deref (car (tl-node-children i1)))
                      (car q))))))

;;; Unification-driven overload resolution

(ert-deftest tl-resolve-overload ()
  "The overload whose parameter unifies with the operand type wins."
  (let* ((list-int (tl-gtype-from-tcon (tl-tcon 'List (list (tl-tint)))))
         (prog (tl-tscheme nil (tl-tarrow (tl-tcon '% nil) (tl-tbool))))
         (lst (let ((a (tl-fresh-tvar)))
                (tl-tscheme (list a)
                            (tl-tarrow (tl-tcon 'List (list a))
                                       (tl-tbool)))))
         (cands (list (cons 'prog prog) (cons 'list lst))))
    ;; A List operand matches the list method, not the domain method.
    (should (eq (tl-resolve-overload list-int cands) 'list))
    ;; A domain value matches the program's method.
    (should (eq (tl-resolve-overload (tl-tcon '% nil) cands) 'prog))
    ;; An unrelated operand matches neither.
    (should-not (tl-resolve-overload (tl-tint) cands))))

;;; Graph-native instance resolution / entailment

(ert-deftest tl-entail-instances ()
  "Instances are matched by one-way graph matching, with entailed context."
  (let ((env (termlisp-make-env)))
    (tl-register-class env '(class Eq (a) nil))
    (tl-register-instance env '(instance (Eq Int) EqIntDict))
    (should (tl-entail-by-inst env (tl-constraint 'Eq (tl-tint))))
    (should-not (tl-entail-by-inst env (tl-constraint 'Eq (tl-tstring))))
    ;; Eq a => Eq (List a): the context is entailed recursively.
    (let ((a (tl-fresh-tvar)))
      (puthash 'Eq
               (cons (tl-instance 'Eq (tl-tcon 'List (list a))
                                  (list (tl-constraint 'Eq a)) nil nil)
                     (gethash 'Eq (tl-env-instance-env env)))
               (tl-env-instance-env env))
      (should (tl-entail-by-inst
               env (tl-constraint 'Eq (tl-tcon 'List (list (tl-tint))))))
      (should-not (tl-entail-by-inst
                   env (tl-constraint 'Eq (tl-tcon 'List (list (tl-tstring)))))))))

(ert-deftest tl-entail-superclass ()
  "A predicate is entailed by a superclass of one already held."
  (let ((env (termlisp-make-env)))
    (tl-register-class env '(class Eq (a) nil))
    (tl-register-class env '(class Ord (a) ((Eq (a)))))
    (should (tl-entail env (list (tl-constraint 'Ord (tl-tint)))
                       (tl-constraint 'Eq (tl-tint))))
    (should-not (tl-entail env (list (tl-constraint 'Ord (tl-tint)))
                           (tl-constraint 'Eq (tl-tstring))))))

(ert-deftest tl-context-reduction ()
  "split-context, ambiguity detection and defaulting."
  (let ((a (tl-fresh-tvar)) (b (tl-fresh-tvar)))
    ;; A predicate mentioning a generalized variable is retained; a
    ;; ground one is deferred.
    (let ((sp (tl-split-context
               nil (list a)
               (list (tl-constraint 'Eq (tl-tcon 'List (list a)))
                     (tl-constraint 'Eq (tl-tint))))))
      (should (= 1 (length (car sp))))
      (should (= 1 (length (cadr sp)))))
    ;; An ambiguous Num predicate defaults its variable to Int.
    (let ((subs (tl-default-subs nil (list (tl-constraint 'Num b)))))
      (should (equal (cdr (assq b subs)) (tl-tint))))
    ;; A predicate over an undetermined variable is ambiguous.
    (should (= 1 (length (tl-ambiguities
                          nil nil
                          (list (tl-constraint 'Eq (tl-tcon 'List (list a))))))))))

;;; Kind checking

(ert-deftest tl-kind-check ()
  "Constructors must be applied at their arity; datatype arities register."
  (let ((env (termlisp-make-env)))
    (should (tl-kind-check env (tl-tcon 'List (list (tl-tint)))))
    (should-error (tl-kind-check env (tl-tcon 'Int (list (tl-tint)))))
    (tl-register-datatype-types env 'Pair '((Pair a b)))
    (should (tl-kind-check env (tl-tcon 'Pair (list (tl-tint) (tl-tstring)))))
    (should-error (tl-kind-check env (tl-tcon 'Pair (list (tl-tint)))))))

(ert-deftest tl-kind-vars ()
  "Type variables get a kind arity from their use; inconsistent use errors."
  (let ((env (termlisp-make-env))
        (f (tl-fresh-tvar))
        (a (tl-fresh-tvar))
        (b (tl-fresh-tvar)))
    ;; `f a -> f a': f is a unary constructor, consistently.
    (should (tl-kind-check env (tl-tarrow (tl-tcon f (list a))
                                          (tl-tcon f (list b)))))
    (should (= 1 (tl-node-kind f)))
    ;; `f a b': f used at arity 2 now conflicts with arity 1.
    (should-error (tl-kind-check env (tl-tcon f (list a b)))))
  ;; A kind clash between two known head variables is caught during unify.
  (let ((f (tl-fresh-tvar)) (g (tl-fresh-tvar)) (a (tl-fresh-tvar)))
    (setf (tl-node-kind f) 1)
    (setf (tl-node-kind g) 2)
    (should-error (tl-unify-types (tl-tcon f (list a)) (tl-tcon g (list a)) nil)
                  :type 'termlisp-type-error)))

;;; Constraint improvement

(ert-deftest tl-fundep-improvement ()
  "A functional dependency unifies determined predicate parameters."
  (let ((env (termlisp-make-env))
        (b1 (tl-fresh-tvar)) (b2 (tl-fresh-tvar)))
    (tl-register-class env '(class Conv (a b) nil (fundeps (a -> b))))
    (let* ((i (tl-tint))
           (c1 (tl-constraint 'Conv (tl-tcon 'Conv (list i b1))))
           (c2 (tl-constraint 'Conv (tl-tcon 'Conv (list i b2)))))
      (should (tl-improve-constraints env (list c1 c2)))
      (should (eq (tl-gnode-deref b1) (tl-gnode-deref b2)))
      ;; `a' is fixed, so the fundep determines `b': not ambiguous.
      (should (null (tl-ambiguities env nil (list c1))))
      ;; With an undetermined `a', the whole predicate is ambiguous.
      (should (= 1 (length (tl-ambiguities
                            env nil
                            (list (tl-constraint 'Conv (tl-tcon 'Conv
                                                                (list (tl-fresh-tvar) b1)))))))))))

;;; Dictionary-passing elaboration

(ert-deftest tl-dictionary-passing ()
  "Class-constrained definitions and calls elaborate with dictionaries.
A definition whose inferred scheme carries a class constraint acquires a
dictionary parameter; a call to that function threads the dictionary, and
a ground method call resolves a concrete instance dictionary."
  (let ((env (termlisp-make-env '(:elaborate t :type-check t))))
    (termlisp-load-prelude env)
    (should (equal (tl-elaborate-form
                    env
                    (car (termlisp-parse
                          "(define (twice g x) (fmap g (fmap g x)))")))
                   '(define (twice $dFunctor0 g x)
                      (fmap $dFunctor0 g (fmap $dFunctor0 g x)))))
    (should (equal (tl-elaborate-form
                    env
                    (car (termlisp-parse
                          "(fmap (lambda (x) (+ x 1)) (Just 4))")))
                   '(fmap FunctorMaybeDict (lambda (x) (+ x 1)) (Just 4))))))

(ert-deftest tl-numeric-class ()
  "Arithmetic is an overloaded class; instances are selected by operand type."
  (let ((env (termlisp-make-env '(:elaborate t :type-check t))))
    (termlisp-load-prelude env)
    (should (equal (tl-elaborate-form
                    env (car (termlisp-parse "(num-add 1 2)")))
                   '(num-add IntNumDict 1 2)))
    (should (equal (tl-elaborate-form
                    env
                    (car (termlisp-parse "(define (double x) (num-add x x))")))
                   '(define (double $dNum0 x) (num-add $dNum0 x x))))
    (termlisp-eval "(define (double x) (num-add x x))" env)
    (should (equal (termlisp-eval "(double 21)" env) 42))))

(ert-deftest tl-nested-instance-dict ()
  "An instance with a context builds its dictionary from sub-dictionaries."
  (let ((env (termlisp-make-env)))
    (tl-register-class env '(class C (a) nil))
    (tl-register-instance env '(instance (C Int) CIntDict))
    (tl-register-instance env '(instance (C (List a)) ((C a)) c-list-dict))
    (should (equal (tl-resolve-instance-dict
                    env (tl-constraint 'C (tl-tint)) nil)
                   'CIntDict))
    (should (equal (tl-resolve-instance-dict
                    env (tl-constraint 'C (tl-tcon 'List (list (tl-tint)))) nil)
                   '(c-list-dict CIntDict)))))

(provide 'aldor-test)
;;; aldor-test.el ends here
