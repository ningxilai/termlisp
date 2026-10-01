EMACS ?= emacs

.PHONY: test compile clean

test: clean
	$(EMACS) -Q --batch -L . -L test -L vendor/cats -l test/termlisp-test.el \
	  -f ert-run-tests-batch-and-exit

compile:
	$(EMACS) -Q --batch -L . -L test -L vendor/cats \
	  -f batch-byte-compile termlisp*.el

clean:
	rm -f *.elc test/*.elc vendor/cats/*.elc
