EMACS ?= emacs

.PHONY: test compile clean submodule

# Fetch the emacs-cats submodule on demand.  The file dependency means the
# recipe runs only when the submodule has not been checked out yet.
vendor/cats/cats.el:
	git submodule update --init --recursive

submodule: vendor/cats/cats.el
	@:

test: submodule clean
	$(EMACS) -Q --batch -L . -L test -L vendor/cats -l test/termlisp-test.el \
	  -f ert-run-tests-batch-and-exit

compile: submodule
	$(EMACS) -Q --batch -L . -L test -L vendor/cats \
	  -f batch-byte-compile termlisp*.el

clean:
	rm -f *.elc test/*.elc vendor/cats/*.elc
