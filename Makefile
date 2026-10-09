EMACS ?= emacs

# `cats' is the one external dependency (`termlisp-data-reader').  It is a
# normal package dependency, so it is expected on the load-path; by default
# we take it from the elpaca sources directory.  Override CATS_DIR if you
# keep a checkout elsewhere.
CATS_DIR ?= $(HOME)/.config/emacs/elpaca/sources/cats
LOAD_PATH = -L .
ifneq ($(wildcard $(CATS_DIR)/cats.el),)
LOAD_PATH += -L $(CATS_DIR)
endif

.PHONY: compile clean

compile: clean
	$(EMACS) -Q --batch $(LOAD_PATH) -f batch-byte-compile termlisp*.el

clean:
	rm -f *.elc
