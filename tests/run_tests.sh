#!/usr/bin/env bash
set -euo pipefail

# Run the elisp tests in batch Emacs. This assumes Emacs is on PATH.
EMACS=${EMACS:-emacs}

# Use -Q to avoid user init interference
$EMACS -Q --batch -l setup-typed.el -l tests/test_setup_typed.el

