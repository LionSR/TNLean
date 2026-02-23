/-
Copyright (c) 2025 TNLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Experimental / work-in-progress modules

This module is **not** imported by `TNLean` (the main stable entrypoint).
It collects results that are:
- incomplete (`sorry`),
- known-false as stated but kept for documentation/counterexamples, or
- active research prototypes.

Use this module for exploratory development, while keeping `import TNLean`
free of sorries for downstream users.
-/

import TNLean

-- Block separation attempts
import TNLean.PiAlgebra.BlockSeparationProof
import TNLean.PiAlgebra.CanonicalFormSep
