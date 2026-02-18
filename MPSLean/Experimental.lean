/-
Copyright (c) 2025 MPSLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Experimental / work-in-progress modules

This module is **not** imported by `MPSLean` (the main stable entrypoint).
It collects results that are:
- incomplete (`sorry`),
- known-false as stated but kept for documentation/counterexamples, or
- active research prototypes.

Use this module for exploratory development, while keeping `import MPSLean`
free of sorries for downstream users.
-/

import MPSLean

-- Block separation attempts
import MPSLean.PiAlgebra.BlockSeparationProof
import MPSLean.PiAlgebra.CanonicalFormSep
