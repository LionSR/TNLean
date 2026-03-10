/-
Copyright (c) 2025 TNLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Experimental TNLean entrypoint

This module is intentionally excluded from `TNLean.lean`. It gathers non-stable
modules that are kept either for active work or for documentary reasons.

At present it exposes:
* `TNLean.PiAlgebra.BlockSeparationProof`, the vestigial Vandermonde-based
  block-separation sketch with a known-false `sorry`;
* `TNLean.PiAlgebra.CanonicalFormSep`, the newer non-stable block-separation
  development.

Use `import TNLean` for the maintained, sorry-free library surface.
-/

import TNLean

-- Block separation attempts
import TNLean.PiAlgebra.BlockSeparationProof
import TNLean.PiAlgebra.CanonicalFormSep
