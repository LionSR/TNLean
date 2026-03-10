/-
Copyright (c) 2025 TNLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Experimental TNLean entrypoint

This module is intentionally excluded from `TNLean.lean`. It gathers non-stable
modules that are kept either for active work or for documentary reasons.

At present it re-exports:
* `TNLean.PiAlgebra.CanonicalFormSep`, the newer non-stable block-separation
  development.

The abandoned `TNLean.PiAlgebra.BlockSeparationProof` module remains in the
repository only for historical inspection; it is not re-exported here because
its downstream block-separation route still contains a known-false `sorry`.

Use `import TNLean` for the maintained, sorry-free library surface.
-/

import TNLean

-- Block separation attempts
import TNLean.PiAlgebra.CanonicalFormSep
