/-
Copyright (c) 2025 TNLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Experimental TNLean entrypoint

This module is intentionally excluded from `TNLean.lean`.

Historically it served as a convenience entrypoint for non-stable Pi-algebra
work. At present it is entirely vestigial: the former extra import
`TNLean.PiAlgebra.CanonicalFormSep` is already on the main proof path via
`TNLean.MPS.BNTConstruction`, `TNLean.MPS.CanonicalFormFromPrimitive`, and
`TNLean.MPS.NormalCanonicalFormPipeline`, so this file currently adds no
imports beyond `TNLean`.

The abandoned `TNLean.PiAlgebra.BlockSeparationProof` module remains in the
repository only for historical inspection; it is not re-exported here because
its downstream block-separation route still contains a known-false `sorry`.

Prefer `import TNLean` unless you specifically want this historical umbrella
module.
-/

import TNLean
