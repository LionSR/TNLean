# Physical-matrix ownership audit

## Scope

Continue the preparation dependency separation tracked in #8637. Move existing
MPS-typed reshape and Gram identities out of preparation/convergence modules into
`TNLean.MPS.Core.PhysicalMatrix`. This is an ownership change, not a new circuit,
channel, tensor, or approximation formalism.

Baseline: `b46e0aabb2c621dcf12946bac229f0d4e9143070`.

## Preserved public API

The following declarations keep their namespace, name, statement, proof, and
attributes. All three moved source blocks are byte-identical to the baseline.

From `MPS.Preparation.BlockedPolar`:

- `MPSTensor.physicalMatrix`
- `MPSTensor.ofPhysicalMatrix`
- `MPSTensor.ofPhysicalMatrix_physicalMatrix`
- `MPSTensor.physicalMatrix_ofPhysicalMatrix`
- `MPSTensor.physicalMatrix_injective`
- `MPSTensor.physicalMatrix_rotatePhysical`

From `MPS.Preparation.ApproximatingState`:

- `MPSTensor.conjTranspose_physicalMatrix_mul_physicalMatrix_apply`
- `MPSTensor.conjTranspose_physicalMatrix_mul_apply`

Both original modules import the new owner, preserving their public import surface.
Polar factors, injectivity-to-polar arguments, and spectral convergence stay in the
existing preparation modules. Existing Gram consumers include `PositivePartRate`
and `OverlappingBlockGram`; their statements and proof text do not change.

## Dependency boundary

The new owner imports `MPS.Core.PhysicalRotation`, `QICLean.Kraus.Transfer`, and
`QICLean.Kraus.MixedMap`. Its TNLean closure consists of three modules: itself,
`MPS.Core.PhysicalRotation`, and `MPS.Defs`. A source-level traversal counts 12
non-Mathlib modules in total and finds no preparation, canonical-form, circuit,
Gametheory, or whole-Mathlib import.

The higher `ApproximatingState` module still needs convergence theory; that is
intentional. Algebra-only consumers can now import the core owner directly rather
than importing its 345-module non-Mathlib convergence closure or rederiving the
same Gram entries locally. Counts are for the pinned baseline and include each
traversal's root module.

## Verification

- Source comparison confirms byte-identical moved declaration blocks.
- Generated import frontier includes the new owner.
- At candidate `3c754f2dcfabb55e04dd92a30416a75ba5d80d3d`, an isolated exact-source
  build passed with the repository's Lean options and zero diagnostics for
  `Core.PhysicalMatrix`, `Preparation.BlockedPolar`, `FixedPointPairState`,
  `SupportedPolar`, and `BlockIsometryState`. Reused dependencies were checked
  against source and build-trace hashes; affected dependencies were rebuilt.
- Full-root remote CI remains required for the broader `ApproximatingState`,
  `PositivePartRate`, and `OverlappingBlockGram` consumers.
