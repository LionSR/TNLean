/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.Basic
import TNLean.MPS.CanonicalForm.CyclicSectors.Compression
import TNLean.MPS.CanonicalForm.CyclicSectors.CompressionPositive
import TNLean.MPS.CanonicalForm.CyclicSectors.CommutingProj
import TNLean.MPS.CanonicalForm.CyclicSectors.FixedAdjoint

/-!
# Cyclic-sector decompositions for blocked MPS tensors

This module keeps the historical import path
`TNLean.MPS.CanonicalForm.CyclicSectors` while the development is organized
across five focused supporting modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.CyclicSectors.Basic` — the
  `BasicProjectionWordLemmas` section.
* `TNLean.MPS.CanonicalForm.CyclicSectors.Compression` — the
  `Compression` section.
* `TNLean.MPS.CanonicalForm.CyclicSectors.CompressionPositive` — the
  `CompressionPositiveMPV` section.
* `TNLean.MPS.CanonicalForm.CyclicSectors.CommutingProj` — the
  `CommutingProjectionDecomposition` section.
* `TNLean.MPS.CanonicalForm.CyclicSectors.FixedAdjoint` — the
  `FixedAdjointProjection` section.

## Main statements

The imported modules provide the original declarations at their historical
names, including
`exists_compressedTensor_of_supported_projection`,
`exists_compressedTensor_of_supported_projection_pos_mpv`,
`exists_blockDecomp_of_commuting_projections`,
`commutes_letters_of_adjoint_fixed_projection`, and
`exists_blockDecomp_of_adjoint_fixed_projections`.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]
-/
