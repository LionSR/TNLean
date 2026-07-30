/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveFourthRegionContraction

/-!
# Adjacent cyclic-active suffix marginals

This file specializes the arbitrary-suffix physical-sector block expansion to
the marginals obtained by tracing one or two suffix sites. After tracing the
two surviving outer boundary factors, these adjacent contractions have
coefficients given by the square and cube of the cyclic-active trace matrix.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Trace the last site fiber of a fixed retained sector block of the cyclic
neighboring product, summing over its discarded sector label.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** This is the one-suffix side of
the source-adjacent comparison. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable abbrev oneSuffixSectorContraction
    (F : PhysicalSectorFactorization K) {L : ℕ}
    (k : Fin L → Fin F.sectorCount) :
    Matrix (F.SectorChainFiber k) (F.SectorChainFiber k) ℂ :=
  F.suffixSectorContraction 1 k

/-- Trace the last two site fibers of a fixed retained sector block of the
cyclic neighboring product, summing over both discarded sector labels.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** The two-suffix contraction is
paired with the one-suffix contraction. After tracing the two surviving outer
boundary factors, their coefficients are respectively \(T_C^3\) and
\(T_C^2\). See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable abbrev twoSuffixSectorContraction
    (F : PhysicalSectorFactorization K) {L : ℕ}
    (k : Fin L → Fin F.sectorCount) :
    Matrix (F.SectorChainFiber k) (F.SectorChainFiber k) ℂ :=
  F.suffixSectorContraction 2 k

/-- In complete physical-sector coordinates, the marginal obtained by
discarding one suffix site is the direct sum of the corresponding one-suffix
contractions of the cyclic neighboring products.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** This is the one-suffix side of
the comparison with the two-suffix expansion. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_one_eq_oneSuffixSectorContraction
    (F : PhysicalSectorFactorization K) (L : ℕ) :
    Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 1)))⁻¹ : ℂ) •
        Matrix.blockDiagonal' (fun k ↦ F.oneSuffixSectorContraction k) :=
  F.reindex_reducedBlockState_add_eq_suffixSectorContraction L 1

/-- In complete physical-sector coordinates, the marginal obtained by
discarding two suffix sites is the direct sum of the corresponding two-suffix
contractions of the cyclic neighboring products.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** This is the two-suffix side of
the comparison with the one-suffix expansion. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_two_eq_twoSuffixSectorContraction
    (F : PhysicalSectorFactorization K) (L : ℕ) :
    Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 2)))⁻¹ : ℂ) •
        Matrix.blockDiagonal' (fun k ↦ F.twoSuffixSectorContraction k) :=
  F.reindex_reducedBlockState_add_eq_suffixSectorContraction L 2

end MPOTensor.PhysicalSectorFactorization
