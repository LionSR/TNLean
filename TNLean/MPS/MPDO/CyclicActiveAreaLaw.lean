/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveMarkovDecomposition
import TNLean.MPS.MPDO.PhysicalSupportSALTransport
import TNLean.MPS.MPDO.SALArbitraryCut

/-!
# Area law from the cyclic-active Markov decomposition

This file transports the all-cut quantum-Markov decomposition in physical-sector
coordinates back to the original physical basis.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1597--1619.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- A positive physical-sector factorization with source zero correlation
length saturates the area law.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1619.

**Scope restriction (physical-sector factorization):** The theorem assumes the
physical-sector factorization and positivity of its neighboring operators.
The source derives this structure from a translation-invariant commuting bond.
The missing non-circular bridge is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem isSAL_of_isSourceZCL (F : PhysicalSectorFactorization K) [NeZero D]
    (hK : K.IsInjective)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hZCL : K.IsSourceZCL) : IsSAL K := by
  have hMpdo : IsMPDO F.sectorCoordinateTensor := by
    intro N hN
    letI : NeZero N := ⟨ne_of_gt hN⟩
    exact F.mpo_sectorCoordinateTensor_posSemidef hpos
  have htrace : ∀ N, 0 < N → Matrix.trace
      (mpo F.sectorCoordinateTensor N) ≠ 0 := by
    intro N hN
    exact ne_of_gt
      (F.trace_mpo_sectorCoordinateTensor_pos_of_isSourceZCL hpos hZCL hN)
  have hCoordinateSAL : IsSAL F.sectorCoordinateTensor := by
    apply isSAL_of_quantumMarkovDecomposition_tripartite_m
      F.sectorCoordinateTensor hMpdo htrace
    intro N m hm1 hmN
    dsimp only
    have hlength : (m - 1) + (N - m - 1) + 2 = N := by omega
    convert
      F.exists_hayashiMarkovDecomposition_cyclicActiveCut_of_isSourceZCL
        hK hpos hZCL (m - 1) (N - m - 1) using 1
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, hlength]
  apply isSAL_of_changePhysicalBasis_isSAL_of_isometry
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry K
  rw [← F.sectorCoordinateTensor_eq_changePhysicalBasis]
  exact hCoordinateSAL

end MPOTensor.PhysicalSectorFactorization
