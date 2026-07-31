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
coordinates back to the original physical basis.  It also proves the
source-faithful fixed-bond implication from source zero correlation length to
saturation of the area law.

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
It is therefore a conditional explicit-factorization result, rather than the
source proposition by itself. The source-faithful implication from a
translation-invariant commuting bond is
`EtaLocalStructureData.isSAL_of_isSourceZCL`; see
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

namespace MPOTensor.EtaLocalStructureData

variable {d D : ℕ} {K : MPOTensor d D}

/-- An injective tensor generating matrix-product density operators, with a
fixed translation-invariant positive commuting-bond presentation and source
zero correlation length, saturates the area law.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1619.

**Local fix (cyclic-active two-step coefficient):** The argument at source
lines 1613--1616 uses an invalid one-step inference that the neighboring trace
matrix has rank one. This proof instead uses the documented positive rank-one
factorization of the cyclic-active two-step coefficient and transports the
resulting normalized marginals from the selected fixed-product tensor to the
source tensor. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem isSAL_of_isSourceZCL
    (hMPDO : IsMPDO K) (hK : K.IsInjective)
    (data : EtaLocalStructureData K) (hZCL : K.IsSourceZCL) :
    IsSAL K := by
  let F :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  let U := F.physicalCoordinateMatrix
  let M := PhysicalSectorFactorization.changePhysicalBasis U K
  have hMMPDO : IsMPDO M := by
    intro N hN
    dsimp only [M]
    rw [← singleKrausMap_sitewisePhysicalMatrix_mpo]
    exact (hMPDO N hN).mul_mul_conjTranspose_same
      (sitewisePhysicalMatrix U N)
  have hMtrace : ∀ N, 0 < N → Matrix.trace (mpo M N) ≠ 0 := by
    intro N hN
    dsimp only [M, U]
    rw [trace_mpo_changePhysicalBasis_of_isometry
      F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry]
    exact trace_mpo_ne_zero_of_isSourceZCL K hZCL hN
  have hMSAL : IsSAL M := by
    apply isSAL_of_quantumMarkovDecomposition_tripartite_m M hMMPDO hMtrace
    intro N m hm1 hmN
    dsimp only
    have hlength : (m - 1) + (N - m - 1) + 2 = N := by omega
    convert
      data.exists_hayashiMarkovDecomposition_selectedPhysicalCut_of_isSourceZCL
        hK hZCL (m - 1) (N - m - 1) using 1
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, hlength, M, U, F]
  apply isSAL_of_changePhysicalBasis_isSAL_of_isometry
    U F.physicalCoordinateMatrix_isometry K
  exact hMSAL

end MPOTensor.EtaLocalStructureData
