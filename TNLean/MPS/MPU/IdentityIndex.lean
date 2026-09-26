/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftSourceFactors
import TNLean.MPS.MPU.Index
import TNLean.MPS.MPU.TransferStabilizationConverse

/-!
# Index of the bond-one identity tensor

The existing bond-one identity tensor has a canonical-form-II presentation:
its normalized transfer matrix is the one-by-one identity, with fixed matrix
`ρ = 1`. Its right and left source-cut ranks both equal the physical
dimension. Consequently its blocking-independent index is zero, independently
of the chosen canonical-form-II presentation.

This is the identity consequence of the index definition in CPSV17,
arXiv:1703.09188, lines 681–704. The source does not separately state a
bond-one identity-index theorem; its later example at lines 2037–2041 concerns
the three two-spin tensors $U_1,U_2,U_3$, of which $U_1$ is an identity family.

## References

* CPSV17, arXiv:1703.09188, canonical form II (lines 269–281), the
  bond-one transfer argument (lines 397–409), and Definition `def:index`
  with Proposition `index-well-defined` (lines 681–704).
-/

open scoped ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

private theorem blockTensor_one_eq_reindexPhysical (U : MPOTensor d D) :
    blockTensor U 1 = reindexPhysical (Kraus.singleBlockEquiv d) U := by
  ext i j
  simp [blockTensor, reindexPhysical, MPSTensor.wordOfBlock, Kraus.wordOfBlock_one]

/-- The bond-one identity tensor has a full-support canonical-form-II
presentation with the one-by-one fixed matrix `ρ = 1`.

The construction specializes the transfer-power criterion to bond dimension
one. Source: CPSV17, arXiv:1703.09188, canonical form II (lines 269–281)
and the bond-one transfer discussion (lines 397–409). -/
noncomputable def identityMPUTensor_canonicalFormII (d : ℕ) [NeZero d] :
    IsMPUCanonicalFormII (identityMPUTensor d) := by
  refine (identityMPUTensor_isMPU d).canonicalFormIIOfSuppliedTransferPower
    (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.PosDef.one (by simp) 1 ?_
  rw [pow_one, (identityMPUTensor_isMPU d).normalized_transfer_matrix_eq_one_fin_one]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i
  fin_cases j
  fin_cases k
  fin_cases l
  simp [Matrix.vecMulVec_apply]

/-- Every canonical-form-II presentation of the bond-one identity tensor has
index zero.

Its source-cut ranks are both `d`, and one-site blocking only relabels the
physical alphabet. Source: the index definition and blocking independence in
CPSV17, arXiv:1703.09188, lines 681–704. -/
theorem IsMPUCanonicalFormII.index_identityMPUTensor (d : ℕ) [NeZero d]
    (hI : IsMPUCanonicalFormII (identityMPUTensor d)) : hI.index = 0 := by
  have hS : IsMPUSimple (identityMPUTensor d) :=
    (hI.isMPUSimple_tfae.out 1 0).mp (by
      rw [rightRank_identityMPUTensor, leftRank_identityMPUTensor])
  have hS₁ : IsMPUSimple (MPOTensor.blockTensor (identityMPUTensor d) 1) := by
    rw [blockTensor_one_eq_reindexPhysical]
    exact hS.reindexPhysical (Kraus.singleBlockEquiv d)
  rw [hI.index_eq_logb_of_isMPUSimple_blockTensor (by omega) hS₁,
    blockTensor_one_eq_reindexPhysical, rightRank_reindexPhysical,
    leftRank_reindexPhysical, rightRank_identityMPUTensor,
    leftRank_identityMPUTensor, sub_self, mul_zero]

/-- The identity MPU has blocking-independent index zero.

This follows from the index definition of CPSV17, arXiv:1703.09188,
lines 681–704, for its bond-one representative. -/
theorem identityMPUTensor_index (d : ℕ) [NeZero d] :
    (identityMPUTensor_canonicalFormII d).index = 0 :=
  IsMPUCanonicalFormII.index_identityMPUTensor d (identityMPUTensor_canonicalFormII d)

end MPOTensor
