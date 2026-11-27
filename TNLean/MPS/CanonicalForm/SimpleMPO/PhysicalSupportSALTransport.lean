/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.DensityOperator.AreaLaw
import TNLean.MPS.CanonicalForm.SimpleMPO.PhysicalSupportRestriction
import TNLean.MPS.Operator.PhysicalSector.SitewisePhysicalMatrix
import QICLean.Entropy.VonNeumann.Entropy

/-!
# Saturated-area-law transport through a physical support

Restricting an MPO tensor to an orthogonal one-site support does not change
the nonzero spectrum of any chain state or contiguous marginal.  Consequently,
saturation of the area law passes from the ambient tensor to its injective
restriction.

This is the range-restriction step preceding the injective application of
Proposition C.8 in each BNT sector.

No hypothesis or conclusion concerns the empty periodic chain.  The case
`L = N` does leave a zero-site *complement* in the definition of a marginal;
there `Fin 0` is only the one-dimensional tensor unit for the partial trace,
not an MPO state of length zero.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d e D : ℕ}

open PhysicalSectorFactorization

/-- An isometric physical inclusion preserves the trace of every periodic
MPO, including every positive-length chain used by SAL. -/
theorem trace_mpo_changePhysicalBasis_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (N : ℕ) :
    Matrix.trace (mpo (changePhysicalBasis V M) N) =
      Matrix.trace (mpo M N) := by
  rw [← singleKrausMap_piKronecker_mpo]
  exact (singleKrausMap_isKrausCPTP (Matrix.piKronecker fun _ : Fin N ↦ V)
    (Matrix.piKronecker_const_isometry V hV N)).trace_map (mpo M N)

/-- Normalization commutes with an isometric physical inclusion. -/
theorem normalizedMPO_changePhysicalBasis_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (N : ℕ) :
    normalizedMPO (changePhysicalBasis V M) N =
      singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V) (normalizedMPO M N) := by
  rw [normalizedMPO, normalizedMPO,
    trace_mpo_changePhysicalBasis_of_isometry V hV M N,
    ← singleKrausMap_piKronecker_mpo]
  exact ((singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)).map_smul _ _).symm

/-- After splitting a chain into a prefix and suffix, the sitewise physical
matrix is the Kronecker product of the corresponding prefix and suffix
matrices. -/
theorem reindex_piKronecker_blockSplit
    (V : Matrix (Fin e) (Fin d) ℂ) (L K : ℕ) :
    Matrix.reindex (MPOTensor.blockSplitEquiv e L K)
        (MPOTensor.blockSplitEquiv d L K)
        (Matrix.piKronecker fun _ : Fin (L + K) ↦ V) =
      Matrix.kroneckerMap (· * ·)
        (Matrix.piKronecker fun _ : Fin L ↦ V) (Matrix.piKronecker fun _ : Fin K ↦ V) := by
  ext ⟨a, b⟩ ⟨x, y⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.piKronecker_apply,
    Matrix.kroneckerMap_apply, MPOTensor.blockSplitEquiv_symm_apply]
  rw [Fin.prod_univ_add]
  simp

/-- Reassociating the chain length from `N` to `L + (N - L)` does not alter
the sitewise physical matrix. -/
theorem reindex_piKronecker_blockReindex
    (V : Matrix (Fin e) (Fin d) ℂ) (N L : ℕ) (hL : L ≤ N) :
    Matrix.reindex (blockReindexEquiv e N L hL)
        (blockReindexEquiv d N L hL) (Matrix.piKronecker fun _ : Fin N ↦ V) =
      (Matrix.piKronecker fun _ : Fin (L + (N - L)) ↦ V) := by
  ext s t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.piKronecker_apply, blockReindexEquiv, Equiv.arrowCongr_symm,
    Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    finCongr_symm]
  exact Fintype.prod_equiv (finCongr (Nat.add_sub_cancel' hL)).symm
    (fun i : Fin N ↦ V (s ((finCongr (Nat.add_sub_cancel' hL)).symm i))
      (t ((finCongr (Nat.add_sub_cancel' hL)).symm i)))
    (fun i : Fin (L + (N - L)) ↦ V (s i) (t i)) (fun _ ↦ rfl)

/-- A sitewise isometry commutes with taking a contiguous prefix marginal.
The isometry on the discarded suffix disappears under the partial trace. -/
theorem blockReducedState_singleKraus_sitewise
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (L K : ℕ)
    (X : Matrix (Fin (L + K) → Fin d) (Fin (L + K) → Fin d) ℂ) :
    MPOTensor.blockReducedState e L K
        (singleKrausMap (Matrix.piKronecker fun _ : Fin (L + K) ↦ V) X) =
      singleKrausMap (Matrix.piKronecker fun _ : Fin L ↦ V)
        (MPOTensor.blockReducedState d L K X) := by
  change Matrix.partialTraceRight
      (Matrix.reindex (MPOTensor.blockSplitEquiv e L K) (MPOTensor.blockSplitEquiv e L K)
        (singleKrausMap (Matrix.piKronecker fun _ : Fin (L + K) ↦ V) X)) = _
  rw [Matrix.reindex_singleKrausMap
      (MPOTensor.blockSplitEquiv d L K) (MPOTensor.blockSplitEquiv e L K),
    reindex_piKronecker_blockSplit]
  exact Matrix.partialTraceRight_kronecker_conj_of_right_isometry
    (Matrix.piKronecker fun _ : Fin L ↦ V) (Matrix.piKronecker fun _ : Fin K ↦ V)
    (Matrix.piKronecker_const_isometry V hV K)
    (Matrix.reindex (MPOTensor.blockSplitEquiv d L K) (MPOTensor.blockSplitEquiv d L K) X)

/-- Every contiguous marginal of a physically included MPO is the isometric
conjugate of the corresponding marginal before inclusion. -/
theorem reducedBlockState_changePhysicalBasis_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N) :
    reducedBlockState (changePhysicalBasis V M) N L hL =
      singleKrausMap (Matrix.piKronecker fun _ : Fin L ↦ V)
        (reducedBlockState M N L hL) := by
  rw [reducedBlockState, reducedBlockState,
    normalizedMPO_changePhysicalBasis_of_isometry V hV]
  change MPOTensor.blockReducedState e L (N - L)
      (Matrix.reindex (blockReindexEquiv e N L hL)
        (blockReindexEquiv e N L hL)
        (singleKrausMap (Matrix.piKronecker fun _ : Fin N ↦ V)
          (normalizedMPO M N))) = _
  rw [Matrix.reindex_singleKrausMap
      (blockReindexEquiv d N L hL) (blockReindexEquiv e N L hL),
    reindex_piKronecker_blockReindex]
  exact blockReducedState_singleKraus_sitewise V hV L (N - L)
    (Matrix.reindex (blockReindexEquiv d N L hL)
      (blockReindexEquiv d N L hL) (normalizedMPO M N))

/-- An isometric physical inclusion does not change a contiguous block
entropy. -/
theorem blockEntropy_changePhysicalBasis_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) :
    blockEntropy (changePhysicalBasis V M) N L hL
        (by
          rw [← singleKrausMap_piKronecker_mpo]
          exact hM.mul_mul_conjTranspose_same
            (Matrix.piKronecker fun _ : Fin N ↦ V)) =
      blockEntropy M N L hL hM := by
  let hM' : (mpo (changePhysicalBasis V M) N).PosSemidef := by
    rw [← singleKrausMap_piKronecker_mpo]
    exact hM.mul_mul_conjTranspose_same (Matrix.piKronecker fun _ : Fin N ↦ V)
  let hρ := reducedBlockState_isHermitian M N L hL hM
  let hρ' := Matrix.isHermitian_mul_mul_conjTranspose
    (Matrix.piKronecker fun _ : Fin L ↦ V) hρ
  change vonNeumannEntropy
      (reducedBlockState (changePhysicalBasis V M) N L hL)
        (reducedBlockState_isHermitian
          (changePhysicalBasis V M) N L hL hM') =
    vonNeumannEntropy (reducedBlockState M N L hL) hρ
  have hred := reducedBlockState_changePhysicalBasis_of_isometry
    V hV M N L hL
  calc
    _ = vonNeumannEntropy
        (singleKrausMap (Matrix.piKronecker fun _ : Fin L ↦ V)
          (reducedBlockState M N L hL)) hρ' :=
      vonNeumannEntropy_congr hred _ _
    _ = _ := vonNeumannEntropy_singleKraus_isometry
      (Matrix.piKronecker fun _ : Fin L ↦ V) (Matrix.piKronecker_const_isometry V hV L)
      (reducedBlockState M N L hL) hρ

/-- An isometric physical inclusion does not change the mutual information
between a contiguous block and its complement. -/
theorem mutualInfoChain_changePhysicalBasis_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) :
    mutualInfoChain (changePhysicalBasis V M) N L hL
        (by
          rw [← singleKrausMap_piKronecker_mpo]
          exact hM.mul_mul_conjTranspose_same
            (Matrix.piKronecker fun _ : Fin N ↦ V)) =
      mutualInfoChain M N L hL hM := by
  simp only [mutualInfoChain_eq]
  rw [blockEntropy_changePhysicalBasis_of_isometry V hV,
    blockEntropy_changePhysicalBasis_of_isometry V hV,
    blockEntropy_changePhysicalBasis_of_isometry V hV]

/-- Saturation of the area law descends through an isometric physical
inclusion.  Only positive chain lengths occur, as in Definition 4.6.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem isSAL_of_changePhysicalBasis_isSAL_of_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (hSAL : IsSAL (changePhysicalBasis V M)) :
    IsSAL M := by
  obtain ⟨hAmbientMpdo, hAmbientTrace, hAmbientStep⟩ := hSAL
  let hMpdo := isMPDO_of_changePhysicalBasis_isMPDO_of_isometry
    V hV M hAmbientMpdo
  refine ⟨hMpdo, ?_, ?_⟩
  · intro N hN
    rw [← trace_mpo_changePhysicalBasis_of_isometry V hV]
    exact hAmbientTrace N hN
  · intro N L hL hLN
    have hstep := hAmbientStep N L hL hLN
    rw [mutualInfoChain_changePhysicalBasis_of_isometry V hV M N L
        (Nat.le_of_lt (hLN.trans_le (Nat.div_le_self N 2))) (hMpdo N (by omega)),
      mutualInfoChain_changePhysicalBasis_of_isometry V hV M N (L + 1)
        (hLN.trans_le (Nat.div_le_self N 2)) (hMpdo N (by omega))] at hstep
    exact hstep

/-- The injective tensor obtained by restricting to an orthogonal physical
support inherits saturation of the area law from the ambient tensor.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem PhysicalSupportRestrictionData.restricted_isSAL
    {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}
    (F : PhysicalSupportRestrictionData P K) (hSAL : IsSAL K) :
    IsSAL (changePhysicalBasis F.inclusionᴴ K) := by
  apply isSAL_of_changePhysicalBasis_isSAL_of_isometry
    F.inclusion F.inclusion_isometry
  rw [F.reembed]
  exact hSAL

end MPOTensor
