/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixRankKronecker
import QICLean.Channel.SingleKrausPositivity
import TNLean.MPS.MPDO.RFPViaTSGlobal
import TNLean.MPS.MPDO.StrongRFP

/-!
# Periodic rank growth of a strong renormalization fixed point

CPSV16 Appendix D observes that the local Strong-RFP relation
\(M₂ = U (M₁ ⊗ P) U†\) iterates around a periodic chain. Thus adjoining one
site tensors the periodic operator with the same positive matrix \(P\), up to a
unitary change of physical coordinates, and its ordinary matrix rank is
multiplied by \(\operatorname{rank} P\).

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix D,
  lines 2109--2117 (labels `Strong-RFP` and the paragraph following it).
-/

open scoped Matrix Kronecker ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The canonical shuffle which places the newly prepared physical coordinate
next to the first coordinate of a chain.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2117. -/
def firstSitePreparationEquiv (N : ℕ) :
    ((Fin d × (Fin N → Fin d)) × Fin d) ≃ ((Fin d × Fin d) × (Fin N → Fin d)) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Localizing a preparation map at the first site is, after the canonical
shuffle, the Kronecker product with the prepared matrix. -/
theorem tensorMapId_preparationMap_eq_reindex_kronecker
    (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (A : Matrix (Fin d × (Fin N → Fin d)) (Fin d × (Fin N → Fin d)) ℂ) :
    Matrix.tensorMapId (Matrix.preparationMap P) A =
      Matrix.reindex (firstSitePreparationEquiv (d := d) N)
        (firstSitePreparationEquiv (d := d) N) (A ⊗ₖ P) := by
  ext ⟨⟨i, j⟩, u⟩ ⟨⟨k, l⟩, v⟩
  simp [Matrix.tensorMapId_apply, Matrix.preparationMap, Matrix.bipartiteSlice,
    Matrix.reindex_apply, firstSitePreparationEquiv]

/-- Applying a unitary conjugation to the first factor is conjugation by the
Kronecker product of that unitary with the identity. -/
private theorem tensorMapId_singleKrausMap
    {α δ : Type*} [Fintype α] [Fintype δ] [DecidableEq δ]
    (U : Matrix α α ℂ) (X : Matrix (α × δ) (α × δ) ℂ) :
    Matrix.tensorMapId (singleKrausMap U) X =
      singleKrausMap (U ⊗ₖ (1 : Matrix δ δ ℂ)) X := by
  ext ⟨i, u⟩ ⟨j, v⟩
  simp only [Matrix.tensorMapId_apply, singleKrausMap_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Matrix.bipartiteSlice]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]
  · simp

/-- The fixed Strong-RFP witnesses give the global closure identity. The
canonical regroupings expose the operation as first adjoining \(P\), then
conjugating the first two coordinates by \(U\).

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2117. -/
theorem strongRFP_physCloseN_eq_localized_preparation
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrel : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    physCloseN M (N + 2) X =
      refineFirstSite ((singleKrausMap U).comp (Matrix.preparationMap P)) N
        (physCloseN M (N + 1) X) := by
  symm
  apply refineFirstSite_physCloseN
  intro Y
  simp only [LinearMap.comp_apply, singleKrausMap_apply]
  exact (hrel Y).symm

/-- Written with all canonical regroupings visible, the global closure is
unitarily equivalent to the Kronecker product of the shorter closure with
\(P\). This is the fixed-witness operator identity used for rank growth.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2117. -/
theorem strongRFP_physCloseN_eq_reindex_singleKrausMap_kronecker
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrel : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    physCloseN M (N + 2) X =
      Matrix.reindex (finAddTwoArrowEquiv (Fin d) N).symm
        (finAddTwoArrowEquiv (Fin d) N).symm
        (singleKrausMap (U ⊗ₖ (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ))
          (Matrix.reindex (firstSitePreparationEquiv (d := d) N)
            (firstSitePreparationEquiv (d := d) N)
            (Matrix.reindex (finSuccArrowEquiv (Fin d) N)
              (finSuccArrowEquiv (Fin d) N) (physCloseN M (N + 1) X) ⊗ₖ P))) := by
  rw [strongRFP_physCloseN_eq_localized_preparation M P U hrel N]
  simp only [refineFirstSite, LinearMap.comp_apply, Matrix.equivReindexMap,
    Matrix.tensorMapIdLM_apply]
  change Matrix.reindex _ _ (Matrix.tensorMapId _ (Matrix.reindex _ _ _)) = _
  change Matrix.reindex _ _
    (Matrix.tensorMapId (singleKrausMap U)
      (Matrix.tensorMapId (Matrix.preparationMap P) (Matrix.reindex _ _ _))) = _
  rw [tensorMapId_singleKrausMap,
    tensorMapId_preparationMap_eq_reindex_kronecker]

/-- The fixed Strong-RFP witnesses give the corresponding identity for the
ordinary periodic MPO operator.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2117. -/
theorem strongRFP_mpo_eq_localized_preparation
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrel : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ)
    (N : ℕ) :
    mpo M (N + 2) =
      refineFirstSite ((singleKrausMap U).comp (Matrix.preparationMap P)) N
        (mpo M (N + 1)) := by
  rw [← physCloseN_identity_eq_mpo M (N + 2),
    strongRFP_physCloseN_eq_localized_preparation M P U hrel N,
    physCloseN_identity_eq_mpo]

/-- With the same canonical regroupings, the ordinary periodic operator on
`N+2` sites is unitarily equivalent to `mpo M (N+1) ⊗ₖ P`.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2117. -/
theorem strongRFP_mpo_eq_reindex_singleKrausMap_kronecker
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrel : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ)
    (N : ℕ) :
    mpo M (N + 2) =
      Matrix.reindex (finAddTwoArrowEquiv (Fin d) N).symm
        (finAddTwoArrowEquiv (Fin d) N).symm
        (singleKrausMap (U ⊗ₖ (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ))
          (Matrix.reindex (firstSitePreparationEquiv (d := d) N)
            (firstSitePreparationEquiv (d := d) N)
            (Matrix.reindex (finSuccArrowEquiv (Fin d) N)
              (finSuccArrowEquiv (Fin d) N) (mpo M (N + 1)) ⊗ₖ P))) := by
  rw [← physCloseN_identity_eq_mpo M (N + 2),
    strongRFP_physCloseN_eq_reindex_singleKrausMap_kronecker M P U hrel N,
    physCloseN_identity_eq_mpo]

/-- The fixed Strong-RFP witnesses force the ordinary periodic MPO rank to
obey the one-step recurrence
`rank (mpo M (N+2)) = rank (mpo M (N+1)) * rank P`.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2114--2117. -/
theorem strongRFP_rank_mpo_add_two
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hrel : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ)
    (N : ℕ) :
    (mpo M (N + 2)).rank = (mpo M (N + 1)).rank * P.rank := by
  rw [strongRFP_mpo_eq_localized_preparation M P U hrel N]
  simp only [refineFirstSite, LinearMap.comp_apply, Matrix.equivReindexMap]
  change (Matrix.reindex _ _ _).rank = _
  rw [Matrix.rank_reindex]
  rw [Matrix.tensorMapIdLM_comp]
  simp only [LinearMap.comp_apply, Matrix.tensorMapIdLM_apply]
  rw [tensorMapId_singleKrausMap]
  rw [Matrix.rank_singleKrausMap_of_mem_unitaryGroup _ _
    (Matrix.kronecker_mem_unitary hU (one_mem _))]
  rw [tensorMapId_preparationMap_eq_reindex_kronecker, Matrix.rank_reindex,
    Matrix.rank_kronecker]
  change (Matrix.reindex _ _ _).rank * P.rank = _
  rw [Matrix.rank_reindex]

/-- Iterating the fixed-witness recurrence from chain length one gives the
geometric rank formula.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2114--2117. -/
theorem strongRFP_rank_mpo_add_one
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hrel : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      physClose2 M X = U * (physClose1 M X ⊗ₖ P) * Uᴴ) :
    ∀ N : ℕ,
      (mpo M (N + 1)).rank = (mpo M 1).rank * P.rank ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      simpa [pow_succ, ih, mul_assoc] using
        strongRFP_rank_mpo_add_two M P U hU hrel N

/-- A Strong-RFP tensor exposes a single positive witness \(P\) whose rank is
the factor in both the periodic rank recurrence and its geometric solution.
No trace normalization, virtual gauge, or MPDO hypothesis is used.

Source: CPSV16, arXiv:1606.00608, Appendix D, lines 2109--2117. -/
theorem IsStrongRFP.exists_periodic_rank_factor
    {M : MPOTensor d D} (h : IsStrongRFP M) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ,
      P.PosSemidef ∧
      (∀ N : ℕ, (mpo M (N + 2)).rank = (mpo M (N + 1)).rank * P.rank) ∧
      (∀ N : ℕ, (mpo M (N + 1)).rank = (mpo M 1).rank * P.rank ^ N) := by
  rw [isStrongRFP_iff_physClose] at h
  obtain ⟨P, U, hP, hU, hrel⟩ := h
  exact ⟨P, hP, strongRFP_rank_mpo_add_two M P U hU hrel,
    strongRFP_rank_mpo_add_one M P U hU hrel⟩

end MPOTensor
