/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.RFPViaTSGlobal

/-!
# Renormalization fixed points under two-site physical blocking

The two maps in the renormalization-fixed-point condition may each be applied
twice. The resulting trace-preserving completely positive maps exchange the
two-site and four-site physical closures. Reindexing these closures by the
canonical blocked coordinates proves that two-site physical blocking preserves
the condition.

## Main result

* `MPOTensor.IsRFPViaTS.blockTwo`: a renormalization fixed point remains one
  after two neighboring physical sites are blocked together.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1, lines 645--659; Theorem 4.9, lines 851--893; and the
  twice-applied channel construction at lines 1810--1825.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

private lemma equivReindexMap_symm_apply_self
    {α β : Type*} (e : α ≃ β) (X : Matrix α α ℂ) :
    Matrix.equivReindexMap e.symm (Matrix.equivReindexMap e X) = X := by
  ext i j
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv]

/-- Apply a one-to-two physical channel twice, in product coordinates. -/
private noncomputable def refinementSquaredMap
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × (Fin d × (Fin d × Fin d)))
        (Fin d × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.equivReindexMap (_root_.finFourArrowEquiv (Fin d)) ∘ₗ
    refineFirstSite T 2 ∘ₗ
      refineFirstSite T 1 ∘ₗ
        Matrix.equivReindexMap (finTwoArrowEquiv (Fin d)).symm

/-- Apply a two-to-one physical channel twice, in product coordinates. -/
private noncomputable def coarseningSquaredMap
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × (Fin d × Fin d)))
        (Fin d × (Fin d × (Fin d × Fin d))) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.equivReindexMap (finTwoArrowEquiv (Fin d)) ∘ₗ
    coarsenFirstTwoSites S 1 ∘ₗ
      coarsenFirstTwoSites S 2 ∘ₗ
        Matrix.equivReindexMap (_root_.finFourArrowEquiv (Fin d)).symm

private theorem refinementSquaredMap_isKrausCPTP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hT : IsKrausCPTP T) : IsKrausCPTP (refinementSquaredMap T) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP (finTwoArrowEquiv (Fin d)).symm)
        (refineFirstSite_isKrausCPTP hT 1))
      (refineFirstSite_isKrausCPTP hT 2))
    (Matrix.equivReindexMap_isKrausCPTP (_root_.finFourArrowEquiv (Fin d)))

private theorem coarseningSquaredMap_isKrausCPTP
    {S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ}
    (hS : IsKrausCPTP S) : IsKrausCPTP (coarseningSquaredMap S) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP
          (_root_.finFourArrowEquiv (Fin d)).symm)
        (coarsenFirstTwoSites_isKrausCPTP hS 2))
      (coarsenFirstTwoSites_isKrausCPTP hS 1))
    (Matrix.equivReindexMap_isKrausCPTP (finTwoArrowEquiv (Fin d)))

private theorem refinementSquaredMap_physClose2
    (M : MPOTensor d D)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : ∀ X, T (physClose1 M X) = physClose2 M X)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    refinementSquaredMap T (physClose2 M X) = physClose4 M X := by
  rw [refinementSquaredMap]
  simp only [LinearMap.comp_apply]
  rw [← LinearMap.congr_fun (physCloseN_two_eq_physClose2 M) X]
  simp only [LinearMap.comp_apply]
  change Matrix.equivReindexMap (_root_.finFourArrowEquiv (Fin d))
      (refineFirstSite T 2
        (refineFirstSite T 1
          (Matrix.equivReindexMap (finTwoArrowEquiv (Fin d)).symm
            (Matrix.equivReindexMap (finTwoArrowEquiv (Fin d))
              (physCloseN M 2 X))))) = physClose4 M X
  rw [equivReindexMap_symm_apply_self]
  rw [refineFirstSite_physCloseN M T hT 1 X]
  rw [refineFirstSite_physCloseN M T hT 2 X]
  exact LinearMap.congr_fun (physCloseN_four_eq_physClose4 M) X

private theorem coarseningSquaredMap_physClose4
    (M : MPOTensor d D)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : ∀ X, S (physClose2 M X) = physClose1 M X)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    coarseningSquaredMap S (physClose4 M X) = physClose2 M X := by
  rw [coarseningSquaredMap]
  simp only [LinearMap.comp_apply]
  rw [← LinearMap.congr_fun (physCloseN_four_eq_physClose4 M) X]
  simp only [LinearMap.comp_apply]
  change Matrix.equivReindexMap (finTwoArrowEquiv (Fin d))
      (coarsenFirstTwoSites S 1
        (coarsenFirstTwoSites S 2
          (Matrix.equivReindexMap (_root_.finFourArrowEquiv (Fin d)).symm
            (Matrix.equivReindexMap (_root_.finFourArrowEquiv (Fin d))
              (physCloseN M 4 X))))) = physClose2 M X
  rw [equivReindexMap_symm_apply_self]
  rw [coarsenFirstTwoSites_physCloseN M S hS 2 X]
  rw [coarsenFirstTwoSites_physCloseN M S hS 1 X]
  exact LinearMap.congr_fun (physCloseN_two_eq_physClose2 M) X

private noncomputable def blockedRefinementMap
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ :=
  Matrix.equivReindexMap (blockedPairEquiv d).symm ∘ₗ
    refinementSquaredMap T ∘ₗ
      Matrix.equivReindexMap (blockedIndexEquiv d)

private noncomputable def blockedCoarseningMap
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d) × Fin (d * d))
        (Fin (d * d) × Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Matrix.equivReindexMap (blockedIndexEquiv d).symm ∘ₗ
    coarseningSquaredMap S ∘ₗ
      Matrix.equivReindexMap (blockedPairEquiv d)

/-- A tensor satisfying the trace-preserving completely positive map condition
of Definition 4.1 remains a renormalization fixed point after two neighboring
physical sites are blocked together. The new maps are the twice-applied
coarse-graining and refinement maps, transported through the canonical blocked
coordinates.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659, and the
twice-applied channel construction for Theorem 4.9 at lines 1810--1825. -/
theorem IsRFPViaTS.blockTwo {M : MPOTensor d D} (h : IsRFPViaTS M) :
    IsRFPViaTS (blockTwo M) := by
  obtain ⟨S, T, hS, hT, hSclose, hTclose⟩ := h
  refine ⟨blockedCoarseningMap S, blockedRefinementMap T, ?_, ?_, ?_, ?_⟩
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP (blockedPairEquiv d))
        (coarseningSquaredMap_isKrausCPTP hS))
      (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d).symm)
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d))
        (refinementSquaredMap_isKrausCPTP hT))
      (Matrix.equivReindexMap_isKrausCPTP (blockedPairEquiv d).symm)
  · intro X
    change Matrix.reindex (blockedIndexEquiv d).symm (blockedIndexEquiv d).symm
        (coarseningSquaredMap S
          (Matrix.reindex (blockedPairEquiv d) (blockedPairEquiv d)
            (physClose2 (MPOTensor.blockTwo M) X))) =
      physClose1 (MPOTensor.blockTwo M) X
    rw [show Matrix.reindex (blockedPairEquiv d) (blockedPairEquiv d)
        (physClose2 (MPOTensor.blockTwo M) X) = physClose4 M X by
      exact LinearMap.congr_fun (physClose2_blockTwo_eq_physClose4 M) X]
    rw [coarseningSquaredMap_physClose4 M S hSclose X]
    rw [← show Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
        (physClose1 (MPOTensor.blockTwo M) X) = physClose2 M X by
      exact LinearMap.congr_fun (physClose1_blockTwo_eq_physClose2 M) X]
    simp
  · intro X
    change Matrix.reindex (blockedPairEquiv d).symm (blockedPairEquiv d).symm
        (refinementSquaredMap T
          (Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
            (physClose1 (MPOTensor.blockTwo M) X))) =
      physClose2 (MPOTensor.blockTwo M) X
    rw [show Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
        (physClose1 (MPOTensor.blockTwo M) X) = physClose2 M X by
      exact LinearMap.congr_fun (physClose1_blockTwo_eq_physClose2 M) X]
    rw [refinementSquaredMap_physClose2 M T hTclose X]
    rw [← show Matrix.reindex (blockedPairEquiv d) (blockedPairEquiv d)
        (physClose2 (MPOTensor.blockTwo M) X) = physClose4 M X by
      exact LinearMap.congr_fun (physClose2_blockTwo_eq_physClose4 M) X]
    simp

end MPOTensor
