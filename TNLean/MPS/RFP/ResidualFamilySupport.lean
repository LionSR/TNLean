/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace
import TNLean.MPS.RFP.AppendixBCommutation
import TNLean.MPS.RFP.ResidualWordSpan

/-!
# Two-site support of a residual-isometry family

This file constructs the common physical isometry carried by the valid
Sigma-indexed virtual pairs of a family of distinct normal sectors.  The index
space is
`BlockEntryIndex dim = Σ j, Fin (dim j) × Fin (dim j)`, not the full square
of the direct-sum bond space: cross-sector virtual pairs are absent from the
source isometry equation.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and `eq:III_isometry`, lines
543--555, and equations (3.16)--(3.18), lines 549--578.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The common one-site physical matrix of a residual-isometry family, indexed
only by valid within-sector virtual pairs.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
noncomputable def residualFamilyPhysicalIsometryMatrix
    (U : (j : Fin r) → MPSTensor d (dim j)) :
    Matrix (Fin d) (BlockEntryIndex dim) ℂ :=
  fun i x ↦ U x.1 i x.2.1 x.2.2

/-- The cross-sector residual-isometry equations say that the common physical
matrix is an isometry on `BlockEntryIndex dim`.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
theorem IsResidualIsometryFamily.residualFamilyPhysicalIsometryMatrix_isometry
    {U : (j : Fin r) → MPSTensor d (dim j)}
    (hU : IsResidualIsometryFamily U) :
    (residualFamilyPhysicalIsometryMatrix U)ᴴ *
        residualFamilyPhysicalIsometryMatrix U = 1 := by
  classical
  ext x y
  rcases x with ⟨j, a, b⟩
  rcases y with ⟨k, c, e⟩
  by_cases hjk : j = k
  · subst k
    simp only [residualFamilyPhysicalIsometryMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [show (∑ i : Fin d, star (U j i a b) * U j i c e) =
        ∑ i : Fin d, U j i c e * star (U j i a b) by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _]
    rw [hU.1 j c e a b]
    simp [eq_comm]
  · have hCross := hU.2 k j (Ne.symm hjk) c e a b
    simpa [residualFamilyPhysicalIsometryMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, hjk, mul_comm] using hCross

/-- Simultaneous Appendix B data for a finite family of sectors.  The fields
are precisely the sectorwise product-pair form and the common cross-sector
isometry equation; no cross-sector virtual matrix entries are introduced.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and `eq:III_isometry`, lines
543--555. -/
structure ResidualFamilyAppendixBData
    (B : (j : Fin r) → MPSTensor d (dim j)) where
  /-- Appendix B structural data for each normal sector. -/
  sector : (j : Fin r) → AppendixBStructuralData (B j)
  /-- The residual tensors of all sectors form the one common physical
  isometry in equation `eq:III_isometry`. -/
  residual : IsResidualIsometryFamily (fun j ↦ (sector j).U)

namespace ResidualFamilyAppendixBData

variable {B : (j : Fin r) → MPSTensor d (dim j)}

/-- The boundary-coordinate space for the equal-sector two-site basic
vectors.  It is the curried form of functions on `BlockEntryIndex dim`.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
abbrev TwoSiteBoundary (dim : Fin r → ℕ) :=
  (j : Fin r) → Fin (dim j) × Fin (dim j) → ℂ

/-- Insert the rank-one virtual bond separately in every sector and sum the
resulting two-site physical vectors.  Unequal-sector bonds are absent by
construction.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def twoSiteBondEmbedding
    (h : ResidualFamilyAppendixBData B) :
    TwoSiteBoundary dim →ₗ[ℂ] NSiteSpace d 2 where
  toFun v := ∑ j : Fin r, (h.sector j).twoSiteBasicEmbedding (v j)
  map_add' v w := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]
    exact Finset.smul_sum.symm

/-- The combined equal-sector bond insertion has range equal to the linear sum
of the sector two-site ground spaces.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and (3.17)--(3.18), lines
543--578. -/
theorem twoSiteBondEmbedding_range
    (h : ResidualFamilyAppendixBData B) :
    LinearMap.range h.twoSiteBondEmbedding =
      ⨆ j : Fin r, groundSpace (B j) 2 := by
  classical
  apply le_antisymm
  · rintro ψ ⟨v, rfl⟩
    change (∑ j : Fin r, (h.sector j).twoSiteBasicEmbedding (v j)) ∈
      ⨆ j : Fin r, groundSpace (B j) 2
    apply Submodule.sum_mem
    intro j _
    apply Submodule.mem_iSup_of_mem j
    rw [(h.sector j).groundSpace_eq_coreTensor]
    change (h.sector j).twoSiteBasicEmbedding (v j) ∈
      (h.sector j).twoSiteBasicSpace
    rw [← (h.sector j).twoSiteBasicEmbedding_range]
    exact ⟨v j, rfl⟩
  · refine iSup_le fun j ↦ ?_
    rintro ψ hψ
    rw [(h.sector j).groundSpace_eq_coreTensor] at hψ
    have hψ' : ψ ∈ (h.sector j).twoSiteBasicSpace := hψ
    rw [← (h.sector j).twoSiteBasicEmbedding_range] at hψ'
    obtain ⟨v, rfl⟩ := hψ'
    refine ⟨Pi.single j v, ?_⟩
    let f : Fin r → NSiteSpace d 2 := fun k ↦
      (h.sector k).twoSiteBasicEmbedding
        ((Pi.single j v : TwoSiteBoundary dim) k)
    change (∑ k : Fin r, f k) = (h.sector j).twoSiteBasicEmbedding v
    calc
      _ = f j := Finset.sum_eq_single j (fun k _ hkj ↦ by
        simp [f, Pi.single_eq_of_ne hkj]) (by simp)
      _ = _ := by simp [f]

/-- The equal-sector bond-insertion range is exactly the two-site local ground
space of the unit-weight direct sum.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and (3.17)--(3.18), lines
543--578. -/
theorem twoSiteBondEmbedding_range_eq_directSum_groundSpace
    (h : ResidualFamilyAppendixBData B) :
    LinearMap.range h.twoSiteBondEmbedding =
      groundSpace (directSumTensor B) 2 := by
  rw [h.twoSiteBondEmbedding_range]
  have hTensor :
      toTensorFromBlocks (d := d) (fun _ : Fin r ↦ 1) B = directSumTensor B := by
    funext i
    simp [toTensorFromBlocks, directSumTensor]
  rw [← hTensor]
  exact (groundSpace_toTensorFromBlocks_eq_iSup
    (fun _ : Fin r ↦ 1) B (by simp) 2).symm

/-- The orthogonal projector onto the physical image of the equal-sector bond
insertion.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578, and the
parent-space construction, lines 511--524. -/
noncomputable def twoSiteBondSupportProjection
    (_h : ResidualFamilyAppendixBData B) :
    NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2 :=
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)
  e.toLinearMap.comp
    (((groundSpaceES (directSumTensor B) 2).starProjection.toLinearMap).comp
      e.symm.toLinearMap)

/-- The physical equal-sector bond projector has exactly the combined
bond-insertion range.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and (3.17)--(3.18), lines
543--578. -/
theorem twoSiteBondSupportProjection_range
    (h : ResidualFamilyAppendixBData B) :
    LinearMap.range h.twoSiteBondSupportProjection =
      LinearMap.range h.twoSiteBondEmbedding := by
  rw [h.twoSiteBondEmbedding_range_eq_directSum_groundSpace]
  ext ψ
  constructor
  · rintro ⟨v, rfl⟩
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES (directSumTensor B) 2).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v)) ∈
          groundSpace (directSumTensor B) 2
    apply (mem_groundSpaceES_iff (directSumTensor B) 2 _).1
    exact Submodule.starProjection_apply_mem _ _
  · intro hψ
    refine ⟨ψ, ?_⟩
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES (directSumTensor B) 2).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ)) = ψ
    have hψES : (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ ∈
        groundSpaceES (directSumTensor B) 2 := by
      apply (mem_groundSpaceES_iff (directSumTensor B) 2 _).2
      simpa using hψ
    rw [Submodule.starProjection_eq_self_iff.mpr hψES,
      LinearEquiv.apply_symm_apply]

/-- The physical transport target of the residual-family bond projector is
the canonical two-site support projector of the direct-sum tensor.

Source: arXiv:1606.00608, parent construction, lines 511--524, and equations
(3.16)--(3.18), lines 549--578. -/
theorem twoSiteBondSupportProjection_eq_complement
    (h : ResidualFamilyAppendixBData B) :
    h.twoSiteBondSupportProjection =
      1 - parentInteraction (directSumTensor B) 2 := by
  apply LinearMap.ext
  intro v
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES (directSumTensor B) 2).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v)) =
    v - (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES (directSumTensor B) 2)ᗮ.starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v))
  rw [Submodule.starProjection_orthogonal_val]
  simp

end ResidualFamilyAppendixBData

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- Whole-direct-sum transfer idempotence supplies simultaneous Appendix B
data on the faithful Sigma-indexed residual-pair space.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and `eq:III_isometry`, lines
543--555, and Corollary `III.cor3`, lines 583--589. -/
theorem exists_residualFamilyAppendixBData
    (hCF : IsBNTCanonicalForm P)
    (hRFP : IsTransferIdempotent (directSumTensor P.basis)) :
    Nonempty (ResidualFamilyAppendixBData P.basis) := by
  obtain ⟨X, Λ, U, hX, hΛ, _hTrace, hBasis, hU⟩ :=
    hCF.exists_residualIsometryFamily_of_isTransferIdempotent_basisDirectSum hRFP
  let sector : (j : Fin P.basisCount) →
      AppendixBStructuralData (P.basis j) := fun j ↦
    { X := X j
      Λ := fun k ↦ Real.sqrt (Λ j k)
      U := U j
      hX_det := hX j
      hΛ_pos := fun k ↦ Real.sqrt_pos.2 (hΛ j k)
      hU_pair := by
        intro p q
        rw [show (∑ i : Fin d, star (U j i p.1 p.2) * U j i q.1 q.2) =
            ∑ i : Fin d, U j i q.1 q.2 * star (U j i p.1 p.2) by
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _]
        rw [hU.1 j q.1 q.2 p.1 p.2]
        by_cases hpq : p = q
        · subst q
          simp
        · have hne : ¬ (q.1 = p.1 ∧ q.2 = p.2) := by
            intro h
            exact hpq (Prod.ext h.1.symm h.2.symm)
          simp [hpq, hne]
      hA_eq := hBasis j }
  exact ⟨{ sector := sector, residual := hU }⟩

end IsBNTCanonicalForm

end MPSTensor
