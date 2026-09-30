/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.RefinementNormalization
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward

/-!
# Normalizing the explicit periodic refinement input

Physical isometries preserve the multiplicity data of an explicit sector
presentation and reflect repeated-block relations. Thus the refinement witness
of a unit-weight periodic block form supplies the hypotheses of the arbitrary
normalization theorem. The resulting refining block family has unit weights and
the original total bond dimension, as in arXiv:1708.00029, Theorem 4.1,
lines 735–756. The global orbit-phase matching remains a subsequent step.

**Local fix (trace preservation):** The refinement theorem below requires the
input multiplicities to equal one, so its transfer map is trace preserving.
This corrects the printed forward implication of Theorem 4.1 as recorded in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Repetition after a common isometric physical mixing implies repetition of the
original tensors. The conjugate mixing recovers their original letters.
Source: arXiv:1708.00029, Theorem 4.1, lines 735–743, preservation of the
irreducible block presentation under the physical isometry. -/
theorem hetRepeatedBlocks_of_kraus_isometry {d m D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (h : HetRepeatedBlocks (fun t ↦ ∑ i, W t i • A i) (fun t ↦ ∑ i, W t i • B i)) :
    HetRepeatedBlocks A B := by
  obtain ⟨hd, z, X, hz, hrel⟩ := h
  subst E
  refine ⟨rfl, z, X, hz, fun i ↦ ?_⟩
  change A i = _
  rw [← sum_star_smul_sum_smul_of_isometry A W hW i, ← sum_star_smul_sum_smul_of_isometry B W hW i]
  simp_rw [show ∀ t, (∑ j, W t j • A j) =
      z • ((X : Matrix (Fin D) (Fin D) ℂ) * (∑ j, W t j • B j) *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) from hrel]
  simp only [Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, mul_left_comm]

variable {d m : ℕ}

/-- Apply a physical linear map to each representative, retaining the multiplicities
and bond coordinates. Source: arXiv:1708.00029, Theorem 4.1, lines 735–743. -/
noncomputable def SectorDecomposition.mapPhysical (P : SectorDecomposition d)
    (W : Matrix (Fin m) (Fin d) ℂ) : SectorDecomposition m where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := fun j t ↦ ∑ i, W t i • P.basis j i
  sectors := P.sectors

/-- Physical mixing of a sector decomposition agrees letterwise with mixing its
assembled tensor. Source: arXiv:1708.00029, Theorem 4.1, lines 735–743. -/
theorem SectorDecomposition.mapPhysical_toTensor (P : SectorDecomposition d)
    (W : Matrix (Fin m) (Fin d) ℂ) (t : Fin m) :
    (SectorDecomposition.mapPhysical P W).toTensor t = ∑ i, W t i • P.toTensor i := by
  exact toTensorFromBlocks_sum_smul P.flatWeight P.flatBasis W t

/-- An isometric physical map preserves the transfer map of the assembled
sector decomposition. Source: arXiv:1708.00029, Theorem 4.1, lines 735–743. -/
theorem SectorDecomposition.transferMap_mapPhysical (P : SectorDecomposition d)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    Kraus.transferMap (P.mapPhysical W).toTensor = Kraus.transferMap P.toTensor := by
  have he : (P.mapPhysical W).toTensor = fun t ↦ ∑ i, W t i • P.toTensor i :=
    funext (P.mapPhysical_toTensor W)
  rw [he]
  exact transferMap_kraus_isometry P.toTensor W hW

/-- A refinement of an explicit unit-weight periodic block form admits a periodic
unit-weight block presentation of the refining tensor, with the original total
bond dimension. The same physical isometry identifies its blocked MPVs with the
mixed target. This is the normalization of arXiv:1708.00029, Theorem 4.1,
lines 735–756, before the equal-case phase correction and final root construction.
The unit-weight input is the correction recorded in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem exists_unitWeight_periodic_blocks_of_isPRefinable (P : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hweight : ∀ j q, P.weight j q = 1) {p : ℕ} (hp : 0 < p)
    (hRefine : IsPRefinable P.toTensor p) :
    ∃ (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ), Wᴴ * W = 1 ∧
      ∃ (r : ℕ) (dim : Fin r → ℕ) (A : (k : Fin r) → MPSTensor d (dim k))
        (period : Fin r → ℕ),
        (∀ k, IsPeriodic (period k) (A k)) ∧ (∑ k, dim k) = P.totalDim ∧
        SameMPV₂Pos (blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p)
          (SectorDecomposition.mapPhysical P W).toTensor := by
  obtain ⟨A, W, hW, _, hSame⟩ := pRefinementCanonicalization_pullback P.toTensor p hRefine
  let Q := SectorDecomposition.mapPhysical P W
  have hQper (j) : IsPeriodic (periodP j) (Q.basis j) :=
    isPeriodic_kraus_isometry (P.basis j) W hW (hPerP j)
  have hQnonrep : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j) := by
    intro i j hij h
    exact hNonRepP i j hij (hetRepeatedBlocks_of_kraus_isometry (P.basis i) (P.basis j) W hW h)
  have hQweight (j : Fin P.basisCount) (q : Fin (P.copies j)) : ‖Q.weight j q‖ = 1 := by
    change ‖P.weight j q‖ = 1
    rw [hweight, norm_one]
  have hAQ : SameMPV₂Pos (blockTensor A p) Q.toTensor := by
    intro N _ σ
    have he : Q.toTensor = fun t ↦ ∑ i, W t i • P.toTensor i :=
      funext (SectorDecomposition.mapPhysical_toTensor P W)
    rw [he]
    exact (hSame N σ).symm
  obtain ⟨r, dim, B, period, hper, hdim, _, hAB⟩ :=
    exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos
      A hp Q periodP hQper hQnonrep hAQ hQweight
  exact ⟨W, hW, r, dim, B, period, hper, hdim,
    (sameMPV₂Pos_blockTensor A (toTensorFromBlocks (fun _ ↦ 1) B) hAB p hp).symm.trans hAQ⟩

end MPSTensor
