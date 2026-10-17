/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairRankZeroAncestry
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedPrefixCount
import TNLean.PEPS.AreaLaw.Geometry.InitialPrimaryErrorSum
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The primary error sum on retained identifiers

At every finite generation, the actual retained identifiers of birth rank
zero have a uniform boundary-weighted error sum for their prescribed scanner
scales. The scale uses the remembered characteristic birth length and the
literal natural ceiling; the error is the inverse natural hundredth power.
The coefficient precedes the geometric data and the generation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:primary-scale`, lines 709–729,
and the retained primary error sum, lines 777–795 of `10-geometry.tex`.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is a finite-generation auxiliary; it makes no template assignment,
clearance, termination, or finiteness assertion about all initial primaries.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The inverse hundredth powers of the prescribed scanner scales on the
actual retained rank-zero identifiers have a uniform boundary-weighted sum.
The coefficient is chosen before the geometric data, stopping scale, and
number of generations. This is the finite-generation primary contribution.
Source: area-law Section 11, `geometry:primary-scale`, lines 709–729,
and the retained primary error sum, lines 777–795. -/
theorem exists_uniform_repairStage_retained_rank_zero_error_sum_bound
    {C_P : ℝ} (hC_P : 0 < C_P) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
        (Sstar : ℝ) (N : ℕ),
        let I : Type :=
          {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A //
            repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val = 0}
        let n : I → ℕ := fun i ↦
          ⌈C_P * (repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
            i.val.val) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊
        (∑ᶠ i : I, (((n i : ℝ) ^ 100)⁻¹)) ≤
          M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  obtain ⟨M, hM, hbound⟩ := exists_uniform_primaryPitchIndices_error_sum_bound hC_P
  refine ⟨M, hM, fun o Λ A C k₀ hC h₀ Sstar N ↦ ?_⟩
  obtain ⟨N, rfl⟩ : ∃ m, N = 0 + m := ⟨N, (Nat.zero_add N).symm⟩
  intro I n
  choose p hp using fun i : I ↦
    (existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero
      o Λ A C k₀ hC h₀ Sstar N i.val.val i.property i.val.property.1).exists
  let e : I → Σ _ : ℕ, ℤ × ℤ := fun i ↦ ⟨(p i).1.val, (p i).2.val⟩
  have he : Function.Injective e := by
    intro i j hij
    have hpp : p i = p j :=
      Sigma.subtype_ext (Subtype.ext (congrArg Sigma.fst hij))
        (congrArg (fun q : Σ _ : ℕ, ℤ × ℤ ↦ q.2) hij)
    exact Subtype.ext (Subtype.ext ((hp i).symm.trans
      ((congrArg (fun q ↦ repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar
        0 N (.inr (.inl q))) hpp).trans (hp j))))
  have hlen (i : I) :
      repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + N) i.val.val =
        (2 : ℝ) ^ (e i).1 :=
    (congrArg (repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + N))
      (hp i).symm).trans
        (repairStageCharacteristicLength_oldInclusion o Λ A C k₀ hC h₀ Sstar
          0 N (.inr (.inl (p i))))
  let : Finite ((repairStage o Λ A C k₀ hC h₀ Sstar (0 + N)).RetainedRegionIndex Λ A) :=
    (finite_and_card_repairStage_retainedRegionIndex_le o Λ A C k₀ hC h₀ Sstar
      (0 + N)).1
  let : Fintype I := Fintype.ofFinite I
  rw [finsum_eq_sum_of_fintype]
  let hchoice := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let a := Classical.choose hchoice
  let b := Classical.choose (Classical.choose_spec hchoice)
  let G (k : ℕ) := primaryPitchIndices o k (fineScaleIndex k) (pitchScaleIndex k)
    (boundaryEndpoints Λ A) C (a k).val (b k).val
  let K : Finset ℕ := Finset.univ.image (fun i : I ↦ (e i).1)
  let w (k : ℕ) : ℝ :=
    (((⌈C_P * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ : ℕ) : ℝ)
      ^ 100)⁻¹
  have hsum : (∑ i : I, (((n i : ℝ) ^ 100)⁻¹)) ≤
      ∑ q ∈ K.sigma G, w q.1 := by
    refine Finset.sum_le_sum_of_injOn e he.injOn ?_ ?_ ?_
    · exact Finset.image_subset_iff.mpr (fun i _ ↦ Finset.mem_sigma.mpr
        ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, (p i).2.property⟩)
    · exact fun i _ ↦ by simp only [n, hlen, w, le_refl]
    · exact fun q _ _ ↦ inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  refine hsum.trans ?_
  simpa only [Finset.sum_sigma, Finset.sum_const, nsmul_eq_mul] using
    hbound o Λ A C (fun k ↦ (a k).val) (fun k ↦ (b k).val) K

end TNLean.PEPS.AreaLaw.Geometry
