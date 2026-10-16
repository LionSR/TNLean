/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedPrimaryErrorSum
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedNonprimaryErrorSum

/-!
# The prescribed error sum on the retained repair family

For fixed primary coefficient and stopping scale, the inverse hundredth
powers of the prescribed scanner scales have a uniform boundary-weighted
sum on the entire actual retained family. The scale is the primary ceiling
on identifiers of birth rank zero and the belt or replacement ceiling on
identifiers of positive rank. The bound follows by adding the two separate
estimates. Finiteness follows from the actual retained-family construction.

The resulting coefficient is chosen before the belt coefficient, all
geometric data, the metric witness and the generation. This is a
finite-generation auxiliary for the final numerical estimate in the
ordered two-family decomposition. It makes no template, clearance or
termination assertion.
Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, prescribed scanner scales,
lines 709–740, and the two error contributions, lines 777–798.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The literal prescribed scales on the actual retained family have a
uniform boundary-weighted error sum. The coefficient depends only on the
fixed positive primary coefficient and stopping scale greater than one;
it precedes every positive belt coefficient and all geometric data.
The metric assumptions are exactly those of the nonprimary contribution.
Source: area-law Section 11, `geometry:primary-scale`, lines 709–740,
and the final error sums in the proof of `prop:two-families`, lines 777–798. -/
theorem exists_uniform_repairStage_retained_error_sum_bound
    {C_P Sstar : ℝ} (hC_P : 0 < C_P) (hSstar : 1 < Sstar) :
    ∃ E : ℝ, 0 < E ∧
      ∀ (C_B : ℝ), 0 < C_B →
        ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
          (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
          RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
            (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
          ∀ N : ℕ,
            let I : Type :=
              (repairStage o Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A
            let n : I → ℕ := fun i ↦
              if repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val = 0 then
                ⌈C_P * (repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
                  i.val) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊
              else
                ⌈C_B * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
                  i.val⌉₊
            (∑ᶠ i : I, (((n i : ℝ) ^ 100)⁻¹)) ≤
              E * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  obtain ⟨M, hM, hprimary⟩ :=
    exists_uniform_repairStage_retained_rank_zero_error_sum_bound hC_P
  obtain ⟨L, hL, hnonprimary⟩ :=
    exists_uniform_repairStage_retained_positive_rank_error_sum_bound hSstar
  refine ⟨M + L, add_pos hM hL, ?_⟩
  intro C_B hC_B o Λ A C k₀ hC h₀ a₀ h N I n
  let : Finite I :=
    (finite_and_card_repairStage_retainedRegionIndex_le o Λ A C k₀ hC h₀ Sstar N).1
  let : Fintype I := Fintype.ofFinite I
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype
    (fun i : I ↦ repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val = 0)]
  have hp (i : {i : I // repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val = 0}) :
      n i.val = ⌈C_P * (repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
        i.val.val) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ :=
    ite_eq_left i.property
  have hb (i : {i : I // ¬ repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val = 0}) :
      n i.val = ⌈C_B * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
        i.val.val⌉₊ :=
    ite_eq_right i.property
  let e : {i : I // ¬ repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val = 0} ≃
      {i : I // 0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val} :=
    Equiv.subtypeEquivRight (fun _ ↦ Nat.pos_iff_ne_zero.symm)
  have hsum := finsum_comp_equiv e (f := fun i ↦
    ((((⌈C_B * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
      i.val.val⌉₊ : ℕ) : ℝ) ^ 100)⁻¹))
  simpa only [finsum_eq_sum_of_fintype, hp, hb, e, Equiv.subtypeEquivRight_apply, add_mul] using
    add_le_add (hprimary o Λ A C k₀ hC h₀ Sstar N)
      (hsum.le.trans (hnonprimary C_B hC_B o Λ A C k₀ hC h₀ a₀ h N))

end TNLean.PEPS.AreaLaw.Geometry
