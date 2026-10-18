/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLength
import TNLean.PEPS.AreaLaw.Geometry.RepairDepth
import TNLean.PEPS.AreaLaw.Geometry.RepairNonprimaryRetainedCount
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The nonprimary error sum on retained identifiers

At every finite generation, the retained identifiers of positive birth rank
are the retained initial belts and replacements. Their prescribed scanner
scale is the natural ceiling of a positive coefficient times the remembered
characteristic length. These lengths are positive, so each scale is at least
one and each inverse hundredth-power error is at most one. The existing
uniform count therefore bounds their error sum.

The coefficient in the estimate may depend on the fixed stopping scale,
which exceeds one. It precedes the scanner coefficient, all geometric data,
the metric witness, and the generation. This is a finite-generation auxiliary;
it does not assert termination, template assignment, or clearance.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, belt and replacement scanner scales,
lines 732–740, and their error contribution, lines 796–798 of
`10-geometry.tex`. Characteristic primary lengths appear at lines 709–721.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every non-dummy actual identifier has positive characteristic length.
An initial primary has length `2^k`, a belt has length `2^(fineScaleIndex k)`,
and a replacement has its positive removal half-side. Retention preserves
these lengths. Source: area-law Section 11, lines 398–409, 709–721, and
732–740. -/
theorem repairStageCharacteristicLength_pos_of_ne_dummy
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)
    (N : ℕ) (i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex)
    (hi : i ≠ (repairStage o Λ A C k₀ hC h₀ Sstar N).dummy) :
    0 < repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N i := by
  classical
  induction N with
  | zero =>
    rcases i with u | (p | b)
    · exact (hi (congrArg Sum.inl (Subsingleton.elim u ()))).elim
    · exact pow_pos (by norm_num) _
    · exact pow_pos (by norm_num) _
  | succ N ih =>
    rcases i with i | q
    · exact ih i (fun h ↦ hi (congrArg Sum.inl h))
    · exact repairHalfSide_pos _

/-- **Nonprimary error sum with an explicit coefficient.** The prescribed errors on
actual retained positive-rank identifiers have boundary-weighted sum at most
`L_q (2 C₀ + 1) ^ 2 |∂A|` with `L_q = repairRetainedCountConstant S_*`, for every
positive scanner coefficient `C_B`, under the metric hypotheses.
Source: area-law Section 11, scanner scales, lines 732–740;
`geometry:total-repairs`, lines 685–692; and the nonprimary error
contribution, lines 796–798. -/
theorem repairStage_retained_positive_rank_error_sum_le {Sstar : ℝ} (hSstar : 1 < Sstar)
    {C_B : ℝ} (hC_B : 0 < C_B) (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ)
    (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
      (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀) (N : ℕ) :
    let I : Type :=
      {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A //
        0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val}
    let n : I → ℕ := fun i ↦
      ⌈C_B * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
        i.val.val⌉₊
    (∑ᶠ i : I, (((n i : ℝ) ^ 100)⁻¹)) ≤
      repairRetainedCountConstant Sstar * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  intro I n
  obtain ⟨hfinite, hbound⟩ :=
    repairStage_retained_positive_rank_le hSstar o Λ A C k₀ hC h₀ a₀ h N
  let : Fintype I := @Fintype.ofFinite I hfinite
  have hn (i : I) : 1 ≤ n i :=
    Nat.one_le_ceil_iff.mpr (mul_pos hC_B
      (repairStageCharacteristicLength_pos_of_ne_dummy o Λ A C k₀ hC h₀ Sstar N
        i.val.val i.val.property.1))
  rw [finsum_eq_sum_of_fintype]
  refine le_trans ?_ hbound
  have hweight (i : I) : ((n i : ℝ) ^ 100)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn i))
  simpa only [Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card] using
    (Finset.sum_le_card_nsmul Finset.univ (fun i : I ↦ ((n i : ℝ) ^ 100)⁻¹) 1
      (fun i _ ↦ hweight i))

/-- The prescribed errors on actual retained positive-rank identifiers have
a uniform boundary-weighted sum. The coefficient depends only on the fixed
stopping scale and is chosen before the positive scanner coefficient and
the geometric data. The metric hypotheses are exactly those of the retained
positive-rank count; the coefficient is `repairRetainedCountConstant S_*`
(`repairStage_retained_positive_rank_error_sum_le`). Source: area-law
Section 11, scanner scales, lines 732–740; `geometry:total-repairs`, lines
685–692; and the nonprimary error contribution, lines 796–798. -/
theorem exists_uniform_repairStage_retained_positive_rank_error_sum_bound
    {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (C_B : ℝ), 0 < C_B →
        ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
          (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
          RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
            (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
          ∀ N : ℕ,
            let I : Type :=
              {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A //
                0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val}
            let n : I → ℕ := fun i ↦
              ⌈C_B * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N
                i.val.val⌉₊
            (∑ᶠ i : I, (((n i : ℝ) ^ 100)⁻¹)) ≤
              L * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card :=
  ⟨_, repairRetainedCountConstant_pos Sstar, fun _ hC_B ↦
    repairStage_retained_positive_rank_error_sum_le hSstar hC_B⟩

end TNLean.PEPS.AreaLaw.Geometry
