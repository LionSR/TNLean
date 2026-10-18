/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLength
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyExplicitThresholds

/-!
# Uniform lower bounds for nonprimary birth lengths

Initial belt lengths tend to infinity with their dyadic layer. A replacement
is created only when its removal half-side is at least the stopping scale.
Old identifiers retain their characteristic lengths. Consequently, for any
prescribed lower bound, a sufficiently large initial layer and stopping scale
give that bound for every identifier of positive birth rank at every stage.
The initial-layer threshold depends only on the prescribed lower bound `U`; it
is the explicit layer `fineScaleIndexThreshold U = ⌈dyadicIndexThreshold U / ζ⌉₊`.

This is an auxiliary for the choice of scanner thresholds. It applies to all
actual identifiers of positive birth rank, including those whose current
regions are empty. It requires no metric or termination assertion.
Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, nonterminal replacements,
lines 398–409; belt and replacement scales, lines 732–740; and the threshold
choice following `geometry:fine-clearance`, lines 761–771.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry


/-- **Explicit uniform lower bound for nonprimary lengths.** Every prescribed
real lower bound `U` holds for the remembered lengths of all positive-rank
identifiers once the initial layer is at least `fineScaleIndexThreshold U` and
the stopping scale is at least `U`. The usual formation assumptions of the
actual repair family are retained.
Source: area-law Section 11, `10-geometry.tex`, lines 398–409, 732–740
and 761–771. -/
theorem repairStage_positive_rank_length_lower_bound (U : ℝ) (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C)
    (h₀ : 50000000 ≤ k₀) (hk : fineScaleIndexThreshold U ≤ k₀) (Sstar : ℝ)
    (hSstar : U ≤ Sstar) (N : ℕ) (i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex)
    (hi : 0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i) :
    U ≤ repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N i := by
  induction N with
  | zero =>
    rcases i with u | (p | b)
    · exact (Nat.lt_irrefl 0 hi).elim
    · exact (Nat.lt_irrefl 0 hi).elim
    · exact le_two_pow_fineScaleIndex_of_fineScaleIndexThreshold_le
        (hk.trans b.1.property)
  | succ N ih =>
    rcases i with i | q
    · exact ih i hi
    · exact hSstar.trans q.2.1.property

/-- Every prescribed real lower bound holds uniformly for the remembered
lengths of all positive-rank identifiers once the initial layer and stopping
scale are sufficiently large. The threshold is chosen before all geometric
data, the stopping scale and the generation; it is `fineScaleIndexThreshold U`
(`repairStage_positive_rank_length_lower_bound`).
Source: area-law Section 11, `10-geometry.tex`, lines 398–409, 732–740
and 761–771. -/
theorem exists_uniform_repairStage_positive_rank_length_lower_bound (U : ℝ) :
    ∃ K : ℕ, ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
      (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
      ∀ Sstar : ℝ, U ≤ Sstar → ∀ (N : ℕ)
        (i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex),
        0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i →
        U ≤ repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N i :=
  ⟨fineScaleIndexThreshold U, repairStage_positive_rank_length_lower_bound U⟩

end TNLean.PEPS.AreaLaw.Geometry
