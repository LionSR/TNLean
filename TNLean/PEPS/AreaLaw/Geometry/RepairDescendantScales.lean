/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Function.Iterate
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# Exact scales along repair ancestry

The scale of an actual descendant is the iterate of the removal half-side
map applied to its recorded ancestor's scale. This identifies the scales in
the actual repair family with those used by the numerical depth estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, child scales, lines 404–409; and
`geometry:descendant-count`, lines 670–681.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Every actual descendant scale is the iterate of the removal half-side
map applied to its recorded ancestor's scale.
Source: area-law Section 11, lines 404–409 and `geometry:descendant-count`,
lines 670–681. -/
theorem repairStage_scale_eq_iterate (i n : ℕ) (q : (𝔇 (i + n)).markIndex) :
    (𝔇 (i + n)).scale q = (repairHalfSide^[n])
      ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q)) := by
  exact Nat.rec
    (motive := fun n ↦ ∀ q : (𝔇 (i + n)).markIndex,
      (𝔇 (i + n)).scale q = (repairHalfSide^[n])
        ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q)))
    (fun _ ↦ rfl)
    (fun n ih q ↦
      (repairStage_scale_succ o Λ A C k₀ hC h₀ Sstar (i + n) q).trans
        ((congrArg repairHalfSide
          (ih (repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q))).trans
          (Function.iterate_succ_apply' repairHalfSide n
            ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n
              (repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q)))).symm)) n q

end TNLean.PEPS.AreaLaw.Geometry
