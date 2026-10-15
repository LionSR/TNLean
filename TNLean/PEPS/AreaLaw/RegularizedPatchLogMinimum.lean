/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithm of the regularized patch minimum

The positive minimum of the original filtered norm is also an attained minimum
after taking logarithms. Both attainment and the comparison with every feasible
density tuple follow from the established norm minimum. No new positivity
assumption or choice of minimizers is imposed.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 425–481, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This result does not establish the derivative or growth of that minimum.
-/

open Set Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

/-- Taking the logarithm preserves the attained norm minimum of the original
ordered regional filters. Source: OpenAI `03-patches.tex`, lines 425–451. -/
theorem isLeast_log_regularizedPatchObjective (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1) :
    IsLeast ((fun x ↦ Real.log (regularizedPatchObjective regions a b Ω x)) ''
      regularizedPatchDomain regions) (Real.log (regularizedPatchMinimum regions a b Ω)) :=
  match exists_isMinOn_regularizedPatchObjective regions a hb Ω hΩ with
  | ⟨x, hx, hmin⟩ =>
    ⟨⟨x, hx, congrArg Real.log (regularizedPatchObjective_eq_minimum regions a b Ω hx hmin)⟩,
      fun _ hy ↦
        match hy with
        | ⟨y, hy, heq⟩ =>
          (Real.log_le_log (regularizedPatchMinimum_pos regions a ha hb Ω hΩ)
            (calc
              regularizedPatchMinimum regions a b Ω = regularizedPatchObjective regions a b Ω x :=
                (regularizedPatchObjective_eq_minimum regions a b Ω hx hmin).symm
              _ ≤ regularizedPatchObjective regions a b Ω y := hmin hy)).trans_eq heq⟩

end TNLean.PEPS
