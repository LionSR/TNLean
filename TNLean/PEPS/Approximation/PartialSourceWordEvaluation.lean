/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePrivatePreparationEvaluation

/-! # Evaluation of the prepared source word

At each fixed choice of monomials, the prepared source word applies the actual
residual to the source vector tensored with the recorded private product vector.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139 and 246–267.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private theorem eval_comp_apply_eq {a b c : Layout P}
    (u : Word a b) (v : Word b c) (x : Mem a) (y : Mem b)
    (h : u.eval x = y) : (u.comp v).eval x = v.eval y :=
  congrArg v.eval h

/-- The actual pure-input source word applies the actual residual to the
source vector tensored with the original private product vector.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–267. -/
theorem eval_partialSourceWord_tmul {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a) (ξ : Choices (fun _ => true) w)
    (y : Mem w.allResidualSourceLayout) :
    (w.partialSourceWord ψ ξ).eval
      ((appendIso w.allResidualSourceLayout []).symm (y ⊗ₜ[ℂ] (1 : ℂ))) =
      (partialResidual (fun _ => true) w ξ).eval
        ((appendIso w.allResidualSourceLayout
          (Layout.mapOwner (affectedOwner (fun _ => true)) a)).symm
            (y ⊗ₜ[ℂ] Layout.mapOwnerIso (affectedOwner (fun _ => true)) a ψ.vector)) := by
  exact eval_comp_apply_eq (w.sourcePrivatePreparation ψ)
    (partialResidual (fun _ => true) w ξ) _ _ (eval_sourcePrivatePreparation_tmul w ψ y)

end TNLean.PEPS.PairEffect.SourceCircuit
