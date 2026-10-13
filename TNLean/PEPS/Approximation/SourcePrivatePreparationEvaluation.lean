/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePrivatePreparation

/-! # Evaluation of the original private preparation

The original private preparation inserts the recorded product vector while
leaving an arbitrary vector on the source registers unchanged.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139 and 246–267.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The literal private preparation inserts the original private product
vector, leaving all actual source registers arbitrary.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–267. -/
theorem eval_sourcePrivatePreparation_tmul {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a) (y : Mem w.allResidualSourceLayout) :
    (w.sourcePrivatePreparation ψ).eval
      ((appendIso w.allResidualSourceLayout []).symm (y ⊗ₜ[ℂ] (1 : ℂ))) =
      (appendIso w.allResidualSourceLayout (Layout.mapOwner (affectedOwner (fun _ => true)) a)).symm
        (y ⊗ₜ[ℂ] Layout.mapOwnerIso (affectedOwner (fun _ => true)) a ψ.vector) := by
  unfold sourcePrivatePreparation
  rw [Word.eval_frameList_appendIso_symm]
  exact congrArg (fun z =>
    (appendIso w.allResidualSourceLayout
      (Layout.mapOwner (affectedOwner (fun _ => true)) a)).symm (y ⊗ₜ[ℂ] z))
        ((Word.eval_mapOwner (affectedOwner (fun _ => true)) ψ.prepare (1 : ℂ)).trans
          (congrArg (Layout.mapOwnerIso (affectedOwner (fun _ => true)) a) ψ.eval_prepare))

end TNLean.PEPS.PairEffect.SourceCircuit
