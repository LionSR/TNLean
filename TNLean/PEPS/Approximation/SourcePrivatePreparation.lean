/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceLocalMaps

/-! # Incident choices in the actual chronological expansion

These results concern actual gate occurrences and their selected monomial labels.
Source: polynomial-PEPS, `04-compression.tex`, lines 351–381.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace Word
/-- A framed word acts on the second factor of an actual memory tensor.
Source: polynomial-PEPS 04-compression.tex, lines 246–251. -/
theorem eval_frameList_tmul {a b : Layout P} (w : Word a b)
    (rs : Layout P) (x : Mem rs) (y : Mem a) :
    (Word.frameList rs w).eval ((appendIso rs a).symm (x ⊗ₜ[ℂ] y)) =
      (appendIso rs b).symm (x ⊗ₜ[ℂ] w.eval y) := by
  induction rs with
  | nil => exact map_smul w.eval x y
  | cons r rs ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z => u ⊗ₜ[ℂ] z) (ih v)
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
end Word
namespace SourceCircuit
/-- The literal private preparation inserts the original private product
vector, leaving all actual source registers arbitrary.
Source: polynomial-PEPS 04-compression.tex, lines 137–139 and 246–267. -/
theorem eval_sourcePrivatePreparation_tmul {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a) (y : Mem w.allResidualSourceLayout) :
    (w.sourcePrivatePreparation ψ).eval
      ((appendIso w.allResidualSourceLayout []).symm (y ⊗ₜ[ℂ] (1 : ℂ))) =
      (appendIso w.allResidualSourceLayout (Layout.mapOwner (affectedOwner (fun _ => true)) a)).symm
        (y ⊗ₜ[ℂ] Layout.mapOwnerIso (affectedOwner (fun _ => true)) a ψ.vector) := by
  rw [sourcePrivatePreparation, Word.eval_frameList_tmul]
  exact congrArg (fun z =>
    (appendIso w.allResidualSourceLayout
      (Layout.mapOwner (affectedOwner (fun _ => true)) a)).symm (y ⊗ₜ[ℂ] z))
        ((Word.eval_mapOwner (affectedOwner (fun _ => true)) ψ.prepare (1 : ℂ)).trans
          (congrArg (Layout.mapOwnerIso (affectedOwner (fun _ => true)) a) ψ.eval_prepare))

set_option maxHeartbeats 800000 in
-- The actual fixed-source word carries dependent source and owner transports.
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
  change (partialResidual (fun _ => true) w ξ).eval
    ((w.sourcePrivatePreparation ψ).eval _) = _
  rw [eval_sourcePrivatePreparation_tmul]

end SourceCircuit
end TNLean.PEPS.PairEffect
