/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceLocalMaps

/-! # Preparation of the original private product input

The private input is prepared while every source register remains free. The
resulting source-to-output word applies the chronological residual to the
arbitrary source vector tensored with that original private input.
Source: polynomial-PEPS, `04-compression.tex`, lines 137–139 and 246–267.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-sourceprivatepreparation-01
TNLean.PEPS.PairEffect.SourceCircuit.eval_partialSourceWord_tmul
Provenance-ID: 8769-chronological-network-sourceprivatepreparation-02
TNLean.PEPS.PairEffect.SourceCircuit.eval_sourcePrivatePreparation_tmul
-/


noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}
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
