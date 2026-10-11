/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceRegisters
import TNLean.PEPS.Approximation.EffectCircuitPreparation
import TNLean.PEPS.Approximation.SourceResidualCoordinates
import TNLean.PEPS.Approximation.SiteRegisters

/-! # Preparation of the original private product input

The recorded private preparation acts on the private registers while leaving
every fixed source register untouched. Thus it sends `y ⊗ 1` to `y ⊗ ψ` for
an arbitrary source vector `y`. Composing with the actual residual gives the
source-to-output word at each choice of monomials.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139 and 246–267.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Prepare the original private product input, leaving the fixed source
registers as arbitrary spectators. Source: polynomial-PEPS 04-compression.tex,
lines 137–139 and 253–267. -/
def sourcePrivatePreparation {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a) :
    Word (w.allResidualSourceLayout ++ [])
      (w.allResidualSourceLayout ++ Layout.mapOwner (affectedOwner (fun _ => true)) a) :=
  Word.frameList w.allResidualSourceLayout
    (ψ.prepare.mapOwner (affectedOwner (fun _ => true)))

/-- The original private preparation introduces no pair source.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem sources_sourcePrivatePreparation {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a) :
    (w.sourcePrivatePreparation ψ).sources = [] :=
  (Word.sources_frameList _ _).trans <|
    (Word.sources_mapOwner _ _).trans <|
      (congrArg (SourceInventory.mapOwner _) ψ.sources_prepare).trans
        (SourceInventory.mapOwner_nil _)

/-- The actual source-free composition after the recorded private input has
been prepared. Source: polynomial-PEPS 04-compression.tex, lines 137–139,
246–251 and 351–381. -/
def partialSourceWord {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ : Choices (fun _ => true) w) :
    Word (w.allResidualSourceLayout ++ [])
      (Layout.mapOwner (affectedOwner (fun _ => true)) b) :=
  .comp (w.sourcePrivatePreparation ψ) (partialResidual (fun _ => true) w ξ)

/-- The actual pure-input residual contains no source preparations.
Source: polynomial-PEPS 04-compression.tex, lines 246–251. -/
theorem sources_partialSourceWord {a b : Layout P} (w : SourceCircuit a b)
    (ψ : ProductInput a) (ξ : Choices (fun _ => true) w) :
    (w.partialSourceWord ψ ξ).sources = [] := by
  exact (congrArg₂ (fun S T : SourceInventory _ => S ++ T)
    (sources_partialResidual _ _ _) (sources_sourcePrivatePreparation w ψ)).trans rfl

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
  rw [partialSourceWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
  exact congrArg (partialResidual (fun _ => true) w ξ).eval
    (eval_sourcePrivatePreparation_tmul w ψ y)

end TNLean.PEPS.PairEffect.SourceCircuit
