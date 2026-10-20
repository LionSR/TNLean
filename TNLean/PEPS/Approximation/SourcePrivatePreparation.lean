/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceRegisters
import TNLean.Lattice.PartyCircuit.EffectCircuitPreparation
import TNLean.PEPS.Approximation.SourceResidualCoordinates
import TNLean.Lattice.PartyCircuit.SiteRegisters

/-! # Preparation of the original private product input

The recorded private preparation acts on the private registers while leaving
every fixed source register untouched. Thus it sends `y ⊗ 1` to `y ⊗ ψ` for
an arbitrary source vector `y`. Composing with the actual residual gives the
source-to-output word at each choice of monomials.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139 and 246–267.
-/

noncomputable section
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

end TNLean.PEPS.PairEffect.SourceCircuit
