/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualPartialPartyFactorization

/-! # Incident choices in the actual chronological expansion

These results concern actual gate occurrences and their selected monomial labels.
Source: polynomial-PEPS, `04-compression.tex`, lines 351–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-01
TNLean.PEPS.PairEffect.SourceCircuit.allResidualSourceLayout
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-02
https://lionsr.github.io/TNLean/docs/TNLean/PEPS/Approximation/ActualSourceLocalMaps.html#TNLean.PEPS.PairEffect.SourceCircuit.groupByPartyIso_partialSourceWord_eq_tensorPartialSourceLocalMaps
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-03
TNLean.PEPS.PairEffect.SourceCircuit.partialSourceLocalMap
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-04
TNLean.PEPS.PairEffect.SourceCircuit.partialSourceWord
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-05
TNLean.PEPS.PairEffect.SourceCircuit.restrict_partialSourceWord_eq_partialSourceLocalMap
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-06
TNLean.PEPS.PairEffect.SourceCircuit.sourcePrivatePreparation
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-07
TNLean.PEPS.PairEffect.SourceCircuit.sources_partialSourceWord
Provenance-ID: 8769-chronological-network-actualsourcelocalmaps-08
TNLean.PEPS.PairEffect.SourceCircuit.sources_sourcePrivatePreparation
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The actual fixed registers supplied by the all-party source preparation.
Source: polynomial-PEPS 04-compression.tex, lines 253–267 and 409–434. -/
abbrev allResidualSourceLayout {a b : Layout P} (w : SourceCircuit a b) :
    Layout (Option {p : P // (fun _ : P => true) p = true}) :=
  SourceInventory.slotLayout (partialSlots (fun _ => true) w)
    (fun i => euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).1))
    (fun i => euc (Fin (sourceDims w (partialSlotEquiv (fun _ => true) w i).1).2))

/-- Prepare the original private product input, leaving the fixed source
registers as arbitrary spectators. Source: polynomial-PEPS 04-compression.tex,
lines 137–139 and 253–267. -/
def sourcePrivatePreparation {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a) :
    Word (w.allResidualSourceLayout ++ []) w.allResidualInput :=
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

/-- The actual source-free chronology after the recorded private input has
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

/-- The actual local source-to-output map, with the original private input
prepared by its recorded local word. It depends only on incident gate choices.
Source: polynomial-PEPS 04-compression.tex, lines 137–139, 351–381 and 565–588. -/
def partialSourceLocalMap {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (η : Choices (fun p => f (affectedOwner (fun _ => true) p)) w) :
    Mem (Layout.restrict f (w.allResidualSourceLayout ++ [])) →L[ℂ]
      Mem (Layout.restrict f (Layout.mapOwner (affectedOwner (fun _ => true)) b)) :=
  w.partialLocalRemainingMap f η ∘L
    ((w.sourcePrivatePreparation ψ).restrict f (sources_sourcePrivatePreparation w ψ)).eval

set_option maxHeartbeats 800000 in
-- The actual source and private-preparation maps carry dependent layout transports.
/-- Restricting the actual pure-input residual gives its constructed local map
at the actual incident choices. Source: polynomial-PEPS 04-compression.tex,
lines 137–139, 351–381 and 565–588. -/
theorem restrict_partialSourceWord_eq_partialSourceLocalMap {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (ξ : Choices (fun _ => true) w) :
    ((w.partialSourceWord ψ ξ).restrict f (sources_partialSourceWord w ψ ξ)).eval =
      w.partialSourceLocalMap ψ f
        (projectAllChoices (fun p => f (affectedOwner (fun _ => true) p)) w ξ) := by
  exact congrArg (fun A => A ∘L
    ((w.sourcePrivatePreparation ψ).restrict f (sources_sourcePrivatePreparation w ψ)).eval)
      (restrict_partialResidual_eq_partialLocalRemainingMap w f ξ)

set_option maxHeartbeats 800000 in
-- The canonical grouping expands the actual fixed source and private layouts.
/-- The recorded local source-to-output maps factor the actual pure-input
chronology. The auxiliary owner `none` remains an explicit scalar factor.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–588. -/
theorem groupByPartyIso_partialSourceWord_eq_tensorPartialSourceLocalMaps
    {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ : Choices (fun _ => true) w)
    (ps : List (Option {p : P // (fun _ : P => true) p = true}))
    (hn : ps.Nodup) (hP : ∀ q, q ∈ ps) :
    isoL (groupByPartyIso ps (Layout.mapOwner (affectedOwner (fun _ => true)) b) hn
      (fun r _ => hP r.owner)) ∘L (w.partialSourceWord ψ ξ).eval =
      tensorPartyMaps (w.allResidualSourceLayout ++ [])
        (Layout.mapOwner (affectedOwner (fun _ => true)) b)
        (fun q => w.partialSourceLocalMap ψ (partySelector q)
          (projectAllChoices
            (fun p => partySelector q (affectedOwner (fun _ => true) p)) w ξ)) ps ∘L
        isoL (groupByPartyIso ps (w.allResidualSourceLayout ++ []) hn (fun r _ => hP r.owner)) := by
  simpa only [restrict_partialSourceWord_eq_partialSourceLocalMap] using
    Word.groupByPartyIso_eval_eq_tensorRestrictions (w.partialSourceWord ψ ξ)
      (sources_partialSourceWord w ψ ξ) ps hn (fun p _ => hP p)

end TNLean.PEPS.PairEffect.SourceCircuit
