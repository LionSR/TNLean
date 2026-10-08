/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.OriginalCircuit
import TNLean.PEPS.Approximation.SourceCircuitLocations

/-! # Participating parties in source-only replacement

The replacement has exactly one expanded gate occurrence for each original
nonprivate occurrence, with the same participating parties. Permutations and
private preparations introduce no such occurrences.

Source: polynomial-PEPS, `04-compression.tex`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectcircuitlocations-01
TNLean.PEPS.PairEffect.EffectCircuit.exists_replacementLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-02
TNLean.PEPS.PairEffect.EffectCircuit.participants_replacementLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-03
TNLean.PEPS.PairEffect.EffectCircuit.replacementLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-04
TNLean.PEPS.PairEffect.OriginalCircuit.participants_replacementLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-05
TNLean.PEPS.PairEffect.OriginalCircuit.replacementLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-06
TNLean.PEPS.PairEffect.SourceCircuit.castLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-07
TNLean.PEPS.PairEffect.SourceCircuit.exchangeBlocksLocationsEquivEmpty
Provenance-ID: 8769-source-resource-effectcircuitlocations-08
TNLean.PEPS.PairEffect.SourceCircuit.false_of_gateLocation_ofLocalWord
Provenance-ID: 8769-source-resource-effectcircuitlocations-09
TNLean.PEPS.PairEffect.SourceCircuit.frameListLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-10
TNLean.PEPS.PairEffect.SourceCircuit.ofLocalWordLocationsEquivEmpty
Provenance-ID: 8769-source-resource-effectcircuitlocations-11
TNLean.PEPS.PairEffect.SourceCircuit.participants_castLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitlocations-12
TNLean.PEPS.PairEffect.SourceCircuit.participants_frameListLocationsEquiv
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
namespace SourceCircuit
/-- Changes of register-layout identification do not change gate occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 210–229. -/
def castLocationsEquiv {a b a' b' : Layout P} (w : SourceCircuit a b)
    (h : a = a') (h' : b = b') : w.gateLocations ≃ (w.castLayouts h h').gateLocations := by
  cases h
  cases h'
  exact Equiv.refl _

/-- Layout identification does not change the original participating parties.
Source: polynomial-PEPS 04-compression.tex, line 229. -/
theorem participants_castLocationsEquiv {a b a' b' : Layout P} (w : SourceCircuit a b)
    (h : a = a') (h' : b = b') (g : w.gateLocations) :
    (w.castLayouts h h').participants (w.castLocationsEquiv h h' g) = w.participants g := by
  cases h
  cases h'
  rfl

/-- Retaining preceding registers creates no nonprivate gate occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 210–229. -/
def frameListLocationsEquiv {a b : Layout P} (w : SourceCircuit a b) :
    (rs : Layout P) → w.gateLocations ≃ (w.frameList rs).gateLocations
  | [] => Equiv.refl _
  | _ :: rs => frameListLocationsEquiv w rs

/-- Retained registers do not alter any later gate's participating set.
Source: polynomial-PEPS 04-compression.tex, line 229. -/
theorem participants_frameListLocationsEquiv {a b : Layout P} (w : SourceCircuit a b)
    (rs : Layout P) (g : w.gateLocations) :
    (w.frameList rs).participants (w.frameListLocationsEquiv rs g) = w.participants g := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih

/-- A word made exclusively of local operations and tensor-order permutations
contains no expanded gate. Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
theorem false_of_gateLocation_ofLocalWord {a b : Layout P} (w : Word a b)
    (h : w.sources = []) (g : (ofLocalWord w h).gateLocations) : False := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw _ g
      | inr g => exact ihv _ g
  | localMap => exact nomatch g
  | source => cases h
  | swap => exact nomatch g
  | frame r w ih => exact ih h g

/-- Exact local words have an empty type of expanded gate occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
def ofLocalWordLocationsEquivEmpty {a b : Layout P} (w : Word a b)
    (h : w.sources = []) : (ofLocalWord w h).gateLocations ≃ Empty where
  toFun g := (false_of_gateLocation_ofLocalWord w h g).elim
  invFun g := nomatch g
  left_inv g := (false_of_gateLocation_ofLocalWord w h g).elim
  right_inv g := nomatch g

/-- Exchanges inserted only to order retained registers have no nonprivate
occurrences. Source: polynomial-PEPS 04-compression.tex, lines 210–229. -/
def exchangeBlocksLocationsEquivEmpty (a b tail : Layout P) :
    (exchangeBlocks a b tail).gateLocations ≃ Empty :=
  ofLocalWordLocationsEquivEmpty (Word.exchangeBlocks a b tail) (by simp)
end SourceCircuit
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect
namespace EffectCircuit
/-- Replacement preserves every original expanded occurrence and its prescribed
participant image. Newly inserted tensor-order exchanges contribute no occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 210–229. -/
theorem exists_replacementLocationsEquiv {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    {a b : Layout P} (w : EffectCircuit a b) (hw : w.IsAllowed)
    (hb : w.IsExpansionBounded r S) :
    ∃ e : w.gateLocations ≃ (w.replacement hδ hw hb).gateLocations,
      ∀ g, (w.replacement hδ hw hb).participants (e g) = w.participants g := by
  let m := stackLength r S δ
  induction w with
  | id =>
      refine ⟨Equiv.refl _, ?_⟩
      intro g
      exact nomatch g
  | @comp a b d w v ihw ihv =>
      obtain ⟨ew, hew⟩ := ihw hw.1 hb.1
      obtain ⟨ev, hev⟩ := ihv hw.2 hb.2
      let vR := v.replacement hδ hw.2 hb.2
      let wR := w.replacement hδ hw.1 hb.1
      let rs := w.auxiliary m
      let e := Equiv.sumCongr ew (ev.trans (vR.frameListLocationsEquiv rs))
      let hOut := (List.append_assoc rs (v.auxiliary m) d).symm
      refine ⟨e.trans ((SourceCircuit.comp wR (vR.frameList rs)).castLocationsEquiv
        rfl hOut), ?_⟩
      intro g
      refine (SourceCircuit.participants_castLocationsEquiv
        (SourceCircuit.comp wR (vR.frameList rs)) rfl hOut (e g)).trans ?_
      cases g with
      | inl g => exact hew g
      | inr g =>
          exact (vR.participants_frameListLocationsEquiv rs (ev g)).trans (hev g)
  | localMap =>
      refine ⟨Equiv.refl _, ?_⟩
      intro g
      exact nomatch g
  | @gate C _ owner a b L tail =>
      let G := Classical.choose (exists_prepared_effectReplacement_uniform hδ L
        (fun q hq => ⟨hw.1 q hq, hb.1 q hq⟩) hw.2 hb.2)
      let hOut := gate_auxiliary_layout owner m L tail
      refine ⟨(SourceCircuit.gate owner G tail).castLocationsEquiv rfl hOut, ?_⟩
      intro g
      exact (SourceCircuit.gate owner G tail).participants_castLocationsEquiv rfl hOut g
  | swap =>
      refine ⟨Equiv.refl _, ?_⟩
      intro g
      exact nomatch g
  | @frame t a b w ih =>
      obtain ⟨e, he⟩ := ih hw hb
      let rs := w.auxiliary m
      let E := SourceCircuit.exchangeBlocks [t] rs b
      let : IsEmpty E.gateLocations :=
        Function.isEmpty (SourceCircuit.exchangeBlocksLocationsEquivEmpty [t] rs b)
      refine ⟨e.trans (Equiv.sumEmpty _ E.gateLocations).symm, ?_⟩
      intro g
      exact he g

/-- The occurrence correspondence constructed from the original chronology and
its actual replacement. Source: polynomial-PEPS 04-compression.tex, line 229. -/
def replacementLocationsEquiv {r : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : EffectCircuit a b) (hδ : 0 < δ) (hw : w.IsAllowed) (hb : w.IsExpansionBounded r S) :
    w.gateLocations ≃ (w.replacement hδ hw hb).gateLocations :=
  Classical.choose (exists_replacementLocationsEquiv hδ w hw hb)

/-- Replacement retains the participant image of every original expanded gate.
Source: polynomial-PEPS 04-compression.tex, line 229. -/
theorem participants_replacementLocationsEquiv {r : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : EffectCircuit a b) (hδ : 0 < δ) (hw : w.IsAllowed) (hb : w.IsExpansionBounded r S)
    (g : w.gateLocations) :
    (w.replacement hδ hw hb).participants (w.replacementLocationsEquiv hδ hw hb g) =
      w.participants g :=
  Classical.choose_spec (exists_replacementLocationsEquiv hδ w hw hb) g
end EffectCircuit

namespace OriginalCircuit
/-- Each original nonprivate gate corresponds to exactly one source-prepared
replacement gate. Source: polynomial-PEPS 04-compression.tex, line 229. -/
def replacementLocationsEquiv {r : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : OriginalCircuit a b) (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) :
    w.nonprivateLocations ≃
      (w.produce.replacement hδ w.isAllowed_produce
        ((w.isExpansionBounded_produce_iff r S).mpr hb)).gateLocations :=
  w.produceLocationsEquiv.trans (w.produce.replacementLocationsEquiv hδ w.isAllowed_produce
    ((w.isExpansionBounded_produce_iff r S).mpr hb))

/-- The source-only construction has exactly the original nonprivate participant
sets under the occurrence correspondence.
Source: polynomial-PEPS 04-compression.tex, line 229. -/
theorem participants_replacementLocationsEquiv {r : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : OriginalCircuit a b) (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (g : w.nonprivateLocations) :
    (w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).participants
        (w.replacementLocationsEquiv hδ hb g) = w.participants g :=
  (w.produce.participants_replacementLocationsEquiv hδ w.isAllowed_produce
    ((w.isExpansionBounded_produce_iff r S).mpr hb) (w.produceLocationsEquiv g)).trans
      (w.participants_produce g)
end OriginalCircuit
end TNLean.PEPS.PairEffect
