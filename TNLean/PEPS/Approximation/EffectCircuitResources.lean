/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.SourceOnlyReduction

/-! # Participation counts of source-only replacements

Source: polynomial-PEPS 04-compression.tex, lines 137–147 and 199–229.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-effectcircuitresources-01
TNLean.PEPS.PairEffect.OriginalCircuit.card_nonprivateLocations
Provenance-ID: 8769-source-resource-effectcircuitresources-02
TNLean.PEPS.PairEffect.OriginalCircuit.natCard_nonprivateLocations
Provenance-ID: 8769-source-resource-effectcircuitresources-03
TNLean.PEPS.PairEffect.OriginalCircuit.nonprivateLocationsFintype
Provenance-ID: 8769-source-resource-effectcircuitresources-04
TNLean.PEPS.PairEffect.OriginalCircuit.participationCount
Provenance-ID: 8769-source-resource-effectcircuitresources-05
TNLean.PEPS.PairEffect.OriginalCircuit.participationCount_replacement
Provenance-ID: 8769-source-resource-effectcircuitresources-06
TNLean.PEPS.PairEffect.OriginalCircuit.participationCount_replacement_le
Provenance-ID: 8769-source-resource-effectcircuitresources-07
TNLean.PEPS.PairEffect.OriginalCircuit.participationLocationsEquiv
Provenance-ID: 8769-source-resource-effectcircuitresources-08
TNLean.PEPS.PairEffect.SourceCircuit.participationCount
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
namespace OriginalCircuit
variable {P : Type}

/-- A finite original chronology has finitely many nonprivate occurrences,
independently of the number or dimensions of private registers.
Source: polynomial-PEPS 04-compression.tex, lines 137–147 and 199–229. -/
instance nonprivateLocationsFintype : {a b : Layout P} →
    (w : OriginalCircuit a b) → Fintype w.nonprivateLocations
  | _, _, .id _ => inferInstanceAs (Fintype Empty)
  | _, _, .comp w v => by
      letI := nonprivateLocationsFintype w
      letI := nonprivateLocationsFintype v
      exact inferInstanceAs (Fintype (w.nonprivateLocations ⊕ v.nonprivateLocations))
  | _, _, .privateMap .. => inferInstanceAs (Fintype Empty)
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ _ _ _ _ =>
      inferInstanceAs (Fintype Unit)
  | _, _, .swap .. => inferInstanceAs (Fintype Empty)
  | _, _, .frame _ w => nonprivateLocationsFintype w
/-- The finite nonprivate occurrence set has the original structural gate count.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
theorem natCard_nonprivateLocations {a b : Layout P} (w : OriginalCircuit a b) :
    Nat.card w.nonprivateLocations = w.nonprivateCount := by
  induction w <;> simp_all [nonprivateLocations, nonprivateCount]

/-- Finite enumeration agrees with the original structural nonprivate gate count.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
theorem card_nonprivateLocations {a b : Layout P} (w : OriginalCircuit a b) :
    Fintype.card w.nonprivateLocations = w.nonprivateCount :=
  Nat.card_eq_fintype_card.symm.trans w.natCard_nonprivateLocations
end OriginalCircuit
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect
variable {P : Type}
/-- The number of nonprivate occurrences involving a party over the whole
original chronology. Source: polynomial-PEPS 04-compression.tex, lines 140–142. -/
def OriginalCircuit.participationCount {a b : Layout P} (w : OriginalCircuit a b)
    (p : P) : ℕ := Nat.card {g : w.nonprivateLocations // p ∈ w.participants g}

/-- The number of expanded occurrences involving a party over the whole
source-only chronology. Source: polynomial-PEPS 04-compression.tex, lines 140–142. -/
def SourceCircuit.participationCount {a b : Layout P} (w : SourceCircuit a b)
    (p : P) : ℕ := Nat.card {g : w.gateLocations // p ∈ w.participants g}

/-- Replacement preserves the full occurrence set involving any fixed party.
Source: polynomial-PEPS 04-compression.tex, lines 140–142 and 229. -/
def OriginalCircuit.participationLocationsEquiv {r : ℕ} {S δ : ℝ}
    {a b : Layout P} (w : OriginalCircuit a b) (hδ : 0 < δ)
    (hb : w.IsExpansionBounded r S) (p : P) :
    {g : w.nonprivateLocations // p ∈ w.participants g} ≃
      {g : (w.produce.replacement hδ w.isAllowed_produce
        ((w.isExpansionBounded_produce_iff r S).mpr hb)).gateLocations //
        p ∈ (w.produce.replacement hδ w.isAllowed_produce
          ((w.isExpansionBounded_produce_iff r S).mpr hb)).participants g} :=
  (w.replacementLocationsEquiv hδ hb).subtypeEquiv (fun g ↦ by
    rw [w.participants_replacementLocationsEquiv hδ hb g])
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect.OriginalCircuit
variable {P : Type}

/-- Replacement preserves each party's number of participating nonprivate
occurrences over the whole chronology, including repeated uses of a gate.
Source: polynomial-PEPS 04-compression.tex, lines 140–142 and 229. -/
theorem participationCount_replacement {r : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : OriginalCircuit a b) (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) (p : P) :
    (w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).participationCount p =
        w.participationCount p :=
  (Nat.card_congr (w.participationLocationsEquiv hδ hb p)).symm

/-- The original whole-lifetime participation bound holds for the actual
source-only replacement. Source: polynomial-PEPS 04-compression.tex, lines 140–142. -/
theorem participationCount_replacement_le {r b₀ : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : OriginalCircuit a b) (hδ : 0 < δ) (hb : w.IsExpansionBounded r S)
    (hlifetime : ∀ p, w.participationCount p ≤ b₀) (p : P) :
    (w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).participationCount p ≤ b₀ :=
  (w.participationCount_replacement hδ hb p).trans_le (hlifetime p)
end TNLean.PEPS.PairEffect.OriginalCircuit
