/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Sym.Card
import TNLean.PEPS.Approximation.EffectCircuitResources

/-! # Actual pair-source positions in replacement circuits

Common slots contain one source for every unordered distinct participating pair.
The total number of source positions is consequently bounded by the original
nonprivate gate count times the number of pairs in the participation bound.

Source: polynomial-PEPS 04-compression.tex, lines 140–147, 199–229 and 342–364.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P ι : Type} [Fintype ι] {c : ι → ℂ} {a b : Layout P}

/-- Each actual prepared branch creates one pair source at each common slot.
Source: polynomial-PEPS, `04-compression.tex:233–251` and `342–355`. -/
theorem PreparedSourceGate.length_sources_branchWord
    (G : PreparedSourceGate c a b) (ξ : ι) :
    (G.branchWord ξ).sources.length = G.slots.length := by
  rw [G.sources_branchWord]
  simp only [SourceInventory.ofSlots, List.length_ofFn]

/-- The common prepared slots are exactly all unordered distinct participating pairs.
Source: polynomial-PEPS, `04-compression.tex:233–251` and `342–355`. -/
theorem PreparedSourceGate.length_slots [Fintype P]
    (G : PreparedSourceGate c a b) : G.slots.length = (Fintype.card P).choose 2 := by
  classical
  let s := (G.slots.map PairSource.partyPair).toFinset
  have hc : Fintype.card {k : Sym2 P // ¬k.IsDiag} = s.card :=
    Fintype.card_of_subtype s (by intro k; simpa [s] using G.pair_complete k)
  have hlen : G.slots.length = s.card := by
    simpa only [s, List.length_map] using
      (List.toFinset_card_of_nodup G.pair_nodup).symm
  exact hlen.trans (hc.symm.trans Sym2.card_subtype_not_diag)

/-- The actual prepared monomial has one normalized source on every distinct
participating party pair, including one-dimensional padding slots.
Source: polynomial-PEPS, `04-compression.tex:233–251` and `342–355`. -/
theorem PreparedSourceGate.length_sources_branchWord_eq_choose [Fintype P]
    (G : PreparedSourceGate c a b) (ξ : ι) :
    (G.branchWord ξ).sources.length = (Fintype.card P).choose 2 :=
  (G.length_sources_branchWord ξ).trans G.length_slots

/-- Bounded gate participation gives a constant bound on actual prepared sources,
independent of stack length, private dimensions and original expansion size.
Source: polynomial-PEPS, `04-compression.tex:140–147` and `233–251`. -/
theorem PreparedSourceGate.length_sources_branchWord_le_choose [Fintype P]
    (G : PreparedSourceGate c a b) (ξ : ι) {b : ℕ} (hb : Fintype.card P ≤ b) :
    (G.branchWord ξ).sources.length ≤ b.choose 2 := by
  rw [G.length_sources_branchWord_eq_choose]
  exact Nat.choose_le_choose 2 hb
end TNLean.PEPS.PairEffect

namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}
/-- Every actual gate occurrence has one common source slot per unordered pair
of its participating original parties.
Source: polynomial-PEPS, `04-compression.tex:233–251` and `342–355`. -/
theorem slotCount_eq_choose {a b : Layout P} (w : SourceCircuit a b)
    (g : w.gateLocations) : w.slotCount g = (w.participants g).card.choose 2 := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv => cases g with
    | inl g => exact ihw g
    | inr g => exact ihv g
  | localMap => exact nomatch g
  | @gate C ι _ _ owner a b c G tail =>
      simpa only [slotCount, participants, Finset.card_map, Finset.card_univ]
        using G.length_slots
  | swap => exact nomatch g
  | frame t w ih => exact ih g

/-- Count actual source positions over all chronological gate occurrences.
Source: polynomial-PEPS, `04-compression.tex:342–364`. -/
theorem card_sourceLocations_eq_sum_choose {a b : Layout P} (w : SourceCircuit a b) :
    Fintype.card w.sourceLocations = ∑ g : w.gateLocations, (w.participants g).card.choose 2 := by
  change Fintype.card (Σ g : w.gateLocations, Fin (w.slotCount g)) = _
  simp only [Fintype.card_sigma, Fintype.card_fin, slotCount_eq_choose]

/-- A participant bound at every original gate occurrence bounds all actual
source positions, with no dependence on monomial labels or private dimensions.
Source: polynomial-PEPS, `04-compression.tex:140–147` and `342–364`. -/
theorem card_sourceLocations_le {a b : Layout P} (w : SourceCircuit a b) {b₀ : ℕ}
    (hb : ∀ g : w.gateLocations, (w.participants g).card ≤ b₀) :
    Fintype.card w.sourceLocations ≤ Fintype.card w.gateLocations * b₀.choose 2 := by
  rw [card_sourceLocations_eq_sum_choose]
  exact (Finset.sum_le_sum fun g _ ↦ Nat.choose_le_choose 2 (hb g)).trans_eq
    (by simp)
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.OriginalCircuit
variable {P : Type}
/-- Actual source positions of the constructed replacement are bounded by the
original nonprivate gate count and the original per-gate participant bound.
Source: polynomial-PEPS, `04-compression.tex:140–147`, `199–229` and `342–364`. -/
theorem card_sourceLocations_replacement_le {r : ℕ} {S δ : ℝ} {a b : Layout P}
    (w : OriginalCircuit a b) (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) {b₀ : ℕ}
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ b₀) :
    Fintype.card (w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hb)).sourceLocations ≤
        w.nonprivateCount * b₀.choose 2 := by
  let R := w.produce.replacement hδ w.isAllowed_produce
    ((w.isExpansionBounded_produce_iff r S).mpr hb)
  let e := w.replacementLocationsEquiv hδ hb
  have hpartR : ∀ g : R.gateLocations, (R.participants g).card ≤ b₀ := by
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    simpa only [e, R, w.participants_replacementLocationsEquiv hδ hb g] using hpart g
  have hcard := w.card_nonprivateLocations
  exact (R.card_sourceLocations_le hpartR).trans_eq
    (congrArg (fun n ↦ n * b₀.choose 2) ((Fintype.card_congr e).symm.trans hcard))
end TNLean.PEPS.PairEffect.OriginalCircuit
