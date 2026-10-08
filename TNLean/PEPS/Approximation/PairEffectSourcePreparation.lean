/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyLayout
import TNLean.PEPS.Approximation.PairSourceGrouping

/-!
# Pair-effect elimination with one source per pair of parties

Every allowed word factors exactly into the preparation of normalized pair
sources followed by local contractions and exchanges of registers. Sources
with the same unordered pair of endpoint parties can be combined before these
remaining operations. Thus each pair occurs at most once, including when the
original word lists its endpoints in opposite orders.

Applying this factorization separately to the words in the pair-effect
elimination preserves the gate, the number of terms, every coefficient and
the common output registers. It supplies the last clause of Lemma 5.1 in
addition to the error, normalization and ownership conclusions.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, Lemma 5.1 (`lem:effects`), `04-compression.tex`,
lines 53–70 and 99–127, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type} {ℓX ℓY : Layout P}

/-- An allowed word is exactly a preparation with at most one normalized
source on each unordered pair of parties, followed by an allowed word with
no sources. The pairs occurring in the preparation are exactly the original
pairs. Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 68–70
and 125–127. -/
theorem Word.exists_grouped_source_preparation (w : Word ℓX ℓY) (hw : w.IsAllowed) :
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ k ∈ w.sources.map PairSource.partyPair) ∧
      ∃ v : Word (S.layout ++ ℓX) ℓY,
        v.IsAllowed ∧ v.sources = [] ∧ w.eval = v.eval ∘L (S.prepare ℓX).eval := by
  obtain ⟨S, hS, hN, hK, hE⟩ :=
    SourceInventory.exists_grouped w.sources (w.isNormalized_sources hw)
  obtain ⟨v, hv, hs, he⟩ := hE ℓX
  refine ⟨S, hS, hN, hK, .comp v w.localPart,
    ⟨hv, w.isAllowed_localPart hw⟩, ?_, ?_⟩
  · simp only [Word.sources, Word.sources_localPart, hs, List.nil_append]
  · rw [Word.eval_comp, comp_assoc, he, ← w.eval_eq_localPart_comp_prepare]

/-- Elimination of pair effects, including the combination of all sources on
each unordered pair of parties. Every conclusion of `partyPairEffectElimination`
is retained, and every word in its expansion admits an exact factorization
with distinct pair sources and no sources in the remaining operations.
No assumption on the contraction norm of the whole weighted gate is needed.
Source: polynomial-PEPS Lemma 5.1 (`lem:effects`), `04-compression.tex`,
lines 53–70 and 99–127. -/
lemma partyPairEffectElimination_with_grouped_sources {m r : ℕ} (hm : m ≠ 0)
    (L : PartyGate ℓX ℓY)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.toEffectChain.effectCount ≤ r) :
    ‖inventoryVector m (toGate L)‖ = 1 ∧
    (∀ x, gateIso m L ((prepGate m L).eval x) = x ⊗ₜ inventoryVector m (toGate L)) ∧
    (prepGate m L).IsAllowed ∧
    ‖replaceGate m (toGate L) - appendRight (inventoryVector m (toGate L)) ∘L gate (toGate L)‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ∧
    replaceGate m (toGate L) =
      ((wordList m L).map fun q => q.1 • (isoL (gateIso m L) ∘L q.2.eval)).sum ∧
    (∀ q ∈ wordList m L, q.2.IsAllowed) ∧
    (∀ q ∈ termList m (toGate L), IsSourceOnly (isoL (gateIso m L).symm ∘L q.2)) ∧
    (wordList m L).length ≤ L.length * m ^ r ∧
    ((wordList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum ∧
    gateOut m L = (L.flatMap fun p => p.2.stackRegs m) ++ ℓY ∧
    (∀ p ∈ L, (p.2.stackRegs m).map Reg.owner =
      p.2.effectParties.flatMap fun e => (List.replicate m [e.1, e.2]).flatten) ∧
    ∀ q ∈ wordList m L,
      ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
        (∀ k, k ∈ S.map PairSource.partyPair ↔ k ∈ q.2.sources.map PairSource.partyPair) ∧
        ∃ v : Word (S.layout ++ ℓX) (gateOut m L),
          v.IsAllowed ∧ v.sources = [] ∧ q.2.eval = v.eval ∘L (S.prepare ℓX).eval := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    partyPairEffectElimination hm L hL
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    fun q hq ↦ q.2.exists_grouped_source_preparation (h6 q hq)⟩

end TNLean.PEPS.PairEffect
