/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyChainComposition

/-!
# Composition of actual gate expansions

The chronological product of two finite monomial expansions is their ordered
Cartesian expansion. Each branch retains the two original monomials in order.
The number of branches and the absolute coefficient sums multiply, while the
numbers of pair effects add. These identities apply equally to message basis
expansions and to arbitrary existing source and effect monomials.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-message-resources-partygatecomposition-01
TNLean.PEPS.PairEffect.PartyGate.comp
Provenance-ID: 8769-message-resources-partygatecomposition-02
TNLean.PEPS.PairEffect.PartyGate.effectCount_comp_le
Provenance-ID: 8769-message-resources-partygatecomposition-03
TNLean.PEPS.PairEffect.PartyGate.gate_comp
Provenance-ID: 8769-message-resources-partygatecomposition-04
TNLean.PEPS.PairEffect.PartyGate.isAllowed_comp
Provenance-ID: 8769-message-resources-partygatecomposition-05
TNLean.PEPS.PairEffect.PartyGate.length_comp
Provenance-ID: 8769-message-resources-partygatecomposition-06
TNLean.PEPS.PairEffect.PartyGate.mem_comp
Provenance-ID: 8769-message-resources-partygatecomposition-07
TNLean.PEPS.PairEffect.PartyGate.sum_norm_comp
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.PartyGate
variable {P : Type} {a b c : Layout P}

/-- The literal ordered expansion of the second gate after the first. -/
def comp (L : PartyGate a b) (K : PartyGate b c) : PartyGate a c :=
  L.flatMap fun l ↦ K.map fun k ↦ (l.1 * k.1, PartyChain.comp l.2 k.2)

/-- A composed branch is exactly one ordered pair of original branches. -/
theorem mem_comp {L : PartyGate a b} {K : PartyGate b c} {q : ℂ × PartyChain a c} :
    q ∈ comp L K ↔ ∃ l ∈ L, ∃ k ∈ K, q = (l.1 * k.1, PartyChain.comp l.2 k.2) := by
  simp only [comp, List.mem_flatMap, List.mem_map, eq_comm]

/-- Splitting a literal expansion list splits its operator sum. -/
private theorem gate_append (L K : PartyGate a b) :
    gate (toGate (L ++ K)) = gate (toGate L) + gate (toGate K) := by
  induction L with
  | nil => simp only [List.nil_append, gate, zero_add]
  | cons l L ih => simp only [List.cons_append, toGate, gate, ih, add_assoc]

/-- Fixing the first monomial leaves the second expansion as a chronological sum. -/
private theorem gate_comp_row (l : ℂ × PartyChain a b) (K : PartyGate b c) :
    gate (toGate (K.map fun k ↦ (l.1 * k.1, PartyChain.comp l.2 k.2))) =
      gate (toGate K) ∘L (l.1 • l.2.toEffectChain.eval) := by
  induction K with
  | nil => simp only [List.map_nil, toGate, gate, zero_comp]
  | cons k K ih =>
      simp only [List.map_cons, toGate, gate, PartyChain.eval_comp, ih, add_comp,
        smul_comp, comp_smul, smul_add, smul_smul]

/-- The composed list evaluates to the actual chronological operator product. -/
theorem gate_comp (L : PartyGate a b) (K : PartyGate b c) :
    gate (toGate (comp L K)) = gate (toGate K) ∘L gate (toGate L) := by
  induction L with
  | nil => simp only [comp, List.flatMap_nil, toGate, gate, comp_zero]
  | cons l L ih =>
      change gate (toGate
        ((K.map fun k ↦ (l.1 * k.1, PartyChain.comp l.2 k.2)) ++ comp L K)) = _
      rw [gate_append, gate_comp_row, ih]
      simp only [gate, comp_add]

/-- Every pair of original monomial occurrences contributes one composed branch. -/
theorem length_comp (L : PartyGate a b) (K : PartyGate b c) :
    (comp L K).length = L.length * K.length := by
  simp [comp, List.length_flatMap]

/-- Absolute coefficient sums multiply exactly under composition. -/
theorem sum_norm_comp (L : PartyGate a b) (K : PartyGate b c) :
    ((comp L K).map fun q ↦ ‖q.1‖).sum =
      (L.map fun q ↦ ‖q.1‖).sum * (K.map fun q ↦ ‖q.1‖).sum := by
  simp only [comp, List.map_flatten, List.flatMap_def, List.sum_flatten, List.map_map,
    Function.comp_def, norm_mul, List.sum_map_mul_left, List.sum_map_mul_right]

/-- Each composed monomial consists of the same allowed factors as its two
original constituents, in their chronological order. -/
theorem isAllowed_comp (L : PartyGate a b) (K : PartyGate b c)
    (hL : ∀ l ∈ L, l.2.IsAllowed) (hK : ∀ k ∈ K, k.2.IsAllowed) :
    ∀ q ∈ comp L K, q.2.IsAllowed := by
  intro q hq
  obtain ⟨l, hl, k, hk, rfl⟩ := mem_comp.mp hq
  exact PartyChain.isAllowed_comp l.2 k.2 (hL l hl) (hK k hk)

/-- Pair-effect bounds add for the actual composed branches. -/
theorem effectCount_comp_le (L : PartyGate a b) (K : PartyGate b c) {r s : ℕ}
    (hL : ∀ l ∈ L, l.2.toEffectChain.effectCount ≤ r)
    (hK : ∀ k ∈ K, k.2.toEffectChain.effectCount ≤ s) :
    ∀ q ∈ comp L K, q.2.toEffectChain.effectCount ≤ r + s := by
  intro q hq
  obtain ⟨l, hl, k, hk, rfl⟩ := mem_comp.mp hq
  exact (PartyChain.effectCount_comp l.2 k.2).trans_le (Nat.add_le_add (hL l hl) (hK k hk))

end TNLean.PEPS.PairEffect.PartyGate
