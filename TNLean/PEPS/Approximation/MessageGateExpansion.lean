/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.MessageMonomial

/-!
# Actual gate expansions after eliminating messages

A gate is a finite weighted list of the original message monomials. Expanding
each message and retaining the original coefficients gives a literal list of
existing party monomials, with exactly the same operator. Its number of terms
is the sum of the actual products of message dimensions. Its absolute
coefficient sum is the corresponding weighted sum of those products.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-message-resources-messagegateexpansion-01
TNLean.PEPS.PairEffect.MessageGate
Provenance-ID: 8769-message-resources-messagegateexpansion-02
TNLean.PEPS.PairEffect.MessageGate.effectCount_expand_le
Provenance-ID: 8769-message-resources-messagegateexpansion-03
TNLean.PEPS.PairEffect.MessageGate.eval
Provenance-ID: 8769-message-resources-messagegateexpansion-04
TNLean.PEPS.PairEffect.MessageGate.eval_expand
Provenance-ID: 8769-message-resources-messagegateexpansion-05
TNLean.PEPS.PairEffect.MessageGate.expand
Provenance-ID: 8769-message-resources-messagegateexpansion-06
TNLean.PEPS.PairEffect.MessageGate.expansion_size
Provenance-ID: 8769-message-resources-messagegateexpansion-07
TNLean.PEPS.PairEffect.MessageGate.expansion_size_le
Provenance-ID: 8769-message-resources-messagegateexpansion-08
TNLean.PEPS.PairEffect.MessageGate.expansion_size_le_of_coeff_le
Provenance-ID: 8769-message-resources-messagegateexpansion-09
TNLean.PEPS.PairEffect.MessageGate.isAllowed_expand
Provenance-ID: 8769-message-resources-messagegateexpansion-10
TNLean.PEPS.PairEffect.MessageGate.mem_expand
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- The original finite weighted list of monomials, before expanding messages. -/
abbrev MessageGate (a b : Layout P) := List (ℂ × MessageMonomial a b)

namespace MessageGate
variable {a b : Layout P}

/-- The original gate operator, with its original scalar coefficients. -/
def eval (L : MessageGate a b) : Mem a →L[ℂ] Mem b :=
  (L.map fun q ↦ q.1 • q.2.eval).sum

/-- Flatten the actual message expansions and retain every original coefficient. -/
def expand (L : MessageGate a b) : PartyGate a b :=
  L.flatMap fun q ↦ q.2.expand.map fun t ↦ (q.1 * t.1, t.2)

/-- Every expanded branch comes from an original monomial and one of its
constructed message-coordinate branches. -/
theorem mem_expand {L : MessageGate a b} {t : ℂ × PartyChain a b} :
    t ∈ L.expand ↔ ∃ q ∈ L, ∃ u ∈ q.2.expand, t = (q.1 * u.1, u.2) := by
  simp only [expand, List.mem_flatMap, List.mem_map, eq_comm]

/-- The actual expanded list has exactly the original gate operator. -/
theorem eval_expand (L : MessageGate a b) : gate (toGate L.expand) = L.eval := by
  rw [gate_toGate_eq_sum]
  simp only [expand, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def, mul_smul]
  unfold eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [← q.2.eval_expand, gate_toGate_eq_sum, List.smul_sum, List.map_map]
  rfl

/-- Message expansion preserves allowedness of the actual monomial factors. -/
theorem isAllowed_expand (L : MessageGate a b) (hL : ∀ q ∈ L, q.2.IsAllowed) :
    ∀ t ∈ L.expand, t.2.IsAllowed := by
  intro t ht
  obtain ⟨q, hq, u, hu, rfl⟩ := mem_expand.mp ht
  exact (q.2.isAllowed_effectCount_expand (hL q hq) u hu).1

/-- The original pair-effect bound holds for every expanded branch. -/
theorem effectCount_expand_le (L : MessageGate a b) (hL : ∀ q ∈ L, q.2.IsAllowed)
    {r : ℕ} (hr : ∀ q ∈ L, q.2.effectCount ≤ r) :
    ∀ t ∈ L.expand, t.2.toEffectChain.effectCount ≤ r := by
  intro t ht
  obtain ⟨q, hq, u, hu, rfl⟩ := mem_expand.mp ht
  exact ((q.2.isAllowed_effectCount_expand (hL q hq) u hu).2).trans_le (hr q hq)

/-- Exact branch count and coefficient mass, before applying uniform resource
bounds. Original monomial occurrences remain separate even if their values agree. -/
theorem expansion_size (L : MessageGate a b) :
    L.expand.length = (L.map fun q ↦ q.2.messageDimensions.prod).sum ∧
      (L.expand.map fun t ↦ ‖t.1‖).sum =
        (L.map fun q ↦ ‖q.1‖ * (q.2.messageDimensions.prod : ℝ)).sum := by
  constructor
  · simp only [expand, List.length_flatMap, List.length_map]
    apply congrArg List.sum
    exact List.map_congr_left fun q _ ↦ q.2.expansion_size.1
  · simp only [expand, List.flatMap_def, List.map_flatten, List.sum_flatten,
      List.map_map, Function.comp_def, norm_mul, List.sum_map_mul_left]
    apply congrArg List.sum
    exact List.map_congr_left fun q _ ↦ congrArg (‖q.1‖ * ·) q.2.expansion_size.2

/-- At most `K` original monomials, each with at most `m` messages of dimension
at most `D`, give the stated count and coefficient-sum bounds. -/
theorem expansion_size_le (L : MessageGate a b) (D : ℝ) (m K : ℕ)
    (hD : 1 ≤ D) (hK : L.length ≤ K)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m) :
    (L.expand.length : ℝ) ≤ K * D ^ m ∧
      (L.expand.map fun t ↦ ‖t.1‖).sum ≤ (L.map fun q ↦ ‖q.1‖).sum * D ^ m := by
  have hp : ∀ q ∈ L, (q.2.messageDimensions.prod : ℝ) ≤ D ^ m := by
    intro q hq
    exact q.2.expansion_size.2.symm.trans_le
      (q.2.expansion_size_le D m hD (hd q hq) (hm q hq)).2
  constructor
  · rw [L.expansion_size.1, Nat.cast_list_sum, List.map_map]
    have hs := List.sum_le_length_nsmul
      (L.map fun q ↦ (q.2.messageDimensions.prod : ℝ)) (D ^ m) (by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hp q hq)
    have hs' : (L.map fun q ↦ (q.2.messageDimensions.prod : ℝ)).sum ≤
        (L.length : ℝ) * D ^ m := by
      simpa only [List.length_map, nsmul_eq_mul] using hs
    exact hs'.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) (by positivity))
  · rw [L.expansion_size.2]
    have hs := List.sum_le_sum (fun q hq ↦
      mul_le_mul_of_nonneg_left (hp q hq) (norm_nonneg q.1))
    simpa only [List.sum_map_mul_right] using hs

/-- An individual original coefficient bound gives the corresponding explicit
coefficient mass bound after expanding the bounded messages. -/
theorem expansion_size_le_of_coeff_le (L : MessageGate a b) (D C : ℝ) (m K : ℕ)
    (hD : 1 ≤ D) (hC : 0 ≤ C) (hK : L.length ≤ K)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m)
    (hc : ∀ q ∈ L, ‖q.1‖ ≤ C) :
    (L.expand.length : ℝ) ≤ K * D ^ m ∧
      (L.expand.map fun t ↦ ‖t.1‖).sum ≤ (K : ℝ) * C * D ^ m := by
  have hs := List.sum_le_length_nsmul (L.map fun q ↦ ‖q.1‖) C (by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact hc q hq)
  have hmass : (L.map fun q ↦ ‖q.1‖).sum ≤ (K : ℝ) * C := by
    have hs' : (L.map fun q ↦ ‖q.1‖).sum ≤ (L.length : ℝ) * C := by
      simpa only [List.length_map, nsmul_eq_mul] using hs
    exact hs'.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) hC)
  have hsize := L.expansion_size_le D m K hD hK hd hm
  exact ⟨hsize.1, hsize.2.trans (mul_le_mul_of_nonneg_right hmass (by positivity))⟩

end MessageGate
end TNLean.PEPS.PairEffect
