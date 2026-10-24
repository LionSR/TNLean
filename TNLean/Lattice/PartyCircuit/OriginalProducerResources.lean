/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.ApproximateCircuitResources

/-!
# Original monomial counts and expansion majorants

Every produced occurrence keeps the original monomial count. Increasing the
pair-effect and coefficient-sum majorants preserves the original expansion
condition; this comparison enlarges the expansion bounds of the sheet-stack
changes and of the dyadic protocol. The monomial-count comparison is the form,
for produced occurrences, of the monomial bound in Theorem 5.2.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
lines 143–149 and 199–208, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.Lattice.PartyCircuit.OriginalCircuit

variable {P : Type}

/-- Every actual produced gate occurrence retains its original monomial-list bound.
The producer preserves the original occurrences; no bounds on private memories enter.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 143–149 and 199–208. -/
theorem monomialCount_produce_le_of_isMonomialBounded
    {a b : Layout P} (w : OriginalCircuit a b) {K : ℕ} :
    w.IsMonomialBounded K → ∀ g : w.produce.gateLocations,
      w.produce.monomialCount g ≤ K := by
  induction w with
  | id => intro _ g; exact nomatch g
  | comp w v ihw ihv =>
      intro hK g
      cases g with
      | inl g => exact ihw hK.1 g
      | inr g => exact ihv hK.2 g
  | privateMap => intro _ g; exact nomatch g
  | nonprivateGate =>
      intro hK g
      simpa only [produce, EffectCircuit.monomialCount, IsMonomialBounded] using hK
  | swap => intro _ g; exact nomatch g
  | frame r w ih => intro hK g; exact ih hK g

/-- Increasing the pair-effect bound and the coefficient bound preserves the original expansion
condition. Source: polynomial-PEPS, `04-compression.tex`, lines 199–208. -/
theorem isExpansionBounded_mono {a b : Layout P} (w : OriginalCircuit a b) {r r' : ℕ}
    {s s' : ℝ} (h : w.IsExpansionBounded r s) (hr : r ≤ r') (hs : s ≤ s') :
    w.IsExpansionBounded r' s' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate => exact ⟨fun m hm => (h.1 m hm).trans hr, h.2.trans hs⟩
  | swap => trivial
  | frame _ w ih => exact ih h

end TNLean.Lattice.PartyCircuit.OriginalCircuit
