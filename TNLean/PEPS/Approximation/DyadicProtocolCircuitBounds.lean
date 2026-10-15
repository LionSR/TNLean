/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolOriginalCircuit
import TNLean.PEPS.Approximation.OriginalCircuitLayoutResources

/-!
# Gate bounds and participating sets in the complete dyadic protocol circuit

The lifetime sum recorded in a supplied bounded protocol is the participation
count of its actual ordered circuit, including after identifying equal input
and output register layouts. Consequently the protocol's bound holds for that
circuit. The total gate count is bounded by the per-change count times the
number of changes. Every nonprivate occurrence also has an original stage
occurrence with the same participating set. The existence of the bounded
protocol is a separate assertion. The uniform monomial, pair-effect and
coefficient-sum bounds also hold for the complete circuit.

Source: polynomial-PEPS manuscript, Proposition 7.1, `06-geometry.tex`,
lines 25–32, and Theorem 5.2, `04-compression.tex`, lines 140–142;
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation.DyadicProtocol

open TNLean.PEPS.PairEffect

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)
variable {Ω : StateSpace L q} {C : ℝ} {b k r : ℕ}

/-- The supplied protocol's lifetime bound holds for its actual ordered circuit.
Source: polynomial-PEPS manuscript, Proposition 7.1, 06-geometry.tex, lines 31–32,
and Theorem 5.2, 04-compression.tex, lines 140–142. -/
theorem IsDistributionProtocol.participationCount_originalCircuit_le
    (h : D.IsDistributionProtocol Ω C b k r) (p : P) :
    D.originalCircuit.participationCount p ≤ b := by
  simpa only [originalCircuit, OriginalCircuit.participationCount_castLayouts,
    OriginalCircuit.participationCount_sequence, participation] using h.participation_le p

/-- The actual complete circuit has at most the per-change gate bound times
its number of changes. Source: polynomial-PEPS manuscript, Proposition 7.1,
06-geometry.tex, lines 25–32. -/
theorem IsDistributionProtocol.nonprivateCount_originalCircuit_le
    (h : D.IsDistributionProtocol Ω C b k r) :
    D.originalCircuit.nonprivateCount ≤ b * D.changes := by
  rw [originalCircuit, OriginalCircuit.nonprivateCount_castLayouts,
    OriginalCircuit.nonprivateCount_sequence]
  simpa only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm] using
    (Finset.sum_le_sum (s := Finset.range D.changes)
      (fun t ht ↦ h.nonprivateCount_le t (Finset.mem_range.mp ht)))

/-- Every occurrence of the complete protocol has one original stage with
exactly the same participating set. Source: polynomial-PEPS manuscript,
Proposition 7.1, 06-geometry.tex, lines 25–37. -/
theorem exists_stage_participants_originalCircuit
    {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P) :
    ∀ g : D.originalCircuit.nonprivateLocations,
      ∃ t < D.changes, ∃ γ : (D.step t).nonprivateLocations,
        D.originalCircuit.participants g = (D.step t).participants γ := by
  unfold originalCircuit
  exact OriginalCircuit.forall_participants_castLayouts
    (OriginalCircuit.sequence D.layout D.step D.changes)
    D.layout_zero D.layout_changes
    (fun S ↦ ∃ t < D.changes, ∃ γ : (D.step t).nonprivateLocations,
      S = (D.step t).participants γ)
    (OriginalCircuit.forall_participants_sequence D.layout D.step
      (fun S ↦ ∃ t < D.changes, ∃ γ : (D.step t).nonprivateLocations,
        S = (D.step t).participants γ)
      D.changes (fun t ht γ ↦ ⟨t, ht, γ, rfl⟩))

/-- The original complete circuit retains the supplied uniform expansion bound.
Source: polynomial-PEPS manuscript, Proposition 7.1, 06-geometry.tex, lines 25–32. -/
theorem IsDistributionProtocol.isExpansionBounded_originalCircuit
    (h : D.IsDistributionProtocol Ω C b k r) :
    D.originalCircuit.IsExpansionBounded r (C * (L : ℝ) ^ k) := by
  exact OriginalCircuit.isExpansionBounded_castLayouts
    (OriginalCircuit.sequence D.layout D.step D.changes)
    D.layout_zero D.layout_changes
    (OriginalCircuit.isExpansionBounded_sequence D.layout D.step r
      (C * (L : ℝ) ^ k) D.changes h.expansionBounded)

/-- The original complete circuit retains the supplied monomial-count bound.
Source: polynomial-PEPS manuscript, Proposition 7.1, 06-geometry.tex, lines 25–32. -/
theorem IsDistributionProtocol.isMonomialBounded_originalCircuit
    (h : D.IsDistributionProtocol Ω C b k r) :
    D.originalCircuit.IsMonomialBounded ⌊C * (L : ℝ) ^ k⌋₊ := by
  exact OriginalCircuit.isMonomialBounded_castLayouts
    (OriginalCircuit.sequence D.layout D.step D.changes)
    D.layout_zero D.layout_changes
    (OriginalCircuit.isMonomialBounded_sequence D.layout D.step
      ⌊C * (L : ℝ) ^ k⌋₊ D.changes h.monomialBounded)

end TNLean.PEPS.Approximation.DyadicProtocol
