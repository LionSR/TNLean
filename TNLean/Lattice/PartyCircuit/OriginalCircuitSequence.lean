/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.EffectReplacementExpansion
import TNLean.Lattice.PartyCircuit.EffectCircuitResources

/-!
# Finite chronological composition of original distributed circuits

A finite sequence of original circuits has its actual ordered composite.
Evaluation, nonprivate gate counts, lifetime participation, and the original
expansion bounds are preserved. Repeated occurrences remain distinct; no
finiteness or dimension bound on the party memories is imposed here.

Source: polynomial-PEPS manuscript, Proposition 7.1, `06-geometry.tex`,
lines 25–37, and Theorem 5.2, `04-compression.tex`, lines 140–149 and
199–229, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace TNLean.PEPS.PairEffect.OriginalCircuit

variable {P : Type} (a : ℕ → Layout P)
  (step : (t : ℕ) → OriginalCircuit (a t) (a (t + 1)))

/-- The actual chronological composite through a prescribed stage.
Source: polynomial-PEPS manuscript, `06-geometry.tex`, lines 25–32,
and `07-assembly.tex`, lines 29–36, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
def sequence : (t : ℕ) → OriginalCircuit (a 0) (a t)
  | 0 => .id (a 0)
  | t + 1 => .comp (sequence t) (step t)

/-- Evaluation at the initial stage is the identity.
Source: polynomial-PEPS manuscript, `07-assembly.tex`, lines 29–36. -/
theorem eval_sequence_zero (v : Mem (a 0)) :
    (sequence a step 0).eval v = v := by
  rfl

/-- The next chronological stage acts after the existing composite.
Source: polynomial-PEPS manuscript, `07-assembly.tex`, lines 29–36. -/
theorem eval_sequence_succ (t : ℕ) (v : Mem (a 0)) :
    (sequence a step (t + 1)).eval v = (step t).eval ((sequence a step t).eval v) := by
  rfl

/-- A uniform bound on the original expansions at every used stage also bounds
its chronological composite.
Source: polynomial-PEPS manuscript, Proposition 7.1, item 2,
`06-geometry.tex`, lines 25–32. -/
theorem isExpansionBounded_sequence (r : ℕ) (S : ℝ) (t : ℕ)
    (h : ∀ s < t, (step s).IsExpansionBounded r S) :
    (sequence a step t).IsExpansionBounded r S := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih fun s hs ↦ h s (by omega), h t (by omega)⟩

/-- Concatenating stages retains every nonprivate occurrence, including repeated
uses of the same local operator.
Source: polynomial-PEPS manuscript, Proposition 7.1, item 2,
`06-geometry.tex`, lines 25–32, and `04-compression.tex`, lines 140–142. -/
theorem nonprivateCount_sequence (t : ℕ) :
    (sequence a step t).nonprivateCount =
      ∑ s ∈ Finset.range t, (step s).nonprivateCount := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- A property of the participating set at every original occurrence is
preserved by concatenating the chronological stages.
Source: polynomial-PEPS manuscript, Proposition 7.1, items 2 and 3,
`06-geometry.tex`, lines 25–37. -/
theorem forall_participants_sequence (Q : Finset P → Prop) (t : ℕ)
    (h : ∀ s < t, ∀ g, Q ((step s).participants g)) :
    ∀ g, Q ((sequence a step t).participants g) := by
  induction t with
  | zero => exact fun g ↦ Empty.elim g
  | succ t ih =>
      rintro (g | g)
      · exact ih (fun s hs ↦ h s (by omega)) g
      · exact h t (by omega) g

/-- A uniform monomial-count bound at every used stage also bounds the actual
chronological composite.
Source: polynomial-PEPS manuscript, Proposition 7.1, item 2,
`06-geometry.tex`, lines 25–32. -/
theorem isMonomialBounded_sequence (K t : ℕ)
    (h : ∀ s < t, (step s).IsMonomialBounded K) :
    (sequence a step t).IsMonomialBounded K := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih fun s hs ↦ h s (by omega), h t (by omega)⟩

/-- Every occurrence involving a fixed party belongs to exactly one of the two
successive original circuits.
Source: polynomial-PEPS manuscript, Theorem 5.2, item 2,
`04-compression.tex`, lines 140–142 and 199–229. -/
theorem participationCount_comp {l₀ l₁ l₂ : Layout P}
    (w : OriginalCircuit l₀ l₁) (v : OriginalCircuit l₁ l₂) (p : P) :
    (w.comp v).participationCount p = w.participationCount p + v.participationCount p := by
  exact (Nat.card_congr (Equiv.subtypeSum
    (p := fun g : w.nonprivateLocations ⊕ v.nonprivateLocations ↦
      p ∈ (w.comp v).participants g))).trans Nat.card_sum

/-- A party's lifetime participation is the sum over the actual chronological
stages; occurrences are not identified when their local maps coincide.
Source: polynomial-PEPS manuscript, Proposition 7.1, item 2,
`06-geometry.tex`, lines 31–32, and Theorem 5.2, `04-compression.tex`, lines 140–142. -/
theorem participationCount_sequence (t : ℕ) (p : P) :
    (sequence a step t).participationCount p =
      ∑ s ∈ Finset.range t, (step s).participationCount p := by
  induction t with
  | zero => exact Nat.card_eq_zero.mpr (Or.inl ⟨fun g ↦ Empty.elim g.1⟩)
  | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact participationCount_comp (sequence a step t) (step t) p

end TNLean.PEPS.PairEffect.OriginalCircuit
