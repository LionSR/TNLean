/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalCircuitLift

/-!
# Pair sources in the gate expansions of an original circuit

The third assumption of Theorem 5.2 of the polynomial-PEPS manuscript bounds, by one constant
`r`, the number of pair sources, pair effects and polynomial-dimensional messages in every
monomial of every nonprivate gate expansion. The pair-effect bound is part of
`OriginalCircuit.IsExpansionBounded`, and messages are expanded before a gate is read as an
original gate (`MessageGate.toOriginalCircuit`). This file adds the pair-source bound
`OriginalCircuit.IsSourceBounded r`.

It is preserved by composition, framing, the exchanges of tensor factors placed around a circuit
and the identification of equal layouts, and it holds with every constant for a circuit without
nonprivate gates. A source-only word or an allowed monomial read operation by operation
(`Word.toOriginalCircuit`, `PartyChain.toOriginalCircuit`) has one monomial per gate, with at most
one pair source.

## Main definitions

* `PairEffect.OriginalCircuit.IsSourceBounded`.

## Main results

* `PairEffect.OriginalCircuit.IsSourceBounded.mono`,
  `PairEffect.OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero`.
* `PairEffect.OriginalCircuit.isSourceBounded_castLayouts`,
  `PairEffect.OriginalCircuit.isSourceBounded_frameList`,
  `PairEffect.OriginalCircuit.isSourceBounded_appendTail`.
* `PairEffect.Word.isSourceBounded_toOriginalCircuit`,
  `PairEffect.PartyChain.isSourceBounded_toOriginalCircuit` and their forms
  `_of_one_le` for every positive constant.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2 `thm:compression`, item 3,
  `04-compression.tex`, lines 143–147; allowed monomials and messages, lines 21–43.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace OriginalCircuit

/-- Every monomial of every nonprivate gate expansion has at most `r` pair sources.

Polynomial-PEPS manuscript, Theorem 5.2, item 3, `04-compression.tex`, lines 143–147: “There is
a constant `r` bounding the number of pair sources, pair effects, and polynomial-dimensional
messages in each monomial.” -/
def IsSourceBounded (r : ℕ) : {a b : Layout P} → OriginalCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsSourceBounded r ∧ v.IsSourceBounded r
  | _, _, .privateMap .. => True
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ L _ _ _ => ∀ m ∈ L, m.2.sourceCount ≤ r
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsSourceBounded r

/-- A larger constant bounds the pair sources as well. -/
theorem IsSourceBounded.mono {a b : Layout P} {w : OriginalCircuit a b} {r r' : ℕ}
    (h : w.IsSourceBounded r) (hr : r ≤ r') : w.IsSourceBounded r' := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | privateMap => trivial
  | nonprivateGate => exact fun m hm => (h m hm).trans hr
  | swap => trivial
  | frame _ w ih => exact ih h

/-- A circuit without nonprivate gates satisfies the pair-source bound with every constant. -/
theorem isSourceBounded_of_nonprivateCount_eq_zero {a b : Layout P} {w : OriginalCircuit a b}
    (h0 : w.nonprivateCount = 0) (r : ℕ) : w.IsSourceBounded r := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      simp only [nonprivateCount, Nat.add_eq_zero_iff] at h0
      exact ⟨ihw h0.1, ihv h0.2⟩
  | privateMap => trivial
  | nonprivateGate => exact absurd h0 one_ne_zero
  | swap => trivial
  | frame _ w ih => exact ih h0

theorem isSourceBounded_castLayouts {a b a' b' : Layout P} (c : OriginalCircuit a b)
    (ha : a = a') (hb : b = b') {r : ℕ} (hc : c.IsSourceBounded r) :
    (c.castLayouts ha hb).IsSourceBounded r :=
  castLayouts_rec c ha hb (motive := fun w ↦ w.IsSourceBounded r) hc

theorem isSourceBounded_frameList {a b : Layout P} (c : OriginalCircuit a b) {r : ℕ}
    (hc : c.IsSourceBounded r) : (rs : Layout P) → (frameList rs c).IsSourceBounded r
  | [] => hc
  | _ :: rs => isSourceBounded_frameList c hc rs

theorem isSourceBounded_appendTail {a b : Layout P} (c : OriginalCircuit a b) (t : Layout P)
    {r : ℕ} (hc : c.IsSourceBounded r) : (c.appendTail t).IsSourceBounded r :=
  ⟨isSourceBounded_of_nonprivateCount_eq_zero
      (Word.nonprivateCount_toOriginalCircuit_of_isReordering (Word.isReordering_exchangeTwo a t))
      r,
    isSourceBounded_frameList c hc t,
    isSourceBounded_of_nonprivateCount_eq_zero
      (Word.nonprivateCount_toOriginalCircuit_of_isReordering (Word.isReordering_exchangeTwo t b))
      r⟩

end OriginalCircuit

/-- Each nonprivate gate of the circuit of a source-only word is a single pair source.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43 and 143–147. -/
theorem Word.isSourceBounded_toOriginalCircuit {a b : Layout P} (w : Word a b)
    (hw : w.IsAllowed) : (w.toOriginalCircuit hw).IsSourceBounded 1 := by
  induction w with
  | id => trivial
  | comp w w' ih ih' => exact ⟨ih hw.1, ih' hw.2⟩
  | localMap => trivial
  | source =>
      intro m hm
      rw [List.mem_singleton] at hm
      subst hm
      exact le_rfl
  | swap => trivial
  | frame r w ih => exact ih hw

/-- Each nonprivate gate of the circuit of an allowed monomial is a single pair source or a
single pair effect, so it has at most one pair source.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43 and 143–147. -/
theorem PartyChain.isSourceBounded_toOriginalCircuit {a b : Layout P} (M : PartyChain a b)
    (hM : M.IsAllowed) : (M.toOriginalCircuit hM).IsSourceBounded 1 := by
  induction M with
  | final w => exact w.isSourceBounded_toOriginalCircuit hM
  | effect hpq α β ℓS w η rest ih =>
      refine ⟨w.isSourceBounded_toOriginalCircuit hM.1, fun m hm => ?_, ih hM.2.2⟩
      rw [List.mem_singleton] at hm
      subst hm
      exact Nat.zero_le 1

/-- The circuit of a source-only word satisfies the pair-source bound with every positive
constant, as the gates of the bulk births of Proposition 7.1 do.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 143–147. -/
theorem Word.isSourceBounded_toOriginalCircuit_of_one_le {a b : Layout P} (w : Word a b)
    (hw : w.IsAllowed) {r : ℕ} (hr : 1 ≤ r) : (w.toOriginalCircuit hw).IsSourceBounded r :=
  (w.isSourceBounded_toOriginalCircuit hw).mono hr

/-- The circuit of an allowed monomial satisfies the pair-source bound with every positive
constant, as the gates of the bulk deaths of Proposition 7.1 do.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 143–147. -/
theorem PartyChain.isSourceBounded_toOriginalCircuit_of_one_le {a b : Layout P}
    (M : PartyChain a b) (hM : M.IsAllowed) {r : ℕ} (hr : 1 ≤ r) :
    (M.toOriginalCircuit hM).IsSourceBounded r :=
  (M.isSourceBounded_toOriginalCircuit hM).mono hr

end TNLean.PEPS.PairEffect
