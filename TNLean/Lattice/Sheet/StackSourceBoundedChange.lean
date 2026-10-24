/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.OriginalCircuitSourceBound
import TNLean.Lattice.Sheet.StackChange

/-!
# Bounded changes of the sheet stack with bounded pair sources

Item 3 of Theorem 5.2 of the polynomial-PEPS manuscript asks for a constant bounding the number of
pair sources, pair effects and messages in each monomial of every gate (`04-compression.tex`,
lines 143–147). The protocol of Proposition 7.1 provides it through the counts of the step
theorems of its changes (`06-geometry.tex`, lines 572–583). This file carries the pair-source
bound `PartyCircuit.OriginalCircuit.IsSourceBounded` alongside the bounded changes of the sheets of
`TNLean.Lattice.Sheet.StackChange`, for sheets of an arbitrary type, each sheet `F` with
registers `regs F` and a reference vector `ref F`.

* `Lattice.HasSourceBoundedChange` : a bounded change of the sheets by a circuit with at most
  `rs` pair sources in each monomial.

Its closure properties are those of `Lattice.HasBoundedChange`: weaker bounds, reorderings of
the sheets, identity changes, and changes of one sheet or of two adjacent sheets lifted to the
whole stack.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 25–41 and 572–583; Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147.
-/

noncomputable section

namespace TNLean.Lattice

open TNLean.Lattice.PartyCircuit TNLean.Lattice.PartyCircuit.OriginalCircuit

variable {κ : Type*} {Party : Type}

section Lift

variable (regs : κ → Layout Party) {rs : ℕ}

theorem isSourceBounded_liftOne {F F' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F) (regs F')) (hc : c.IsSourceBounded rs) :
    (pre : List κ) → (liftOne regs post ℓ c pre).IsSourceBounded rs
  | [] => isSourceBounded_appendTail c _ hc
  | G :: pre => isSourceBounded_frameList _ (isSourceBounded_liftOne post ℓ c hc pre) (regs G)

theorem isSourceBounded_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')) (hc : c.IsSourceBounded rs) :
    (pre : List κ) → (liftTwo regs post ℓ c pre).IsSourceBounded rs
  | [] => isSourceBounded_castLayouts _ _ _ (isSourceBounded_appendTail c _ hc)
  | G :: pre => isSourceBounded_frameList _ (isSourceBounded_liftTwo post ℓ c hc pre) (regs G)

end Lift

section Stack

variable {regs : κ → Layout Party} (ref : (F : κ) → Mem (regs F))

/-- **A bounded change of the sheets with bounded pair sources.** There is an original circuit
from the registers of the sheets `Fs`, followed by the idle registers `ℓ`, to those of `Fs'`,
followed by `ℓ`, that is a bounded change from the reference vector of `Fs` with idle vector `ξ`
to that of `Fs'`, and that has at most `rs` pair sources in each monomial.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, items 2 and 4, `06-geometry.tex`,
lines 25–41 and 572–583; Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
def HasSourceBoundedChange (Fs Fs' : List κ) {ℓ : Layout Party} (ξ : Mem ℓ) (S : Set Party)
    (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∃ c : OriginalCircuit (stackRegs regs Fs ℓ) (stackRegs regs Fs' ℓ),
    c.IsBoundedChange S r K ε (stackVec ref Fs ξ) (stackVec ref Fs' ξ) ∧ c.IsSourceBounded rs

variable {ref} {Fs Fs' Gs : List κ} {ℓ : Layout Party} {ξ : Mem ℓ} {S S' : Set Party}
  {r r' K K' rs rs' : ℕ} {ε ε' : ℝ}

theorem HasSourceBoundedChange.hasBoundedChange
    (h : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε) : HasBoundedChange ref Fs Fs' ξ S r K ε :=
  let ⟨c, hc, _⟩ := h
  ⟨c, hc⟩

/-- A bounded change of the sheets with bounded pair sources stays so under weaker bounds. -/
theorem HasSourceBoundedChange.mono (h : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε)
    (hS : S ⊆ S') (hr : r ≤ r') (hK : K ≤ K') (hrs : rs ≤ rs') (hε : ε ≤ ε') :
    HasSourceBoundedChange ref Fs Fs' ξ S' r' K' rs' ε' :=
  let ⟨c, hc, hs⟩ := h
  ⟨c, hc.mono hS hr hK hε, hs.mono hrs⟩

/-- **Reordering the sheets.** A permutation of the sheets is a bounded change without
nonprivate gates, without error and without pair sources. -/
theorem hasSourceBoundedChange_of_perm (h : Fs.Perm Fs') (ξ : Mem ℓ) (S : Set Party)
    (r K rs : ℕ) (hε : 0 ≤ ε) : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε := by
  obtain ⟨c, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm ref h ℓ
  refine ⟨(OriginalCircuit.id _).comp c, ?_, trivial, isSourceBounded_of_nonprivateCount_eq_zero
    h0 rs⟩
  simpa [he] using (OriginalCircuit.isBoundedChange_id S r K hε (stackVec ref Fs ξ)).comp_right c
    h0 (hE r K) (hM K)

variable (ref) in
/-- The identity change of the sheets. -/
theorem hasSourceBoundedChange_refl (Fs : List κ) (ξ : Mem ℓ) (S : Set Party) (r K rs : ℕ)
    (hε : 0 ≤ ε) : HasSourceBoundedChange ref Fs Fs ξ S r K rs ε :=
  hasSourceBoundedChange_of_perm (List.Perm.refl Fs) ξ S r K rs hε

/-- A reordering of the sheets followed by a bounded change is a bounded change. -/
theorem HasSourceBoundedChange.perm_left (hp : Fs.Perm Gs)
    (h : HasSourceBoundedChange ref Gs Fs' ξ S r K rs ε) :
    HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm ref hp ℓ
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨e.comp c, hc.comp_left e h0 (hE r K) (hM K) (he ξ),
    isSourceBounded_of_nonprivateCount_eq_zero h0 rs, hs⟩

/-- A bounded change followed by a reordering of the sheets is a bounded change. -/
theorem HasSourceBoundedChange.perm_right (h : HasSourceBoundedChange ref Fs Gs ξ S r K rs ε)
    (hp : Gs.Perm Fs') : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm ref hp ℓ
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c.comp e, by simpa [he] using hc.comp_right e h0 (hE r K) (hM K),
    hs, isSourceBounded_of_nonprivateCount_eq_zero h0 rs⟩

/-- **A change of one sheet, on the whole stack.** A bounded change of the sheet `F` into `F'`
with at most `rs` pair sources in each monomial is such a change of `pre ++ F :: post` into
`pre ++ F' :: post`, when every reference vector and the idle vector have norm at most one.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasSourceBoundedChange_liftOne {F F' : κ} (pre post : List κ)
    {c : OriginalCircuit (regs F) (regs F')} (hc : c.IsBoundedChange S r K ε (ref F) (ref F'))
    (hs : c.IsSourceBounded rs) (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref (pre ++ F :: post) (pre ++ F' :: post) ξ S r K rs ε :=
  ⟨liftOne regs post ℓ c pre, isBoundedChange_liftOne pre post hc href hξ,
    isSourceBounded_liftOne regs post ℓ c hs pre⟩

/-- **A change of two adjacent sheets, on the whole stack.** A bounded change of the sheets
`F₁, F₂` into `F₁', F₂'` with at most `rs` pair sources in each monomial is such a change of
`pre ++ F₁ :: F₂ :: post` into `pre ++ F₁' :: F₂' :: post`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 389–430 and 574–583. -/
theorem hasSourceBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : κ} (pre post : List κ)
    {c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')}
    (hc : c.IsBoundedChange S r K ε (pairRef ref F₁ F₂) (pairRef ref F₁' F₂'))
    (hs : c.IsSourceBounded rs) (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref (pre ++ F₁ :: F₂ :: post) (pre ++ F₁' :: F₂' :: post) ξ S r K rs
      ε :=
  ⟨liftTwo regs post ℓ c pre, isBoundedChange_liftTwo pre post hc href hξ,
    isSourceBounded_liftTwo regs post ℓ c hs pre⟩

/-- **Activating an auxiliary sheet.** If the sheets `Fs` are a reordering of
`pre ++ F₁ :: F₂ :: post`, a bounded change of the two adjacent sheets with at most `rs` pair
sources in each monomial is such a change of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186, 389–430 and 658–667. -/
theorem hasSourceBoundedChange_activate {F₁ F₂ F₁' F₂' : κ} {pre post : List κ}
    (hp : Fs.Perm (pre ++ F₁ :: F₂ :: post))
    {c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')}
    (hc : c.IsBoundedChange S r K ε (pairRef ref F₁ F₂) (pairRef ref F₁' F₂'))
    (hs : c.IsSourceBounded rs) (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref Fs (pre ++ F₁' :: F₂' :: post) ξ S r K rs ε :=
  (hasSourceBoundedChange_liftTwo pre post hc hs href hξ).perm_left hp

/-- **A one-sheet change after a reordering.** If the sheets `Fs` are a reordering of
`pre ++ F :: post`, a bounded change of `F` with at most `rs` pair sources in each monomial is
such a change of `Fs`. -/
theorem hasSourceBoundedChange_perm_liftOne {F F' : κ} {pre post : List κ}
    (hp : Fs.Perm (pre ++ F :: post)) {c : OriginalCircuit (regs F) (regs F')}
    (hc : c.IsBoundedChange S r K ε (ref F) (ref F')) (hs : c.IsSourceBounded rs)
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref Fs (pre ++ F' :: post) ξ S r K rs ε :=
  (hasSourceBoundedChange_liftOne pre post hc hs href hξ).perm_left hp

end Stack

end TNLean.Lattice
