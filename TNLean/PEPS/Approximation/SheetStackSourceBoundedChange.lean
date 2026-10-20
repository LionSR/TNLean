/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.OriginalCircuitSourceBound
import TNLean.PEPS.Approximation.SheetStackChange

/-!
# Bounded changes of the sheet stack with bounded pair sources

Item 3 of Theorem 5.2 of the polynomial-PEPS manuscript asks for a constant bounding the number of
pair sources, pair effects and messages in each monomial of every gate (`04-compression.tex`,
lines 143–147). The protocol of Proposition 7.1 provides it through the counts of the step
theorems of its changes (`06-geometry.tex`, lines 572–583). This file carries the pair-source
bound `PairEffect.OriginalCircuit.IsSourceBounded` alongside the bounded changes of the sheets of
`TNLean.PEPS.Approximation.SheetStackChange`.

* `EncodedFrame.HasSourceBoundedChange` : a bounded change of the sheets by a circuit with at most
  `rs` pair sources in each monomial.

Its closure properties are those of `EncodedFrame.HasBoundedChange`: weaker bounds, reorderings of
the sheets, identity changes, and changes of one sheet or of two adjacent sheets lifted to the
whole stack.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 25–41 and 572–583; Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open PairEffect PairEffect.OriginalCircuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ}

/-- **A bounded change of the sheets with bounded pair sources.** There is an original circuit
from the registers of the frames `Fs`, followed by the idle registers `ℓ`, to those of `Fs'`,
followed by `ℓ`, that is a bounded change from the reference vector of `Fs` with idle vector `ξ`
to that of `Fs'`, and that has at most `rs` pair sources in each monomial.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, items 2 and 4, `06-geometry.tex`,
lines 25–41 and 572–583; Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
def HasSourceBoundedChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs Fs' : List (Frame pos q Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) (S : Set Party) (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∃ c : OriginalCircuit (stackRegs Fs ℓ) (stackRegs Fs' ℓ),
    c.IsBoundedChange S r K ε (stackVec Ω Fs ξ) (stackVec Ω Fs' ξ) ∧ c.IsSourceBounded rs

variable {Ω : EuclideanSpace ℂ (ι → Fin q)} {Fs Fs' Gs : List (Frame pos q Party)}
  {ℓ : Layout Party} {ξ : Mem ℓ} {S S' : Set Party} {r r' K K' rs rs' : ℕ} {ε ε' : ℝ}

theorem HasSourceBoundedChange.hasBoundedChange
    (h : HasSourceBoundedChange Ω Fs Fs' ξ S r K rs ε) : HasBoundedChange Ω Fs Fs' ξ S r K ε :=
  let ⟨c, hc, _⟩ := h
  ⟨c, hc⟩

/-- A bounded change of the sheets with bounded pair sources stays so under weaker bounds. -/
theorem HasSourceBoundedChange.mono (h : HasSourceBoundedChange Ω Fs Fs' ξ S r K rs ε)
    (hS : S ⊆ S') (hr : r ≤ r') (hK : K ≤ K') (hrs : rs ≤ rs') (hε : ε ≤ ε') :
    HasSourceBoundedChange Ω Fs Fs' ξ S' r' K' rs' ε' :=
  let ⟨c, hc, hs⟩ := h
  ⟨c, hc.mono hS hr hK hε, hs.mono hrs⟩

/-- **Reordering the sheets.** A permutation of the frames is a bounded change without
nonprivate gates, without error and without pair sources. -/
theorem hasSourceBoundedChange_of_perm (h : Fs.Perm Fs') (ξ : Mem ℓ) (S : Set Party) (r K rs : ℕ)
    (hε : 0 ≤ ε) : HasSourceBoundedChange Ω Fs Fs' ξ S r K rs ε := by
  obtain ⟨c, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω h ℓ
  refine ⟨(OriginalCircuit.id _).comp c, ?_, trivial, isSourceBounded_of_nonprivateCount_eq_zero
    h0 rs⟩
  simpa [he] using (OriginalCircuit.isBoundedChange_id S r K hε (stackVec Ω Fs ξ)).comp_right c
    h0 (hE r K) (hM K)

/-- The identity change of the sheets. -/
theorem hasSourceBoundedChange_refl (Fs : List (Frame pos q Party)) (ξ : Mem ℓ) (S : Set Party)
    (r K rs : ℕ) (hε : 0 ≤ ε) : HasSourceBoundedChange Ω Fs Fs ξ S r K rs ε :=
  hasSourceBoundedChange_of_perm (List.Perm.refl Fs) ξ S r K rs hε

/-- A reordering of the sheets followed by a bounded change is a bounded change. -/
theorem HasSourceBoundedChange.perm_left (hp : Fs.Perm Gs)
    (h : HasSourceBoundedChange Ω Gs Fs' ξ S r K rs ε) :
    HasSourceBoundedChange Ω Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω hp ℓ
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨e.comp c, hc.comp_left e h0 (hE r K) (hM K) (he ξ),
    isSourceBounded_of_nonprivateCount_eq_zero h0 rs, hs⟩

/-- A bounded change followed by a reordering of the sheets is a bounded change. -/
theorem HasSourceBoundedChange.perm_right (h : HasSourceBoundedChange Ω Fs Gs ξ S r K rs ε)
    (hp : Gs.Perm Fs') : HasSourceBoundedChange Ω Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, h0, -, hE, hM, he⟩ := exists_originalCircuit_stackVec_of_perm Ω hp ℓ
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c.comp e, by simpa [he] using hc.comp_right e h0 (hE r K) (hM K),
    hs, isSourceBounded_of_nonprivateCount_eq_zero h0 rs⟩

omit [NeZero q] in
theorem isSourceBounded_liftOne {F F' : Frame pos q Party} (post : List (Frame pos q Party))
    (ℓ : Layout Party) (c : OriginalCircuit F.regs F'.regs) (hc : c.IsSourceBounded rs) :
    (pre : List (Frame pos q Party)) → (liftOne post ℓ c pre).IsSourceBounded rs
  | [] => isSourceBounded_appendTail c _ hc
  | G :: pre => isSourceBounded_frameList _ (isSourceBounded_liftOne post ℓ c hc pre) G.regs

omit [NeZero q] in
theorem isSourceBounded_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party)
    (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)) (hc : c.IsSourceBounded rs) :
    (pre : List (Frame pos q Party)) → (liftTwo post ℓ c pre).IsSourceBounded rs
  | [] => isSourceBounded_castLayouts _ _ _ (isSourceBounded_appendTail c _ hc)
  | G :: pre => isSourceBounded_frameList _ (isSourceBounded_liftTwo post ℓ c hc pre) G.regs

/-- **A change of one sheet, on the whole stack.** A bounded change of the frame `F` into `F'` with
at most `rs` pair sources in each monomial is such a change of `pre ++ F :: post` into
`pre ++ F' :: post`, when `‖Ω‖ ≤ 1` and the idle vector has norm at most one.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasSourceBoundedChange_liftOne {F F' : Frame pos q Party}
    (pre post : List (Frame pos q Party)) {c : OriginalCircuit F.regs F'.regs}
    (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω)) (hs : c.IsSourceBounded rs)
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (pre ++ F :: post) (pre ++ F' :: post) ξ S r K rs ε :=
  ⟨liftOne post ℓ c pre, isBoundedChange_liftOne pre post hc hΩ hξ,
    isSourceBounded_liftOne post ℓ c hs pre⟩

/-- **A change of two adjacent sheets, on the whole stack.** A bounded change of the frames
`F₁, F₂` into `F₁', F₂'` with at most `rs` pair sources in each monomial is such a change of
`pre ++ F₁ :: F₂ :: post` into `pre ++ F₁' :: F₂' :: post`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 389–430 and 574–583. -/
theorem hasSourceBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (pre post : List (Frame pos q Party))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω))
    (hs : c.IsSourceBounded rs) (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (pre ++ F₁ :: F₂ :: post) (pre ++ F₁' :: F₂' :: post) ξ S r K rs ε :=
  ⟨liftTwo post ℓ c pre, isBoundedChange_liftTwo pre post hc hΩ hξ,
    isSourceBounded_liftTwo post ℓ c hs pre⟩

/-- **Activating an auxiliary sheet.** If the frames `Fs` are a reordering of
`pre ++ F₁ :: F₂ :: post`, a bounded change of the two adjacent sheets with at most `rs` pair
sources in each monomial is such a change of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186, 389–430 and 658–667. -/
theorem hasSourceBoundedChange_activate {F₁ F₂ F₁' F₂' : Frame pos q Party}
    {pre post : List (Frame pos q Party)} (hp : Fs.Perm (pre ++ F₁ :: F₂ :: post))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω))
    (hs : c.IsSourceBounded rs) (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω Fs (pre ++ F₁' :: F₂' :: post) ξ S r K rs ε :=
  (hasSourceBoundedChange_liftTwo pre post hc hs hΩ hξ).perm_left hp

/-- **A one-sheet change after a reordering.** If the frames `Fs` are a reordering of
`pre ++ F :: post`, a bounded change of `F` with at most `rs` pair sources in each monomial is
such a change of `Fs`. -/
theorem hasSourceBoundedChange_perm_liftOne {F F' : Frame pos q Party}
    {pre post : List (Frame pos q Party)} (hp : Fs.Perm (pre ++ F :: post))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hs : c.IsSourceBounded rs) (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω Fs (pre ++ F' :: post) ξ S r K rs ε :=
  (hasSourceBoundedChange_liftOne pre post hc hs hΩ hξ).perm_left hp

end TNLean.PEPS.EncodedFrame
