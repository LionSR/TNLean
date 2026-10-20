/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.ApproximateCircuitError
import TNLean.Lattice.PartyCircuit.OriginalProducerResources
import TNLean.Lattice.Sheet.StackChange
import TNLean.PEPS.Approximation.SampledOriginalCircuit
import TNLean.PEPS.Approximation.SheetStackReadoutCircuit
import TNLean.PEPS.Approximation.TwoSheetRegisters

/-!
# Bounded changes of the sheet stack

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every change of the memory
is a bounded number of gates: each change of the schedule has at most one nonprivate gate, whose
participants are parties its event uses, whose monomial expansion has polynomially many
monomials with polynomially bounded coefficients and a bounded number of pair effects, and which
takes the reference vector of the sheets within `C L⁻²⁰` of the next reference vector
(`06-geometry.tex`, lines 25–41 and 572–583).

The predicate and its closure properties hold for sheets of any type and are proved in
`TNLean.Lattice.Sheet.StackChange`, together with the predicate
`PairEffect.OriginalCircuit.IsBoundedChange` for one original circuit and the bounded words and
chains of the births, deaths and exchanges. This file reads them at the encoded frames, with
the reference vectors `Ω_F`:

* `EncodedFrame.HasBoundedChange` : a bounded change between two lists of encoded frames, followed
  by the same idle registers, from the reference vector of the first list to that of the second;
* its closure under reorderings, identity changes, lifted changes of one sheet or of two
  adjacent sheets, and the activation of an auxiliary sheet
  (`EncodedFrame.hasBoundedChange_of_perm`, `EncodedFrame.HasBoundedChange.perm_left`,
  `EncodedFrame.HasBoundedChange.perm_right`, `EncodedFrame.hasBoundedChange_liftOne`,
  `EncodedFrame.hasBoundedChange_liftTwo`, `EncodedFrame.hasBoundedChange_activate`);
* the reference vector of two sheets in the coordinates of the exchange
  (`EncodedFrame.pairRef_eq_twoLayoutIso_symm`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 25–41 (statement) and 572–583 (bounded gates and the precision of
  each change); original circuits, `04-compression.tex`, lines 21–43 and 199–208.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS

namespace EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ}

/-- **The reference vector of two sheets in the coordinates of the exchange.** The reference
vector of two frames on their concatenated registers is the product `Ω_{F₁} ⊗ Ω_{F₂}` read through
the coordinates of the two layouts. -/
theorem pairRef_eq_twoLayoutIso_symm (F₁ F₂ : Frame pos q Party)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    pairRef F₁ F₂ Ω = (twoLayoutIso F₁.holes F₂.holes F₁.owner F₂.owner).symm
      (EuclideanSpace.vecKron (F₁.refVec Ω) (F₂.refVec Ω)) := by
  rw [LinearIsometryEquiv.eq_symm_apply]
  change EuclideanSpace.pairIso _ _ ((layoutIso F₂.holes F₂.owner).lTensor _
      ((layoutIso F₁.holes F₁.owner).rTensor _ (appendIso _ _ ((appendIso _ _).symm
        (F₁.regRef Ω ⊗ₜ F₂.regRef Ω))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul]
  ext i
  simp [Frame.regRef, EuclideanSpace.vecKron]

/-! ### Bounded changes of the sheet stack -/

/-- **A bounded change of the sheets.** There is an original circuit from the registers of the
frames `Fs`, followed by the idle registers `ℓ`, to those of `Fs'`, followed by `ℓ`, that is a
bounded change, in the sense of `PairEffect.OriginalCircuit.IsBoundedChange`, from the reference
vector of `Fs` with idle vector `ξ` to that of `Fs'`. This is `Lattice.HasBoundedChange` at the
reference vectors `Ω_F` of the frames.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, items 2 and 4,
`06-geometry.tex`, lines 25–41, and lines 572–583. -/
def HasBoundedChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs Fs' : List (Frame pos q Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) (S : Set Party) (r K : ℕ) (ε : ℝ) : Prop :=
  ∃ c : OriginalCircuit (stackRegs Fs ℓ) (stackRegs Fs' ℓ),
    c.IsBoundedChange S r K ε (stackVec Ω Fs ξ) (stackVec Ω Fs' ξ)

variable {Ω : EuclideanSpace ℂ (ι → Fin q)} {Fs Fs' Gs : List (Frame pos q Party)}
  {ℓ : Layout Party} {ξ : Mem ℓ} {S S' : Set Party} {r r' K K' : ℕ} {ε ε' : ℝ}

/-- A bounded change of the sheets stays bounded under weaker bounds. -/
theorem HasBoundedChange.mono (h : HasBoundedChange Ω Fs Fs' ξ S r K ε) (hS : S ⊆ S')
    (hr : r ≤ r') (hK : K ≤ K') (hε : ε ≤ ε') : HasBoundedChange Ω Fs Fs' ξ S' r' K' ε' :=
  Lattice.HasBoundedChange.mono (ref := fun F : Frame pos q Party => F.regRef Ω) h hS hr hK hε

/-- **Reordering the sheets is a bounded change.** A permutation of the frames is a bounded change
without nonprivate gates and without error. -/
theorem hasBoundedChange_of_perm (h : Fs.Perm Fs') (ξ : Mem ℓ) (S : Set Party) (r K : ℕ)
    (hε : 0 ≤ ε) : HasBoundedChange Ω Fs Fs' ξ S r K ε :=
  Lattice.hasBoundedChange_of_perm (ref := fun F : Frame pos q Party => F.regRef Ω) h ξ S r K hε

/-- The identity change of the sheets. -/
theorem hasBoundedChange_refl (Fs : List (Frame pos q Party)) (ξ : Mem ℓ) (S : Set Party)
    (r K : ℕ) (hε : 0 ≤ ε) : HasBoundedChange Ω Fs Fs ξ S r K ε :=
  hasBoundedChange_of_perm (List.Perm.refl Fs) ξ S r K hε

/-- A reordering of the sheets followed by a bounded change is a bounded change. -/
theorem HasBoundedChange.perm_left (hp : Fs.Perm Gs) (h : HasBoundedChange Ω Gs Fs' ξ S r K ε) :
    HasBoundedChange Ω Fs Fs' ξ S r K ε :=
  Lattice.HasBoundedChange.perm_left (ref := fun F : Frame pos q Party => F.regRef Ω) hp h

/-- A bounded change followed by a reordering of the sheets is a bounded change. -/
theorem HasBoundedChange.perm_right (h : HasBoundedChange Ω Fs Gs ξ S r K ε) (hp : Gs.Perm Fs') :
    HasBoundedChange Ω Fs Fs' ξ S r K ε :=
  Lattice.HasBoundedChange.perm_right (ref := fun F : Frame pos q Party => F.regRef Ω) h hp

/-- The lift of a bounded change of one sheet to the stack. -/
theorem isBoundedChange_liftOne {F F' : Frame pos q Party} (pre post : List (Frame pos q Party))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    (liftOne post ℓ c pre).IsBoundedChange S r K ε (stackVec Ω (pre ++ F :: post) ξ)
      (stackVec Ω (pre ++ F' :: post) ξ) :=
  Lattice.isBoundedChange_liftOne (ref := fun F : Frame pos q Party => F.regRef Ω) pre post hc
    (fun F => F.norm_regRef_le hΩ) hξ

/-- **A change of one sheet, on the whole stack.** A bounded change of the frame `F` into `F'`,
from `Ω_F` to `Ω_{F'}`, is a bounded change of the stack `pre ++ F :: post` into
`pre ++ F' :: post`, with the same participants, bounds and error, when `‖Ω‖ ≤ 1` and the idle
vector has norm at most one.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasBoundedChange_liftOne {F F' : Frame pos q Party} (pre post : List (Frame pos q Party))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange Ω (pre ++ F :: post) (pre ++ F' :: post) ξ S r K ε :=
  ⟨liftOne post ℓ c pre, isBoundedChange_liftOne pre post hc hΩ hξ⟩

/-- The lift of a bounded change of two adjacent sheets to the stack. -/
theorem isBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (pre post : List (Frame pos q Party))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω)) (hΩ : ‖Ω‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) :
    (liftTwo post ℓ c pre).IsBoundedChange S r K ε (stackVec Ω (pre ++ F₁ :: F₂ :: post) ξ)
      (stackVec Ω (pre ++ F₁' :: F₂' :: post) ξ) :=
  Lattice.isBoundedChange_liftTwo (ref := fun F : Frame pos q Party => F.regRef Ω) pre post hc
    (fun F => F.norm_regRef_le hΩ) hξ

/-- **A change of two adjacent sheets, on the whole stack.** A bounded change of the frames
`F₁, F₂` into `F₁', F₂'`, from `Ω_{F₁} ⊗ Ω_{F₂}` to `Ω_{F₁'} ⊗ Ω_{F₂'}`, is a bounded change of
the stack `pre ++ F₁ :: F₂ :: post` into `pre ++ F₁' :: F₂' :: post`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 389–430 and 574–583. -/
theorem hasBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (pre post : List (Frame pos q Party))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω)) (hΩ : ‖Ω‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange Ω (pre ++ F₁ :: F₂ :: post) (pre ++ F₁' :: F₂' :: post) ξ S r K ε :=
  ⟨liftTwo post ℓ c pre, isBoundedChange_liftTwo pre post hc hΩ hξ⟩

/-- **Activating an auxiliary sheet.** If the frames `Fs` are a reordering of
`pre ++ F₁ :: F₂ :: post`, for instance with an idle auxiliary copy `F₂` moved next to the main
sheet `F₁`, then a bounded change of the two adjacent sheets is a bounded change of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186, 389–430 and 658–667. -/
theorem hasBoundedChange_activate {F₁ F₂ F₁' F₂' : Frame pos q Party}
    {pre post : List (Frame pos q Party)} (hp : Fs.Perm (pre ++ F₁ :: F₂ :: post))
    {c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω)) (hΩ : ‖Ω‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) : HasBoundedChange Ω Fs (pre ++ F₁' :: F₂' :: post) ξ S r K ε :=
  (hasBoundedChange_liftTwo pre post hc hΩ hξ).perm_left hp

/-- **A one-sheet change after a reordering.** If the frames `Fs` are a reordering of
`pre ++ F :: post`, a bounded change of `F` is a bounded change of `Fs`. -/
theorem hasBoundedChange_perm_liftOne {F F' : Frame pos q Party}
    {pre post : List (Frame pos q Party)} (hp : Fs.Perm (pre ++ F :: post))
    {c : OriginalCircuit F.regs F'.regs} (hc : c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω))
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) : HasBoundedChange Ω Fs (pre ++ F' :: post) ξ S r K ε :=
  (hasBoundedChange_liftOne pre post hc hΩ hξ).perm_left hp

/-- **An unchanged sheet.** If the frame does not change, as for a birth or death with empty
target or the resize of a hole whose radius does not change, the identity change of the frame is a
bounded change for every set of participants and all bounds.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_isBoundedChange_of_frame_eq {F F' : Frame pos q Party} (h : F = F') (S : Set Party)
    (r K : ℕ) (hε : 0 ≤ ε) :
    ∃ c : OriginalCircuit F.regs F'.regs, c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω) :=
  Lattice.exists_isBoundedChange_of_eq (fun F : Frame pos q Party => F.regRef Ω) h S r K hε

end EncodedFrame

end TNLean.PEPS
