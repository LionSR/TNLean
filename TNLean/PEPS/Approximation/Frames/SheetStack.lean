/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.Initialization
import TNLean.PEPS.Approximation.Frames.FrameRegisters

/-!
# The memory of several encoded frames

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds several
sheets: the main sheet, the active auxiliary sheet of the current repainting, the frozen
auxiliary sheets of earlier repaintings, and the auxiliary copies of `Ω` not yet in use, each
held privately by the party that will initialize it. The reference vector at each stage is the
tensor product of the reference vectors `Ω_F` of the encoded frames of the sheets and of the
idle copies, every factor of norm at most one (`06-geometry.tex`, lines 39–41 and 658–667).

The stack calculus is developed for an arbitrary type of sheets in
`QuantumCircuit.Party` (`stackSystem`, `stackVec`, `liftOne`, `liftTwo`). This file reads it at
the encoded frames, each frame `F` carrying its registers `F.system` and the reference vector
`F.regRef Ω` of `Ω_F` on them: a list of frames followed by an idle system `W` has the registers
`framesSystem Fs W`, and the reference vector `stackRef Ω Fs ξ`, the product of the frame
reference vectors with a vector `ξ` of the idle system.

A bounded change acts on one sheet (a small-patch rewrite, a birth or a death) or on two
adjacent sheets (the lens exchange). Lifting the change to the whole stack, with the other
sheets as spectators (`QuantumCircuit.Party.liftOne`, `QuantumCircuit.Party.liftTwo`), changes
neither its gates nor its participants, and its reference error on the stack is at most its
reference error on the frames it acts on, because the spectator factors have norm at most one
(`EncodedFrame.norm_op_liftOne_stackRef_sub_le`, `EncodedFrame.norm_op_liftTwo_stackRef_sub_le`).

## Main definitions

* `EncodedFrame.framesSystem`, `EncodedFrame.stackRef`, `EncodedFrame.framesRef`,
  `EncodedFrame.pairRef`.

## Main results

* `EncodedFrame.norm_stackRef` : the norm of the reference vector is the product of the norms of
  its factors.
* `EncodedFrame.norm_op_liftOne_stackRef_sub_le`, `EncodedFrame.norm_op_liftTwo_stackRef_sub_le`:
  the reference error of a lifted change.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 39–41 (the reference vectors as products of frame vectors) and
  658–667 (initialization and the reference vectors); encoded frames, `05-frames.tex`,
  lines 71–96.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} [DecidableEq Party]
  {pos : ι → ℝ × ℝ}

/-! ### Registers of several sheets -/

variable (q pos) in
/-- The registers of a list of frames, in order, followed by an idle system `W`: at every party,
the product of its registers on the frames and of its idle basis. -/
abbrev framesSystem (Fs : List (Frame pos q Party)) (W : Party → Type) : Party → Type :=
  stackSystem Frame.system Fs W

/-! ### Reference vectors -/

section Reference

variable [Fintype Party] [NeZero q]

/-- The product of the reference vectors of a list of frames with a vector `ξ` of an idle system.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41. -/
abbrev stackRef (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party))
    {W : Party → Type} [∀ p, Fintype (W p)] (ξ : EuclideanSpace ℂ (Config W)) :
    EuclideanSpace ℂ (Config (framesSystem q pos Fs W)) :=
  stackVec (fun F : Frame pos q Party ↦ F.regRef Ω) Fs ξ

/-- The reference vector of a list of frames, with the trivial idle system. -/
abbrev framesRef (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party)) :
    EuclideanSpace ℂ (Config (framesSystem q pos Fs fun _ ↦ Unit)) :=
  framesVec (fun F : Frame pos q Party ↦ F.regRef Ω) Fs

/-- The reference vector of two frames on the product of their registers. -/
abbrev pairRef (F₁ F₂ : Frame pos q Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    EuclideanSpace ℂ (Config fun p ↦ F₁.system p × F₂.system p) :=
  prodVec (F₁.regRef Ω) (F₂.regRef Ω)

/-- The norm of the reference vector of several sheets is the product of the norms of the frame
reference vectors and of the idle vector. -/
theorem norm_stackRef (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party))
    {W : Party → Type} [∀ p, Fintype (W p)] (ξ : EuclideanSpace ℂ (Config W)) :
    ‖stackRef Ω Fs ξ‖ = (Fs.map fun F ↦ ‖F.refVec Ω‖).prod * ‖ξ‖ := by
  rw [stackRef, norm_stackVec]
  simp only [Frame.norm_regRef]

/-- Every factor of the reference vector of several sheets has norm at most one. -/
theorem norm_stackRef_le {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (Fs : List (Frame pos q Party)) {W : Party → Type} [∀ p, Fintype (W p)]
    (ξ : EuclideanSpace ℂ (Config W)) : ‖stackRef Ω Fs ξ‖ ≤ ‖ξ‖ :=
  norm_stackVec_le (fun F ↦ F.norm_regRef_le hΩ) ξ Fs

variable {W : Party → Type} [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- **The reference error of a change of one sheet.** On the whole stack, the change takes the
reference vector within the error it makes on its own sheet.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_op_liftOne_stackRef_sub_le {F F' : Frame pos q Party}
    (post : List (Frame pos q Party)) (c : OriginalCircuit F.system F'.system)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) {ξ : EuclideanSpace ℂ (Config W)}
    (hξ : ‖ξ‖ ≤ 1) (pre : List (Frame pos q Party)) :
    ‖Matrix.toEuclideanLin (liftOne Frame.system W post c pre).op
        (stackRef Ω (pre ++ F :: post) ξ) - stackRef Ω (pre ++ F' :: post) ξ‖ ≤
      ‖Matrix.toEuclideanLin c.op (F.regRef Ω) - F'.regRef Ω‖ :=
  QuantumCircuit.Party.norm_op_liftOne_stackVec_sub_le W post c
    (fun F ↦ F.norm_regRef_le hΩ) hξ pre

/-- **The reference error of a change of two adjacent sheets.** On the whole stack, the change
takes the reference vector within the error it makes on its two sheets.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_op_liftTwo_stackRef_sub_le {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party))
    (c : OriginalCircuit (fun p ↦ F₁.system p × F₂.system p)
      (fun p ↦ F₁'.system p × F₂'.system p))
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) {ξ : EuclideanSpace ℂ (Config W)}
    (hξ : ‖ξ‖ ≤ 1) (pre : List (Frame pos q Party)) :
    ‖Matrix.toEuclideanLin (liftTwo Frame.system W post c pre).op
        (stackRef Ω (pre ++ F₁ :: F₂ :: post) ξ) - stackRef Ω (pre ++ F₁' :: F₂' :: post) ξ‖ ≤
      ‖Matrix.toEuclideanLin c.op (pairRef F₁ F₂ Ω) - pairRef F₁' F₂' Ω‖ :=
  QuantumCircuit.Party.norm_op_liftTwo_stackVec_sub_le W post c
    (fun F ↦ F.norm_regRef_le hΩ) hξ pre

end Reference

end TNLean.PEPS.EncodedFrame
