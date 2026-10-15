/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameRegisters
import TNLean.PEPS.Approximation.LayoutEqualityCoordinates
import TNLean.PEPS.Approximation.OriginalCircuitLift

/-!
# The memory of several sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds several
sheets: the main sheet, the active auxiliary sheet of the current repainting, the frozen
auxiliary sheets of earlier repaintings, and the auxiliary copies of `Ω` not yet in use, each
held privately by the party that will initialize it. The reference vector at each stage is the
tensor product of the reference vectors `Ω_F` of the encoded frames of the sheets and of the
idle copies, every factor of norm at most one (`06-geometry.tex`, lines 39–41 and 658–667).

A *sheet stack* (`EncodedFrame.SheetStack`) is a list of encoded frames followed by a layout of
idle registers. Its registers are the registers of the frames, in order, followed by the idle
registers (`SheetStack.regs`), and its reference vector is the product of the frame reference
vectors and of a vector of the idle registers (`SheetStack.refVec`).

A bounded change acts on one sheet (a small-patch rewrite, a birth or a death) or on two
adjacent sheets (the lens exchange). Lifting the change to the whole stack, with the other
sheets as spectators (`SheetStack.liftOne`, `SheetStack.liftTwo`), changes neither its gates
nor its participants, and its reference error on the stack is at most its reference error on
the frames it acts on, because the spectator factors have norm at most one
(`SheetStack.norm_eval_liftOne_refVec_sub_le`, `SheetStack.norm_eval_liftTwo_refVec_sub_le`).

## Main definitions

* `EncodedFrame.Frame.regRef` : the reference vector of a frame on its registers.
* `EncodedFrame.stackRegs`, `EncodedFrame.stackVec` : the registers and the reference vector of
  a list of frames before a layout.
* `EncodedFrame.SheetStack`, `EncodedFrame.SheetStack.regs`, `EncodedFrame.SheetStack.refVec`.
* `EncodedFrame.liftOne`, `EncodedFrame.liftTwo` : a change of one sheet or of two adjacent
  sheets, on the whole stack.

## Main results

* `EncodedFrame.norm_stackVec` : the norm of the reference vector is the product of the norms of
  its factors.
* `EncodedFrame.norm_eval_liftOne_stackVec_sub_le`,
  `EncodedFrame.norm_eval_liftTwo_stackVec_sub_le` : the reference error of a lifted change.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 39–41 (the reference vectors as products of frame vectors) and
  658–667 (initialization and the reference vectors); encoded frames, `05-frames.tex`,
  lines 71–96.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} {pos : ι → ℝ × ℝ}

/-! ### Registers of several sheets -/

/-- The registers of a list of frames, in order, followed by the layout `ℓ`. -/
@[reducible] def stackRegs : List (Frame pos q Party) → Layout Party → Layout Party
  | [], ℓ => ℓ
  | F :: Fs, ℓ => F.regs ++ stackRegs Fs ℓ

/-- **Sheet stacks.** The memory of several sheets: encoded frames, in order, followed by idle
registers. Polynomial-PEPS manuscript, Proposition 7.1, `06-geometry.tex`, lines 21–23, 39–41
and 658–667. -/
structure SheetStack (pos : ι → ℝ × ℝ) (q : ℕ) (Party : Type) where
  /-- The encoded frames of the sheets. -/
  frames : List (Frame pos q Party)
  /-- The idle registers, such as auxiliary copies not yet in use. -/
  idle : Layout Party

namespace SheetStack

/-- The registers of a sheet stack. -/
abbrev regs (S : SheetStack pos q Party) : Layout Party := stackRegs S.frames S.idle

end SheetStack

/-! ### A change of one sheet -/

/-- A change of the sheet `F` into `F'` on the whole stack `pre ++ F :: post`, with the other
sheets and the layout `ℓ` as spectators. -/
def liftOne {F F' : Frame pos q Party} (post : List (Frame pos q Party)) (ℓ : Layout Party)
    (c : OriginalCircuit F.regs F'.regs) :
    (pre : List (Frame pos q Party)) →
      OriginalCircuit (stackRegs (pre ++ F :: post) ℓ) (stackRegs (pre ++ F' :: post) ℓ)
  | [] => c.appendTail (stackRegs post ℓ)
  | G :: pre => OriginalCircuit.frameList G.regs (liftOne post ℓ c pre)

@[simp] theorem nonprivateCount_liftOne {F F' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party) (c : OriginalCircuit F.regs F'.regs) :
    (pre : List (Frame pos q Party)) → (liftOne post ℓ c pre).nonprivateCount = c.nonprivateCount
  | [] => OriginalCircuit.nonprivateCount_appendTail c _
  | G :: pre => (OriginalCircuit.nonprivateCount_frameList _ G.regs).trans
      (nonprivateCount_liftOne post ℓ c pre)

theorem participants_liftOne_subset {S : Set Party} {F F' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party) (c : OriginalCircuit F.regs F'.regs)
    (hc : ∀ g, (↑(c.participants g) : Set Party) ⊆ S) :
    (pre : List (Frame pos q Party)) → (g : (liftOne post ℓ c pre).nonprivateLocations) →
      (↑((liftOne post ℓ c pre).participants g) : Set Party) ⊆ S
  | [], g => OriginalCircuit.participants_appendTail_subset c _ hc g
  | G :: pre, g => OriginalCircuit.participants_frameList_subset _
      (participants_liftOne_subset post ℓ c hc pre) G.regs g

theorem isExpansionBounded_liftOne {F F' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party) (c : OriginalCircuit F.regs F'.regs)
    {r : ℕ} {s : ℝ} (hc : c.IsExpansionBounded r s) :
    (pre : List (Frame pos q Party)) → (liftOne post ℓ c pre).IsExpansionBounded r s
  | [] => OriginalCircuit.isExpansionBounded_appendTail c _ hc
  | G :: pre => OriginalCircuit.isExpansionBounded_frameList _
      (isExpansionBounded_liftOne post ℓ c hc pre) G.regs

theorem isMonomialBounded_liftOne {F F' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party) (c : OriginalCircuit F.regs F'.regs)
    {K : ℕ} (hc : c.IsMonomialBounded K) :
    (pre : List (Frame pos q Party)) → (liftOne post ℓ c pre).IsMonomialBounded K
  | [] => OriginalCircuit.isMonomialBounded_appendTail c _ hc
  | G :: pre => OriginalCircuit.isMonomialBounded_frameList _
      (isMonomialBounded_liftOne post ℓ c hc pre) G.regs

/-! ### A change of two adjacent sheets -/

/-- A change of the adjacent sheets `F₁, F₂` into `F₁', F₂'` on the whole stack
`pre ++ F₁ :: F₂ :: post`, with the other sheets and the layout `ℓ` as spectators. -/
def liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party} (post : List (Frame pos q Party))
    (ℓ : Layout Party) (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)) :
    (pre : List (Frame pos q Party)) →
      OriginalCircuit (stackRegs (pre ++ F₁ :: F₂ :: post) ℓ)
        (stackRegs (pre ++ F₁' :: F₂' :: post) ℓ)
  | [] => (c.appendTail (stackRegs post ℓ)).castLayouts (List.append_assoc _ _ _)
      (List.append_assoc _ _ _)
  | G :: pre => OriginalCircuit.frameList G.regs (liftTwo post ℓ c pre)

@[simp] theorem nonprivateCount_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party)
    (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)) :
    (pre : List (Frame pos q Party)) → (liftTwo post ℓ c pre).nonprivateCount = c.nonprivateCount
  | [] => (OriginalCircuit.nonprivateCount_castLayouts _ _ _).trans
      (OriginalCircuit.nonprivateCount_appendTail c _)
  | G :: pre => (OriginalCircuit.nonprivateCount_frameList _ G.regs).trans
      (nonprivateCount_liftTwo post ℓ c pre)

theorem participants_liftTwo_subset {S : Set Party} {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party)
    (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs))
    (hc : ∀ g, (↑(c.participants g) : Set Party) ⊆ S) :
    (pre : List (Frame pos q Party)) → (g : (liftTwo post ℓ c pre).nonprivateLocations) →
      (↑((liftTwo post ℓ c pre).participants g) : Set Party) ⊆ S
  | [], g => OriginalCircuit.participants_castLayouts_subset _ _ _
      (OriginalCircuit.participants_appendTail_subset c _ hc) g
  | G :: pre, g => OriginalCircuit.participants_frameList_subset _
      (participants_liftTwo_subset post ℓ c hc pre) G.regs g

theorem isExpansionBounded_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party)
    (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)) {r : ℕ} {s : ℝ}
    (hc : c.IsExpansionBounded r s) :
    (pre : List (Frame pos q Party)) → (liftTwo post ℓ c pre).IsExpansionBounded r s
  | [] => OriginalCircuit.isExpansionBounded_castLayouts _ _ _
      (OriginalCircuit.isExpansionBounded_appendTail c _ hc)
  | G :: pre => OriginalCircuit.isExpansionBounded_frameList _
      (isExpansionBounded_liftTwo post ℓ c hc pre) G.regs

theorem isMonomialBounded_liftTwo {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party)) (ℓ : Layout Party)
    (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs)) {K : ℕ}
    (hc : c.IsMonomialBounded K) :
    (pre : List (Frame pos q Party)) → (liftTwo post ℓ c pre).IsMonomialBounded K
  | [] => OriginalCircuit.isMonomialBounded_castLayouts _ _ _
      (OriginalCircuit.isMonomialBounded_appendTail c _ hc)
  | G :: pre => OriginalCircuit.isMonomialBounded_frameList _
      (isMonomialBounded_liftTwo post ℓ c hc pre) G.regs

/-! ### Reference vectors -/

section Reference

variable [NeZero q]

/-- The reference vector `Ω_F` of a frame, on the registers of the frame.
Polynomial-PEPS manuscript, `05-frames.tex`, lines 84–96. -/
def Frame.regRef (F : Frame pos q Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) : Mem F.regs :=
  F.regIso.symm (F.refVec Ω)

theorem Frame.norm_regRef (F : Frame pos q Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ‖F.regRef Ω‖ = ‖F.refVec Ω‖ :=
  LinearIsometryEquiv.norm_map _ _

theorem Frame.norm_regRef_le (F : Frame pos q Party) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ ≤ 1) : ‖F.regRef Ω‖ ≤ 1 :=
  (F.norm_regRef Ω).trans_le ((F.norm_refVec_le Ω).trans hΩ)

/-- The product of the reference vectors of a list of frames with a vector `ξ` of the layout
`ℓ`. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41. -/
def stackVec (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    (Fs : List (Frame pos q Party)) → {ℓ : Layout Party} → Mem ℓ → Mem (stackRegs Fs ℓ)
  | [], _, ξ => ξ
  | F :: Fs, ℓ, ξ => (appendIso F.regs (stackRegs Fs ℓ)).symm (F.regRef Ω ⊗ₜ stackVec Ω Fs ξ)

private theorem norm_appendIso_symm_tmul {a b : Layout Party} (x : Mem a) (y : Mem b) :
    ‖(appendIso a b).symm (x ⊗ₜ y)‖ = ‖x‖ * ‖y‖ := by
  rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul]

/-- The norm of the reference vector of several sheets is the product of the norms of the frame
reference vectors and of the idle vector. -/
theorem norm_stackVec (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    (Fs : List (Frame pos q Party)) → {ℓ : Layout Party} → (ξ : Mem ℓ) →
      ‖stackVec Ω Fs ξ‖ = (Fs.map fun F => ‖F.refVec Ω‖).prod * ‖ξ‖
  | [], _, ξ => by rw [List.map_nil, List.prod_nil, one_mul]; rfl
  | F :: Fs, ℓ, ξ => by
      rw [stackVec, norm_appendIso_symm_tmul, norm_stackVec Ω Fs ξ, F.norm_regRef,
        List.map_cons, List.prod_cons, mul_assoc]

/-- Every factor of the reference vector of several sheets has norm at most one. -/
theorem norm_stackVec_le {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) :
    (Fs : List (Frame pos q Party)) → {ℓ : Layout Party} → (ξ : Mem ℓ) →
      ‖stackVec Ω Fs ξ‖ ≤ ‖ξ‖
  | [], _, ξ => le_rfl
  | F :: Fs, ℓ, ξ => by
      rw [stackVec, norm_appendIso_symm_tmul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (F.norm_regRef_le hΩ)).trans
        (norm_stackVec_le hΩ Fs ξ)

namespace SheetStack

/-- The reference vector of a sheet stack: the product of the reference vectors `Ω_F` of its
frames with a vector `ξ` of its idle registers. Polynomial-PEPS manuscript,
`06-geometry.tex`, lines 39–41 and 662–667. -/
abbrev refVec (S : SheetStack pos q Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) (ξ : Mem S.idle) :
    Mem S.regs :=
  stackVec Ω S.frames ξ

theorem norm_refVec_le (S : SheetStack pos q Party) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ ≤ 1) {ξ : Mem S.idle} (hξ : ‖ξ‖ ≤ 1) : ‖S.refVec Ω ξ‖ ≤ 1 :=
  (norm_stackVec_le hΩ S.frames ξ).trans hξ

end SheetStack

/-- **The reference error of a change of one sheet.** On the whole stack, the change takes the
reference vector within the error it makes on its own sheet.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_eval_liftOne_stackVec_sub_le {F F' : Frame pos q Party}
    (post : List (Frame pos q Party)) {ℓ : Layout Party} (c : OriginalCircuit F.regs F'.regs)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) {ξ : Mem ℓ} (hξ : ‖ξ‖ ≤ 1) :
    (pre : List (Frame pos q Party)) →
      ‖(liftOne post ℓ c pre).eval (stackVec Ω (pre ++ F :: post) ξ) -
          stackVec Ω (pre ++ F' :: post) ξ‖ ≤ ‖c.eval (F.regRef Ω) - F'.regRef Ω‖
  | [] => by
      change ‖(c.appendTail (stackRegs post ℓ)).eval ((appendIso F.regs (stackRegs post ℓ)).symm
          (F.regRef Ω ⊗ₜ stackVec Ω post ξ)) -
        (appendIso F'.regs (stackRegs post ℓ)).symm (F'.regRef Ω ⊗ₜ stackVec Ω post ξ)‖ ≤ _
      rw [OriginalCircuit.eval_appendTail_appendIso_symm, ← map_sub, ← TensorProduct.sub_tmul,
        norm_appendIso_symm_tmul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((norm_stackVec_le hΩ post ξ).trans hξ)
  | G :: pre => by
      change ‖(OriginalCircuit.frameList G.regs (liftOne post ℓ c pre)).eval
          ((appendIso G.regs (stackRegs (pre ++ F :: post) ℓ)).symm
            (G.regRef Ω ⊗ₜ stackVec Ω (pre ++ F :: post) ξ)) -
        (appendIso G.regs (stackRegs (pre ++ F' :: post) ℓ)).symm
          (G.regRef Ω ⊗ₜ stackVec Ω (pre ++ F' :: post) ξ)‖ ≤ _
      rw [OriginalCircuit.eval_frameList_appendIso_symm, ← map_sub, ← TensorProduct.tmul_sub,
        norm_appendIso_symm_tmul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (G.norm_regRef_le hΩ)).trans
        (norm_eval_liftOne_stackVec_sub_le post c hΩ hξ pre)

/-- The reference vector of two frames on their concatenated registers. -/
def pairRef (F₁ F₂ : Frame pos q Party) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    Mem (F₁.regs ++ F₂.regs) :=
  (appendIso F₁.regs F₂.regs).symm (F₁.regRef Ω ⊗ₜ F₂.regRef Ω)

private theorem memCongr_appendIso_assoc (a b c : Layout Party) (x : Mem a) (y : Mem b)
    (z : Mem c) :
    Layout.memCongr (List.append_assoc a b c)
        ((appendIso (a ++ b) c).symm ((appendIso a b).symm (x ⊗ₜ y) ⊗ₜ z)) =
      (appendIso a (b ++ c)).symm (x ⊗ₜ (appendIso b c).symm (y ⊗ₜ z)) :=
  eq_of_heq ((Layout.memCongr_apply_heq _ _).trans (appendIso_assoc_symm_heq a b c x y z).symm)

/-- **The reference error of a change of two adjacent sheets.** On the whole stack, the change
takes the reference vector within the error it makes on its two sheets.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_eval_liftTwo_stackVec_sub_le {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (post : List (Frame pos q Party)) {ℓ : Layout Party}
    (c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs))
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) {ξ : Mem ℓ} (hξ : ‖ξ‖ ≤ 1) :
    (pre : List (Frame pos q Party)) →
      ‖(liftTwo post ℓ c pre).eval (stackVec Ω (pre ++ F₁ :: F₂ :: post) ξ) -
          stackVec Ω (pre ++ F₁' :: F₂' :: post) ξ‖ ≤
        ‖c.eval (pairRef F₁ F₂ Ω) - pairRef F₁' F₂' Ω‖
  | [] => by
      change ‖((c.appendTail (stackRegs post ℓ)).castLayouts (List.append_assoc _ _ _)
            (List.append_assoc _ _ _)).eval
          ((appendIso F₁.regs (F₂.regs ++ stackRegs post ℓ)).symm (F₁.regRef Ω ⊗ₜ
            (appendIso F₂.regs (stackRegs post ℓ)).symm (F₂.regRef Ω ⊗ₜ stackVec Ω post ξ))) -
        (appendIso F₁'.regs (F₂'.regs ++ stackRegs post ℓ)).symm (F₁'.regRef Ω ⊗ₜ
            (appendIso F₂'.regs (stackRegs post ℓ)).symm (F₂'.regRef Ω ⊗ₜ stackVec Ω post ξ))‖ ≤
        _
      rw [OriginalCircuit.eval_castLayouts, ← memCongr_appendIso_assoc, ←
        memCongr_appendIso_assoc]
      simp only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply]
      rw [OriginalCircuit.eval_appendTail_appendIso_symm, ← map_sub, ← map_sub,
        ← TensorProduct.sub_tmul, LinearIsometryEquiv.norm_map, norm_appendIso_symm_tmul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((norm_stackVec_le hΩ post ξ).trans hξ)
  | G :: pre => by
      change ‖(OriginalCircuit.frameList G.regs (liftTwo post ℓ c pre)).eval
          ((appendIso G.regs (stackRegs (pre ++ F₁ :: F₂ :: post) ℓ)).symm
            (G.regRef Ω ⊗ₜ stackVec Ω (pre ++ F₁ :: F₂ :: post) ξ)) -
        (appendIso G.regs (stackRegs (pre ++ F₁' :: F₂' :: post) ℓ)).symm
          (G.regRef Ω ⊗ₜ stackVec Ω (pre ++ F₁' :: F₂' :: post) ξ)‖ ≤ _
      rw [OriginalCircuit.eval_frameList_appendIso_symm, ← map_sub, ← TensorProduct.tmul_sub,
        norm_appendIso_symm_tmul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (G.norm_regRef_le hΩ)).trans
        (norm_eval_liftTwo_stackVec_sub_le post c hΩ hξ pre)

end Reference

end TNLean.PEPS.EncodedFrame
