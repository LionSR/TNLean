/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.LayoutEqualityCoordinates
import TNLean.Lattice.PartyCircuit.OriginalCircuitLift

/-!
# The memory of several sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds several
sheets: the main sheet, the active auxiliary sheet of the current repainting, the frozen
auxiliary sheets of earlier repaintings, and the auxiliary copies of `Ω` not yet in use, each
held privately by the party that will initialize it. The reference vector at each stage is the
tensor product of the reference vectors of the sheets and of the idle copies, every factor of
norm at most one (`06-geometry.tex`, lines 39–41 and 658–667).

None of this depends on what a sheet is. This file works with an arbitrary type `κ` of sheets,
each sheet `F` carrying a layout of registers `regs F` and, where a reference vector is needed,
a vector `ref F` on these registers. The encoded frames of the two-dimensional protocol are one
instance; the sheets without holes of a chain are another.

The registers of a list of sheets followed by a layout `ℓ` of idle registers are the registers
of the sheets, in order, followed by `ℓ` (`Lattice.stackRegs`), and the reference vector is the
product of the reference vectors of the sheets with a vector of the idle registers
(`Lattice.stackVec`).

A bounded change acts on one sheet (a small-patch rewrite, a birth or a death) or on two
adjacent sheets (the lens exchange). Lifting the change to the whole stack, with the other
sheets as spectators (`Lattice.liftOne`, `Lattice.liftTwo`), changes neither its gates nor its
participants, and its reference error on the stack is at most its reference error on the sheets
it acts on, when every reference vector has norm at most one
(`Lattice.norm_eval_liftOne_stackVec_sub_le`, `Lattice.norm_eval_liftTwo_stackVec_sub_le`).

## Main definitions

* `Lattice.stackRegs`, `Lattice.stackVec` : the registers and the reference vector of a list of
  sheets before a layout.
* `Lattice.liftOne`, `Lattice.liftTwo` : a change of one sheet or of two adjacent sheets, on the
  whole stack.
* `Lattice.pairRef` : the reference vector of two sheets on their concatenated registers.

## Main results

* `Lattice.norm_stackVec` : the norm of the reference vector is the product of the norms of its
  factors.
* `Lattice.norm_eval_liftOne_stackVec_sub_le`, `Lattice.norm_eval_liftTwo_stackVec_sub_le` : the
  reference error of a lifted change.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 39–41 (the reference vectors as products of frame vectors) and
  658–667 (initialization and the reference vectors); encoded frames, `05-frames.tex`,
  lines 71–96.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.Lattice

open TNLean.PEPS.PairEffect

variable {κ : Type*} {Party : Type}

/-! ### Registers of several sheets -/

section Registers

variable (regs : κ → Layout Party)

/-- The registers of a list of sheets, in order, followed by the layout `ℓ`. -/
@[reducible] def stackRegs : List κ → Layout Party → Layout Party
  | [], ℓ => ℓ
  | F :: Fs, ℓ => regs F ++ stackRegs Fs ℓ

/-! ### A change of one sheet -/

/-- A change of the sheet `F` into `F'` on the whole stack `pre ++ F :: post`, with the other
sheets and the layout `ℓ` as spectators. -/
def liftOne {F F' : κ} (post : List κ) (ℓ : Layout Party) (c : OriginalCircuit (regs F) (regs F')) :
    (pre : List κ) →
      OriginalCircuit (stackRegs regs (pre ++ F :: post) ℓ) (stackRegs regs (pre ++ F' :: post) ℓ)
  | [] => c.appendTail (stackRegs regs post ℓ)
  | G :: pre => OriginalCircuit.frameList (regs G) (liftOne post ℓ c pre)

@[simp] theorem nonprivateCount_liftOne {F F' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F) (regs F')) :
    (pre : List κ) → (liftOne regs post ℓ c pre).nonprivateCount = c.nonprivateCount
  | [] => OriginalCircuit.nonprivateCount_appendTail c _
  | G :: pre => (OriginalCircuit.nonprivateCount_frameList _ (regs G)).trans
      (nonprivateCount_liftOne post ℓ c pre)

theorem participants_liftOne_subset {S : Set Party} {F F' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F) (regs F')) (hc : ∀ g, (↑(c.participants g) : Set Party) ⊆ S) :
    (pre : List κ) → (g : (liftOne regs post ℓ c pre).nonprivateLocations) →
      (↑((liftOne regs post ℓ c pre).participants g) : Set Party) ⊆ S
  | [], g => OriginalCircuit.participants_appendTail_subset c _ hc g
  | G :: pre, g => OriginalCircuit.participants_frameList_subset _
      (participants_liftOne_subset post ℓ c hc pre) (regs G) g

theorem isExpansionBounded_liftOne {F F' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F) (regs F')) {r : ℕ} {s : ℝ} (hc : c.IsExpansionBounded r s) :
    (pre : List κ) → (liftOne regs post ℓ c pre).IsExpansionBounded r s
  | [] => OriginalCircuit.isExpansionBounded_appendTail c _ hc
  | G :: pre => OriginalCircuit.isExpansionBounded_frameList _
      (isExpansionBounded_liftOne post ℓ c hc pre) (regs G)

theorem isMonomialBounded_liftOne {F F' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F) (regs F')) {K : ℕ} (hc : c.IsMonomialBounded K) :
    (pre : List κ) → (liftOne regs post ℓ c pre).IsMonomialBounded K
  | [] => OriginalCircuit.isMonomialBounded_appendTail c _ hc
  | G :: pre => OriginalCircuit.isMonomialBounded_frameList _
      (isMonomialBounded_liftOne post ℓ c hc pre) (regs G)

/-! ### A change of two adjacent sheets -/

/-- A change of the adjacent sheets `F₁, F₂` into `F₁', F₂'` on the whole stack
`pre ++ F₁ :: F₂ :: post`, with the other sheets and the layout `ℓ` as spectators. -/
def liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')) :
    (pre : List κ) →
      OriginalCircuit (stackRegs regs (pre ++ F₁ :: F₂ :: post) ℓ)
        (stackRegs regs (pre ++ F₁' :: F₂' :: post) ℓ)
  | [] => (c.appendTail (stackRegs regs post ℓ)).castLayouts (List.append_assoc _ _ _)
      (List.append_assoc _ _ _)
  | G :: pre => OriginalCircuit.frameList (regs G) (liftTwo post ℓ c pre)

@[simp] theorem nonprivateCount_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')) :
    (pre : List κ) → (liftTwo regs post ℓ c pre).nonprivateCount = c.nonprivateCount
  | [] => (OriginalCircuit.nonprivateCount_castLayouts _ _ _).trans
      (OriginalCircuit.nonprivateCount_appendTail c _)
  | G :: pre => (OriginalCircuit.nonprivateCount_frameList _ (regs G)).trans
      (nonprivateCount_liftTwo post ℓ c pre)

theorem participants_liftTwo_subset {S : Set Party} {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (ℓ : Layout Party) (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂'))
    (hc : ∀ g, (↑(c.participants g) : Set Party) ⊆ S) :
    (pre : List κ) → (g : (liftTwo regs post ℓ c pre).nonprivateLocations) →
      (↑((liftTwo regs post ℓ c pre).participants g) : Set Party) ⊆ S
  | [], g => OriginalCircuit.participants_castLayouts_subset _ _ _
      (OriginalCircuit.participants_appendTail_subset c _ hc) g
  | G :: pre, g => OriginalCircuit.participants_frameList_subset _
      (participants_liftTwo_subset post ℓ c hc pre) (regs G) g

theorem isExpansionBounded_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')) {r : ℕ} {s : ℝ}
    (hc : c.IsExpansionBounded r s) :
    (pre : List κ) → (liftTwo regs post ℓ c pre).IsExpansionBounded r s
  | [] => OriginalCircuit.isExpansionBounded_castLayouts _ _ _
      (OriginalCircuit.isExpansionBounded_appendTail c _ hc)
  | G :: pre => OriginalCircuit.isExpansionBounded_frameList _
      (isExpansionBounded_liftTwo post ℓ c hc pre) (regs G)

theorem isMonomialBounded_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ) (ℓ : Layout Party)
    (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')) {K : ℕ}
    (hc : c.IsMonomialBounded K) :
    (pre : List κ) → (liftTwo regs post ℓ c pre).IsMonomialBounded K
  | [] => OriginalCircuit.isMonomialBounded_castLayouts _ _ _
      (OriginalCircuit.isMonomialBounded_appendTail c _ hc)
  | G :: pre => OriginalCircuit.isMonomialBounded_frameList _
      (isMonomialBounded_liftTwo post ℓ c hc pre) (regs G)

end Registers

/-! ### Reference vectors -/

section Reference

variable {regs : κ → Layout Party} (ref : (F : κ) → Mem (regs F))

/-- The product of the reference vectors `ref F` of a list of sheets with a vector `ξ` of the
layout `ℓ`. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41. -/
def stackVec : (Fs : List κ) → {ℓ : Layout Party} → Mem ℓ → Mem (stackRegs regs Fs ℓ)
  | [], _, ξ => ξ
  | F :: Fs, ℓ, ξ => (appendIso (regs F) (stackRegs regs Fs ℓ)).symm (ref F ⊗ₜ stackVec Fs ξ)

private theorem norm_appendIso_symm_tmul {a b : Layout Party} (x : Mem a) (y : Mem b) :
    ‖(appendIso a b).symm (x ⊗ₜ y)‖ = ‖x‖ * ‖y‖ := by
  rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul]

/-- The norm of the reference vector of several sheets is the product of the norms of the
reference vectors of the sheets and of the idle vector. -/
theorem norm_stackVec : (Fs : List κ) → {ℓ : Layout Party} → (ξ : Mem ℓ) →
    ‖stackVec ref Fs ξ‖ = (Fs.map fun F => ‖ref F‖).prod * ‖ξ‖
  | [], _, ξ => by rw [List.map_nil, List.prod_nil, one_mul]; rfl
  | F :: Fs, ℓ, ξ => by
      rw [stackVec, norm_appendIso_symm_tmul, norm_stackVec Fs ξ, List.map_cons, List.prod_cons,
        mul_assoc]

variable {ref}

/-- If every reference vector has norm at most one, the reference vector of several sheets has
norm at most that of the idle vector. -/
theorem norm_stackVec_le (href : ∀ F, ‖ref F‖ ≤ 1) :
    (Fs : List κ) → {ℓ : Layout Party} → (ξ : Mem ℓ) → ‖stackVec ref Fs ξ‖ ≤ ‖ξ‖
  | [], _, ξ => le_rfl
  | F :: Fs, ℓ, ξ => by
      rw [stackVec, norm_appendIso_symm_tmul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (href F)).trans (norm_stackVec_le href Fs ξ)

/-- **The reference error of a change of one sheet.** On the whole stack, the change takes the
reference vector within the error it makes on its own sheet.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_eval_liftOne_stackVec_sub_le {F F' : κ} (post : List κ) {ℓ : Layout Party}
    (c : OriginalCircuit (regs F) (regs F')) (href : ∀ F, ‖ref F‖ ≤ 1) {ξ : Mem ℓ}
    (hξ : ‖ξ‖ ≤ 1) :
    (pre : List κ) →
      ‖(liftOne regs post ℓ c pre).eval (stackVec ref (pre ++ F :: post) ξ) -
          stackVec ref (pre ++ F' :: post) ξ‖ ≤ ‖c.eval (ref F) - ref F'‖
  | [] => by
      change ‖(c.appendTail (stackRegs regs post ℓ)).eval
          ((appendIso (regs F) (stackRegs regs post ℓ)).symm (ref F ⊗ₜ stackVec ref post ξ)) -
        (appendIso (regs F') (stackRegs regs post ℓ)).symm (ref F' ⊗ₜ stackVec ref post ξ)‖ ≤ _
      rw [OriginalCircuit.eval_appendTail_appendIso_symm, ← map_sub, ← TensorProduct.sub_tmul,
        norm_appendIso_symm_tmul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((norm_stackVec_le href post ξ).trans hξ)
  | G :: pre => by
      change ‖(OriginalCircuit.frameList (regs G) (liftOne regs post ℓ c pre)).eval
          ((appendIso (regs G) (stackRegs regs (pre ++ F :: post) ℓ)).symm
            (ref G ⊗ₜ stackVec ref (pre ++ F :: post) ξ)) -
        (appendIso (regs G) (stackRegs regs (pre ++ F' :: post) ℓ)).symm
          (ref G ⊗ₜ stackVec ref (pre ++ F' :: post) ξ)‖ ≤ _
      rw [OriginalCircuit.eval_frameList_appendIso_symm, ← map_sub, ← TensorProduct.tmul_sub,
        norm_appendIso_symm_tmul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (href G)).trans
        (norm_eval_liftOne_stackVec_sub_le post c href hξ pre)

variable (ref) in
/-- The reference vector of two sheets on their concatenated registers. -/
def pairRef (F₁ F₂ : κ) : Mem (regs F₁ ++ regs F₂) :=
  (appendIso (regs F₁) (regs F₂)).symm (ref F₁ ⊗ₜ ref F₂)

private theorem memCongr_appendIso_assoc (a b c : Layout Party) (x : Mem a) (y : Mem b)
    (z : Mem c) :
    Layout.memCongr (List.append_assoc a b c)
        ((appendIso (a ++ b) c).symm ((appendIso a b).symm (x ⊗ₜ y) ⊗ₜ z)) =
      (appendIso a (b ++ c)).symm (x ⊗ₜ (appendIso b c).symm (y ⊗ₜ z)) :=
  eq_of_heq ((Layout.memCongr_apply_heq _ _).trans (appendIso_assoc_symm_heq a b c x y z).symm)

/-- **The reference error of a change of two adjacent sheets.** On the whole stack, the change
takes the reference vector within the error it makes on its two sheets.
Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_eval_liftTwo_stackVec_sub_le {F₁ F₂ F₁' F₂' : κ} (post : List κ) {ℓ : Layout Party}
    (c : OriginalCircuit (regs F₁ ++ regs F₂) (regs F₁' ++ regs F₂')) (href : ∀ F, ‖ref F‖ ≤ 1)
    {ξ : Mem ℓ} (hξ : ‖ξ‖ ≤ 1) :
    (pre : List κ) →
      ‖(liftTwo regs post ℓ c pre).eval (stackVec ref (pre ++ F₁ :: F₂ :: post) ξ) -
          stackVec ref (pre ++ F₁' :: F₂' :: post) ξ‖ ≤
        ‖c.eval (pairRef ref F₁ F₂) - pairRef ref F₁' F₂'‖
  | [] => by
      change ‖((c.appendTail (stackRegs regs post ℓ)).castLayouts (List.append_assoc _ _ _)
            (List.append_assoc _ _ _)).eval
          ((appendIso (regs F₁) (regs F₂ ++ stackRegs regs post ℓ)).symm (ref F₁ ⊗ₜ
            (appendIso (regs F₂) (stackRegs regs post ℓ)).symm
              (ref F₂ ⊗ₜ stackVec ref post ξ))) -
        (appendIso (regs F₁') (regs F₂' ++ stackRegs regs post ℓ)).symm (ref F₁' ⊗ₜ
            (appendIso (regs F₂') (stackRegs regs post ℓ)).symm
              (ref F₂' ⊗ₜ stackVec ref post ξ))‖ ≤ _
      rw [OriginalCircuit.eval_castLayouts, ← memCongr_appendIso_assoc, ←
        memCongr_appendIso_assoc]
      simp only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply]
      rw [OriginalCircuit.eval_appendTail_appendIso_symm, ← map_sub, ← map_sub,
        ← TensorProduct.sub_tmul, LinearIsometryEquiv.norm_map, norm_appendIso_symm_tmul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((norm_stackVec_le href post ξ).trans hξ)
  | G :: pre => by
      change ‖(OriginalCircuit.frameList (regs G) (liftTwo regs post ℓ c pre)).eval
          ((appendIso (regs G) (stackRegs regs (pre ++ F₁ :: F₂ :: post) ℓ)).symm
            (ref G ⊗ₜ stackVec ref (pre ++ F₁ :: F₂ :: post) ξ)) -
        (appendIso (regs G) (stackRegs regs (pre ++ F₁' :: F₂' :: post) ℓ)).symm
          (ref G ⊗ₜ stackVec ref (pre ++ F₁' :: F₂' :: post) ξ)‖ ≤ _
      rw [OriginalCircuit.eval_frameList_appendIso_symm, ← map_sub, ← TensorProduct.tmul_sub,
        norm_appendIso_symm_tmul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (href G)).trans
        (norm_eval_liftTwo_stackVec_sub_le post c href hξ pre)

end Reference

end TNLean.Lattice
