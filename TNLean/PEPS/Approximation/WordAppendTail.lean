/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Operations beside spectator registers

A composition acting on one list of registers also acts on that list followed
by any spectator registers. Move the spectators to the front, perform the
original composition under those unchanged registers, and move them back.
This construction preserves every source occurrence and tensors the original
operator with the identity on the spectator memory.

Source: polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`,
allowed compositions in lines 32–35 and the local contractions in Theorem 5.2,
lines 409–434.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open ContinuousLinearMap

variable {P : Type}

/-- An empty final memory is the scalar tensor factor. -/
private theorem appendIso_nil_tmul (a : Layout P) (x : Mem a) (z : ℂ) :
    Layout.memCongr (List.append_nil a) ((appendIso a []).symm (x ⊗ₜ z)) = z • x := by
  induction a with
  | nil => simp [appendIso, Layout.memCongr, mul_comm]
  | cons r a ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
          rw [appendIso_symm_cons_tmul, Layout.memCongr_cons_tmul r (List.append_nil a), ih]
          exact TensorProduct.tmul_smul z u v
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy, smul_add]

/-- Equality of the second layout commutes with regrouping the tensor factors. -/
private theorem memCongr_append_right_tmul (a : Layout P) {b c : Layout P}
    (h : b = c) (x : Mem a) (y : Mem b) :
    Layout.memCongr (congrArg (a ++ ·) h) ((appendIso a b).symm (x ⊗ₜ y)) =
      (appendIso a c).symm (x ⊗ₜ Layout.memCongr h y) := by
  cases h
  rfl

/-- Appending an empty final memory with scalar one changes neither block. -/
private theorem appendIso_nil_pair (a b : Layout P) (x : Mem a) (y : Mem b) :
    Layout.memCongr (congrArg (a ++ ·) (List.append_nil b))
      ((appendIso a (b ++ [])).symm (x ⊗ₜ (appendIso b []).symm (y ⊗ₜ (1 : ℂ)))) =
        (appendIso a b).symm (x ⊗ₜ y) := by
  rw [memCongr_append_right_tmul a (List.append_nil b), appendIso_nil_tmul, one_smul]

namespace Word

/-- Exchange two complete lists, identifying their empty final memory. -/
private def exchangeTwo (a b : Layout P) : Word (a ++ b) (b ++ a) :=
  (exchangeBlocks a b []).castLayouts (congrArg (a ++ ·) (List.append_nil b))
    (congrArg (b ++ ·) (List.append_nil a))

/-- The two-list exchange interchanges the corresponding tensor factors. -/
private theorem eval_exchangeTwo (a b : Layout P) (x : Mem a) (y : Mem b) :
    (exchangeTwo a b).eval ((appendIso a b).symm (x ⊗ₜ y)) =
      (appendIso b a).symm (y ⊗ₜ x) := by
  rw [exchangeTwo, eval_castLayouts]
  change Layout.memCongr _ ((exchangeBlocks a b []).eval
    ((Layout.memCongr _).symm ((appendIso a b).symm (x ⊗ₜ y)))) = _
  rw [← appendIso_nil_pair a b x y, LinearIsometryEquiv.symm_apply_apply,
    eval_exchangeBlocks_appendIso_symm, appendIso_nil_pair]

/-- Framing by a list acts only on the second factor of its concatenated memory. -/
private theorem eval_frameList_appendIso {a b : Layout P} (w : Word a b)
    (tail : Layout P) (x : Mem tail) (y : Mem a) :
    (frameList tail w).eval ((appendIso tail a).symm (x ⊗ₜ y)) =
      (appendIso tail b).symm (x ⊗ₜ w.eval y) := by
  induction tail with
  | nil => exact map_smul w.eval x y
  | cons r tail ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z ↦ u ⊗ₜ z) (ih v)
      | add x z hx hz =>
          simp only [TensorProduct.add_tmul, map_add, hx, hz]

/-- Place a composition before unchanged spectator registers using allowed exchanges.
Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def appendTail {a b : Layout P} (w : Word a b) (tail : Layout P) :
    Word (a ++ tail) (b ++ tail) :=
  .comp (exchangeTwo a tail) (.comp (frameList tail w) (exchangeTwo tail b))

/-- A composition beside spectator registers is allowed whenever the original is.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 32–35 and 409–434. -/
theorem isAllowed_appendTail {a b : Layout P} (w : Word a b) (hw : w.IsAllowed)
    (tail : Layout P) : (w.appendTail tail).IsAllowed := by
  simp only [appendTail, IsAllowed, exchangeTwo, isAllowed_castLayouts]
  exact ⟨isAllowed_exchangeBlocks _ _ _, isAllowed_frameList w hw tail,
    isAllowed_exchangeBlocks _ _ _⟩

/-- Spectator registers leave every original source occurrence unchanged.
Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 409–434. -/
@[simp] theorem sources_appendTail {a b : Layout P} (w : Word a b) (tail : Layout P) :
    (w.appendTail tail).sources = w.sources := by
  simp [appendTail, sources, exchangeTwo]

/-- The resulting operator is the original operator tensored with the spectator identity.
This equality holds for arbitrary words and arbitrary input vectors.
Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem eval_appendTail {a b : Layout P} (w : Word a b) (tail : Layout P) :
    (w.appendTail tail).eval ∘L isoL (appendIso a tail).symm =
      isoL (appendIso b tail).symm ∘L w.eval.rTensor (Mem tail) := by
  apply clm_ext_tmul
  intro x y
  change (exchangeTwo tail b).eval ((frameList tail w).eval
    ((exchangeTwo a tail).eval ((appendIso a tail).symm (x ⊗ₜ y)))) =
      (appendIso b tail).symm (w.eval x ⊗ₜ y)
  rw [eval_exchangeTwo, eval_frameList_appendIso, eval_exchangeTwo]

end Word
end TNLean.PEPS.PairEffect
