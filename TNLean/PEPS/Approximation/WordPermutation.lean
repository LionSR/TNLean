/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord

/-!
# Moving a register through a list of registers

Adjacent exchanges move any specified register to the front of a layout.
The resulting word preserves the order of all other registers, and its operator
is exactly the corresponding permutation of tensor factors.

This supplies the exchanges needed to move fresh pair sources past untouched
registers in the source-preparation argument for Lemma 5.1 of the
polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`,
lines 68–70 and 125–127. The proof is independent of the source vectors.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open ContinuousLinearMap

variable {P : Type}

/-- Regrouping a concatenated layout preserves its first tensor factor. -/
theorem appendIso_symm_cons_tmul (r : Reg P) (ℓ₀ ℓ : Layout P)
    (x : r.space) (s : Mem ℓ₀) (y : Mem ℓ) :
    (appendIso (r :: ℓ₀) ℓ).symm ((x ⊗ₜ s) ⊗ₜ y) =
      x ⊗ₜ (appendIso ℓ₀ ℓ).symm (s ⊗ₜ y) := by
  rfl

namespace Word

/-- Move a register to the front by adjacent exchanges, preserving the order
of the preceding registers. This implements the tensor permutations used in
the source grouping of the polynomial-PEPS manuscript, Lemma 5.1,
`04-compression.tex`, lines 68–70 and 125–127. -/
def moveHead (r : Reg P) : (ℓ₀ tail : Layout P) →
    Word (ℓ₀ ++ r :: tail) (r :: (ℓ₀ ++ tail))
  | [], tail => .id (r :: tail)
  | head :: ℓ₀, tail =>
      .comp (.frame head (moveHead r ℓ₀ tail)) (.swap head r (ℓ₀ ++ tail))

/-- Moving a register uses only allowed exchanges and framing.
Source: polynomial-PEPS manuscript, Lemma 5.1, `04-compression.tex`, lines 68–70. -/
theorem isAllowed_moveHead (r : Reg P) : (ℓ₀ tail : Layout P) →
    (moveHead r ℓ₀ tail).IsAllowed
  | [], _ => trivial
  | _ :: ℓ₀, tail => ⟨isAllowed_moveHead r ℓ₀ tail, trivial⟩

/-- The operator of the exchange word moves the selected tensor factor to
the front, with the remaining factors in their original order.
Source: polynomial-PEPS manuscript, Lemma 5.1, source grouping,
`04-compression.tex`, lines 68–70 and 125–127. -/
theorem eval_moveHead_appendIso_symm (r : Reg P) (ℓ₀ tail : Layout P)
    (s : Mem ℓ₀) (x : r.space) (y : Mem tail) :
    (moveHead r ℓ₀ tail).eval ((appendIso ℓ₀ (r :: tail)).symm
      (s ⊗ₜ (x ⊗ₜ y))) =
      x ⊗ₜ (appendIso ℓ₀ tail).symm (s ⊗ₜ y) := by
  induction ℓ₀ with
  | nil => exact (TensorProduct.tmul_smul (R := ℂ) s x y).symm
  | cons head ℓ₀ ih =>
      induction s using TensorProduct.inductionOn with
      | tmul u v =>
          exact congrArg (fun z ↦
            leftCommL head.space r.space (Mem (ℓ₀ ++ tail)) (u ⊗ₜ z)) (ih v)
      | add a b ha hb =>
          simp only [TensorProduct.add_tmul, map_add, ha, hb, TensorProduct.tmul_add]

/-- Exchange two successive lists of registers, preserving the order within
each list. Source: polynomial-PEPS manuscript, Lemma 5.1, grouping sources on
the same pair of parties, `04-compression.tex`, lines 68–70 and 125–127. -/
def exchangeBlocks (a : Layout P) : (b tail : Layout P) →
    Word (a ++ (b ++ tail)) (b ++ (a ++ tail))
  | [], tail => .id (a ++ tail)
  | r :: b, tail =>
      .comp (moveHead r a (b ++ tail)) (.frame r (exchangeBlocks a b tail))

/-- Exchanging lists of registers uses only allowed exchanges and framing. -/
theorem isAllowed_exchangeBlocks (a : Layout P) : (b tail : Layout P) →
    (exchangeBlocks a b tail).IsAllowed
  | [], _ => trivial
  | r :: b, tail => ⟨isAllowed_moveHead r a (b ++ tail),
      isAllowed_exchangeBlocks a b tail⟩

/-- The exchange word interchanges the two indicated tensor factors and
leaves the remaining memory untouched. Source: polynomial-PEPS manuscript,
Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127. -/
theorem eval_exchangeBlocks_appendIso_symm (a b tail : Layout P)
    (s : Mem a) (t : Mem b) (u : Mem tail) :
    (exchangeBlocks a b tail).eval ((appendIso a (b ++ tail)).symm
      (s ⊗ₜ (appendIso b tail).symm (t ⊗ₜ u))) =
      (appendIso b (a ++ tail)).symm
        (t ⊗ₜ (appendIso a tail).symm (s ⊗ₜ u)) := by
  induction b with
  | nil =>
      exact (congrArg (appendIso a tail).symm
        (TensorProduct.tmul_smul (R := ℂ) t s u)).trans
        ((appendIso a tail).symm.map_smul t (s ⊗ₜ u))
  | cons r b ih =>
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
          exact (congrArg ((exchangeBlocks a b tail).eval.lTensor r.space)
            (eval_moveHead_appendIso_symm r a (b ++ tail) s x
              ((appendIso b tail).symm (y ⊗ₜ u)))).trans
            (congrArg (fun z ↦ x ⊗ₜ z) (ih y))
      | add x y hx hy =>
          simp only [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add, hx, hy]

end Word
end TNLean.PEPS.PairEffect
