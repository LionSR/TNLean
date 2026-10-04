/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.IsometryTree
import TNLean.MPS.Preparation.PolarMerge

/-!
# Polar isometries as trees of uniformly bounded leaves

Suppose all blocks of length at least `s` are injective. A block of any length `n`
between `2^h s` and `2^h c` has a binary tree of `h` coarse layers, with every physical
leaf between `s` and `c` sites. Repeatedly split a block into its floor and ceiling
halves. The polar-merge identity identifies the resulting tree with the polar
isometry of the original block. Vertex tensors may differ even at the same depth.

This extends the tree in arXiv:2307.01696, eq. (16), to unequal block lengths;
the physical leaf bound is independent of the total length and the requested accuracy.
-/

open Matrix MPSTensor

namespace MPSPreparation

/-- **A bounded-leaf polar tree for an arbitrary block length.** If every block of length
at least `s > 0` is injective and `2^h s ≤ n ≤ 2^h c`, the polar isometry of the block
has an `h`-layer binary tree whose leaves have at most `c` sites.

Source: arXiv:2307.01696, eq. (16), using the polar merge identity for unequal halves. -/
theorem exists_isometryTree_matrix_eq_cfgPolarIso {d D s : ℕ} (A : MPSTensor d D)
    (hs : 0 < s) (hinj : ∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m))
    (h n c : ℕ) (hlower : 2 ^ h * s ≤ n) (hupper : n ≤ 2 ^ h * c) :
    ∃ T : IsometryTree d (D * D) c h n, T.matrix = cfgPolarIso A n := by
  induction h generalizing n with
  | zero =>
    have hsn : s ≤ n := by simpa using hlower
    exact ⟨.leaf (cfgPolarIso A n) (isIsometry_cfgPolarIso A (hinj n hsn))
      (hs.trans_le hsn) (by simpa using hupper), rfl⟩
  | succ h ih =>
    have hlo : 2 * (2 ^ h * s) ≤ n := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlower
    have hhi : n ≤ 2 * (2 ^ h * c) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hupper
    have hsum : n / 2 + (n - n / 2) = n := by omega
    obtain ⟨T₁, hT₁⟩ := ih (n / 2) (by omega) (by omega)
    obtain ⟨T₂, hT₂⟩ := ih (n - n / 2) (by omega) (by omega)
    have hsn : s ≤ n :=
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (h + 1))).trans hlower
    have hW : (mergeIso A (n / 2) (n - n / 2)).IsIsometry := by
      apply isIsometry_mergeIso A
      rw [hsum]
      exact hinj n hsn
    refine ⟨(IsometryTree.fork T₁ T₂ (mergeIso A (n / 2) (n - n / 2)) hW).cast hsum, ?_⟩
    ext τ x
    rw [IsometryTree.matrix_cast, IsometryTree.matrix_fork_apply, hT₁, hT₂]
    exact (cfgPolarIso_split A hsum τ x).symm

end MPSPreparation
