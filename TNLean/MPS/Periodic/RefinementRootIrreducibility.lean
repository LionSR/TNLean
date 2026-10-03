/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import QICLean.Kraus.IrreducibleAction
import QICLean.Kraus.Transfer

/-!
# Irreducibility of a tensor from an irreducible block

Every subspace invariant under the one-site matrices is invariant under
their products. Consequently, irreducibility of any blocked tensor implies
irreducibility of the original tensor. This is the elementary reduction
needed when selecting a root in the converse of arXiv:1708.00029,
Theorem 4.1; it does not select such a root.
-/

open scoped Matrix

namespace MPSTensor

private theorem invariant_evalWord {d D : ℕ}
    (A : MPSTensor d D) (W : Submodule ℂ (Fin D → ℂ))
    (hW : Matrix.IsInvariantSubmodule A W) (w : List (Fin d))
    (v : Fin D → ℂ) (hv : v ∈ W) :
    (Kraus.evalWord A w).mulVec v ∈ W := by
  induction w with
  | nil => simpa [Kraus.evalWord] using hv
  | cons i w ih =>
      rw [Kraus.evalWord_cons, ← Matrix.mulVec_mulVec]
      exact hW i _ ih

/-- If a blocked tensor is irreducible, then the original tensor is
irreducible. No positivity assumption on the block length is required.
Source context: arXiv:1708.00029, Theorem 4.1, converse. -/
theorem isIrreducibleFamily_of_blockTensor {d D : ℕ}
    (A : MPSTensor d D) (p : ℕ)
    (hBlock : Kraus.IsIrreducibleFamily (blockTensor A p)) :
    Kraus.IsIrreducibleFamily A := by
  apply Kraus.isIrreducibleFamily_of_isIrreducibleAction A
  intro W hW
  apply (Kraus.isIrreducibleAction_of_isIrreducibleFamily
    (blockTensor A p) hBlock) W
  intro i v hv
  exact invariant_evalWord A W hW (wordOfBlock d p i) v hv

/-- If an irreducible target transfer map equals the transfer map of a
blocked root, then the root tensor is irreducible. Source context:
arXiv:1708.00029, Theorem 4.1, converse. -/
theorem isIrreducibleFamily_of_transferMap_eq_blockTensor
    {d e D : ℕ} (B : MPSTensor d D) (A : MPSTensor e D) (p : ℕ)
    (hB : Kraus.IsIrreducibleFamily B)
    (hEq : Kraus.transferMap B = Kraus.transferMap (blockTensor A p)) :
    Kraus.IsIrreducibleFamily A := by
  apply isIrreducibleFamily_of_blockTensor A p
  apply Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM
    (blockTensor A p)
  change IsIrreducibleMap (Kraus.transferMap (blockTensor A p))
  rw [← hEq]
  exact Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB

end MPSTensor
