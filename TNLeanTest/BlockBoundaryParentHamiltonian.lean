/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BlockBoundaryParentHamiltonian
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace

/-!
# Assembled block-parent symmetry regression tests

The state and operator tensors are assembled over independent label sets.
The only adjoint-closure hypothesis is for the whole assembled MPO range.
A selector isolates each periodic MPO even at zero length and for zero-size
summands; no full physical identity or individual-label closure is assumed.
-/

set_option linter.hashCommand false

open scoped Matrix BigOperators

namespace BlockBoundaryParentHamiltonianTest

variable {d r s L N : ℕ} {dim : Fin r → ℕ} {stateDim : Fin s → ℕ}

example (O : (a : Fin r) → MPOTensor d (dim a)) (a : Fin r) :
    MPOTensor.mpoWithBoundary (MPOTensor.blockSum O)
        (MPOTensor.blockBoundarySelector dim a) 0 = MPOTensor.mpo (O a) 0 :=
  MPOTensor.mpoWithBoundary_blockSum_blockBoundarySelector O a 0

example (O : (a : Fin r) → MPOTensor d (dim a))
    (B : (b : Fin s) → MPSTensor d (stateDim b))
    (h : MPOTensor.IsBoundaryCompatible (MPOTensor.blockSum O)
      (MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B))
    (hL : 0 < L) (hLN : L ≤ N)
    (hstar : ∀ X : Matrix (Fin (∑ a, dim a)) (Fin (∑ a, dim a)) ℂ,
      ∃ Y, (MPOTensor.mpoWithBoundary (MPOTensor.blockSum O) X L)ᴴ =
        MPOTensor.mpoWithBoundary (MPOTensor.blockSum O) Y L)
    (hDim : d ^ L > (∑ b, stateDim b) ^ 2) :
    MPSTensor.groundSpace (MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B) L =
        ⨆ b, MPSTensor.groundSpace (B b) L ∧
      MPSTensor.parentInteractionES (MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B) L ≠ 0 ∧
      ∀ a : Fin r,
        Commute (MPSTensor.parentHamiltonianES
          (MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B) L N)
          (Matrix.toEuclideanLin (MPOTensor.mpo (O a) N)) := by
  refine ⟨MPSTensor.groundSpace_toTensorFromBlocks_eq_iSup _ B (by simp) L,
    MPSTensor.parentInteractionES_ne_zero _ L hDim, ?_⟩
  intro a
  exact h.parentHamiltonianES_commute_mpo_block hL hLN hstar a

end BlockBoundaryParentHamiltonianTest

/-- info: 'MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_mpo_block

/-- info: 'MPOTensor.mpoWithBoundary_blockSum_blockBoundarySelector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.mpoWithBoundary_blockSum_blockBoundarySelector
