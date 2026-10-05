/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryBlockFusion

/-!
# Exact action tensors for fixed incoming blocks

The length-independent compatibility condition gives exact biorthogonal
action tensors for every pair consisting of an MPO block and an MPS block.
Only simultaneous spanning of the target state blocks is needed; no
injectivity assumption on the operator blocks is used in this argument.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:compatible`,
  `fusiontensors2`, `eq:orthoV`, and Appendix A, final paragraph.
-/

open scoped Matrix BigOperators Kronecker

noncomputable section

namespace MPOTensor

variable {d D₁ D₂ E₁ E₂ r s : ℕ} {opDim : Fin r → ℕ} {dim : Fin s → ℕ}

/-- Invariant bond inclusions of an operator and a state intertwine their
action tensors. Source: GLM23, `fusiontensors2` and Appendix A. -/
theorem actTensor_intertwine_stackedBondMap
    (T : MPOTensor d D₁) (A : MPSTensor d D₂)
    (S : MPOTensor d E₁) (B : MPSTensor d E₂)
    (W₁ : Matrix (Fin D₁) (Fin E₁) ℂ) (W₂ : Matrix (Fin D₂) (Fin E₂) ℂ)
    (hW₁ : ∀ i j, T i j * W₁ = W₁ * S i j)
    (hW₂ : ∀ i, A i * W₂ = W₂ * B i) (i : Fin d) :
    actTensor T A i * stackedBondMap W₁ W₂ =
      stackedBondMap W₁ W₂ * actTensor S B i := by
  simp only [actTensor_apply, stackedBondMap, Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hW₁, hW₂]

/-- Every fixed operator block and state block has exact action tensors with
biorthogonal left inverses. Source: GLM23, `fusiontensors2`, `eq:orthoV`,
and Appendix A. The source tensor families are unweighted direct sums. -/
theorem IsBoundaryCompatible.exists_blockActionDecomposition
    {T : MPOTensor d (∑ a : Fin r, opDim a)}
    {A : MPSTensor d (∑ c : Fin s, dim c)} (h : IsBoundaryCompatible T A)
    (S : (a : Fin r) → MPOTensor d (opDim a))
    (B : (c : Fin s) → MPSTensor d (dim c))
    (hT : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (S a).toMPSTensor))
    (hA : A = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop B L)
    (a : Fin r) (x : Fin s) :
    ∃ (m : Fin s → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (opDim a * dim x)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (opDim a * dim x)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (actTensor (S a) (B x))
        (fun q : (c : Fin s) × Fin (m c) ↦ B q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨b, hb⟩ := (isBoundaryCompatible_iff_exists_linearMap T A).mp h
  let U := MPSTensor.blockInclusion opDim a
  let J := MPSTensor.blockInclusion dim x
  have hU i j : T i j * U = U * S a i j := by
    have hh := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ ↦ 1) (fun a ↦ (S a).toMPSTensor) a (finProdFinEquiv (i, j))
    rw [← hT] at hh
    simpa [toMPSTensor, U] using hh
  have hJ i : A i * J = J * B x i := by
    rw [hA]
    simpa only [one_smul] using
      MPSTensor.toTensorFromBlocks_mul_blockInclusion (fun _ ↦ 1) B x i
  apply MPSTensor.exists_biorthogonalDecomposition_of_boundaryTransport_restrict
    (actTensor T A) (actTensor (S a) (B x)) B
    (Matrix.finSigmaDiagonalBlocks.comp b) ?_
    (stackedBondMap Uᴴ Jᴴ) (stackedBondMap U J) ?_ ?_ hL hSpan
  · intro n hn X w
    have hh := congrFun (hb n hn X) w
    rw [hh, hA, MPSTensor.mpvWithBoundary_toTensorFromBlocks_one]
    rfl
  · rw [stackedBondMap_mul]
    dsimp [U, J]
    rw [MPSTensor.blockInclusion_conjTranspose_mul_self,
      MPSTensor.blockInclusion_conjTranspose_mul_self, stackedBondMap_one]
  · exact actTensor_intertwine_stackedBondMap T A (S a) (B x) U J hU hJ

end MPOTensor
