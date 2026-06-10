/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Local ground spaces of block-diagonal tensors

This file identifies the local parent-Hamiltonian ground space of a
block-diagonal tensor with the linear sum of the local ground spaces of its
blocks.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 2blocks.2,
  proof lines 1430--1434, where
  \(S=\bigoplus_j\mathcal G_L^{A^j}\).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

namespace BlockSumGroundSpace

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The diagonal block of a boundary matrix written in the dependent direct-sum
basis. -/
noncomputable def sigmaDiagonalBlock
    (X : Matrix ((j : Fin r) × Fin (dim j)) ((j : Fin r) × Fin (dim j)) ℂ)
    (j : Fin r) : Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
  X.submatrix (fun a => ⟨j, a⟩) (fun a => ⟨j, a⟩)

/-- The diagonal block of a boundary matrix on the flattened direct-sum bond. -/
noncomputable def diagonalBlock
    (X : Matrix (Fin (∑ j : Fin r, dim j)) (Fin (∑ j : Fin r, dim j)) ℂ)
    (j : Fin r) : Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
  sigmaDiagonalBlock ((Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm) X) j

/-- A block-diagonal matrix only sees the diagonal blocks of an arbitrary
right boundary matrix under the trace pairing. -/
theorem trace_blockDiagonal'_mul
    (M : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (X : Matrix ((j : Fin r) × Fin (dim j)) ((j : Fin r) × Fin (dim j)) ℂ) :
    Matrix.trace (Matrix.blockDiagonal' M * X) =
      ∑ j : Fin r, Matrix.trace (M j * sigmaDiagonalBlock X j) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sigmaDiagonalBlock,
    Matrix.submatrix_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    apply Finset.sum_eq_zero
    intro b _
    have hjk : j ≠ k := fun h => hkj h.symm
    rw [Matrix.blockDiagonal'_apply_ne M a b hjk]
    simp
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

/-- The boundary parametrization of a block-diagonal tensor is the sum of the block
boundary parametrizations applied to the diagonal boundary blocks. -/
theorem groundSpaceMap_toTensorFromBlocks_eq_sum_diagonalBlock
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ)
    (X : Matrix (Fin (∑ j : Fin r, dim j)) (Fin (∑ j : Fin r, dim j)) ℂ) :
    groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) L X =
      ∑ j : Fin r, groundSpaceMap (A j) L ((μ j) ^ L • diagonalBlock X j) := by
  classical
  ext σ
  simp only [groundSpaceMap_apply, Finset.sum_apply]
  let w := List.ofFn σ
  have hwlen : w.length = L := by simp [w]
  let e : ((j : Fin r) × Fin (dim j)) ≃ Fin (∑ j : Fin r, dim j) :=
    finSigmaFinEquiv
  let Xσ : Matrix ((j : Fin r) × Fin (dim j)) ((j : Fin r) × Fin (dim j)) ℂ :=
    (Matrix.reindex e.symm e.symm) X
  have hX : X = (Matrix.reindex e e) Xσ := by
    ext a b
    simp [Xσ, e]
  rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal μ A w, hX]
  have hmul :
      (Matrix.reindex e e (Matrix.blockDiagonal' fun k : Fin r =>
          μ k ^ w.length • (A k).evalWord w)) * (Matrix.reindex e e Xσ) =
        Matrix.reindex e e
          ((Matrix.blockDiagonal' fun k : Fin r => μ k ^ w.length • (A k).evalWord w) *
            Xσ) := by
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
      (Matrix.blockDiagonal' fun k : Fin r => μ k ^ w.length • (A k).evalWord w) Xσ
  rw [hmul, Matrix.trace_reindex e]
  rw [trace_blockDiagonal'_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hdiag : diagonalBlock ((Matrix.reindex e e) Xσ) j = sigmaDiagonalBlock Xσ j := by
    ext a b
    simp [diagonalBlock, sigmaDiagonalBlock, e]
  rw [hdiag, hwlen]
  rw [Matrix.smul_mul, Matrix.mul_smul]

/-- The boundary parametrization of a block-diagonal tensor on a block-diagonal
boundary condition is the sum of the corresponding block boundary
parametrizations:
\[
  \Gamma_L^{\oplus_j\mu_jA_j}\!\left(\bigoplus_j X_j\right)
  =
  \sum_j \Gamma_L^{A_j}(\mu_j^L X_j).
\]

This is the block-diagonal boundary-condition identity used in PGVWC07,
Theorem 2blocks.2, proof lines 1430--1434. -/
theorem groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ)
    (X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) L
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) =
      ∑ j : Fin r, groundSpaceMap (A j) L ((μ j) ^ L • X j) := by
  rw [groundSpaceMap_toTensorFromBlocks_eq_sum_diagonalBlock]
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 1
  ext a b
  simp [diagonalBlock, sigmaDiagonalBlock]

end BlockSumGroundSpace

open BlockSumGroundSpace

/-- One block's local ground space is contained in the local ground space of the
block-diagonal tensor when that block has nonzero weight.

This is the single-summand direction of the local identity
\[
  G_L\!\left(\bigoplus_k\mu_kA_k\right)=\bigvee_kG_L(A_k).
\] -/
theorem groundSpace_block_le_toTensorFromBlocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {j : Fin r} (hμj : μ j ≠ 0) (L : ℕ) :
    groundSpace (A j) L ≤ groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L := by
  classical
  intro ψ hψ
  rw [groundSpace, LinearMap.mem_range] at hψ
  rcases hψ with ⟨X, rfl⟩
  rw [groundSpace, LinearMap.mem_range]
  let Yσ : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ :=
    Matrix.blockDiagonal' fun k : Fin r =>
      if h : k = j then
        (by
          subst k
          exact ((μ j) ^ L)⁻¹ • X)
      else
        0
  refine ⟨(Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) Yσ, ?_⟩
  ext σ
  rw [groundSpaceMap_toTensorFromBlocks_eq_sum_diagonalBlock]
  rw [Finset.sum_eq_single j]
  · have hpow : (μ j) ^ L ≠ 0 := pow_ne_zero L hμj
    have hdiag :
        diagonalBlock ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) Yσ) j =
          ((μ j) ^ L)⁻¹ • X := by
      ext a b
      simp [diagonalBlock, sigmaDiagonalBlock, Yσ]
    rw [hdiag]
    simp only [groundSpaceMap_apply]
    rw [smul_smul, mul_inv_cancel₀ hpow]
    simp
  · intro k _ hkj
    have hdiag :
        diagonalBlock ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) Yσ) k = 0 := by
      ext a b
      simp [diagonalBlock, sigmaDiagonalBlock, Yσ, hkj]
    rw [hdiag]
    simp
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

/-- The local ground space of a block-diagonal tensor is the linear sum of the local
ground spaces of its blocks:
\[
  G_L\!\left(\bigoplus_j \mu_j A_j\right)=\bigvee_j G_L(A_j).
\]

The reverse inclusion uses \(\mu_j\ne0\) to insert
\((\mu_j^L)^{-1}X\) in the \(j\)-th diagonal boundary block.  This is the
local identity \(G_L(B)=S_L\) used in the proof of PGVWC07, Theorem
2blocks.2. -/
theorem groundSpace_toTensorFromBlocks_eq_iSup
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0) (L : ℕ) :
    groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L =
      ⨆ j : Fin r, groundSpace (A j) L := by
  classical
  apply le_antisymm
  · intro ψ hψ
    rw [groundSpace, LinearMap.mem_range] at hψ
    rcases hψ with ⟨X, rfl⟩
    rw [groundSpaceMap_toTensorFromBlocks_eq_sum_diagonalBlock μ A L X]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.mem_iSup_of_mem j ⟨(μ j) ^ L • diagonalBlock X j, rfl⟩
  · exact iSup_le fun j => groundSpace_block_le_toTensorFromBlocks μ A (hμ j) L

end MPSTensor
