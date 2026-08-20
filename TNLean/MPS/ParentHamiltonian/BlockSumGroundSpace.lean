/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DependentBlockDiagonal
import TNLean.Algebra.MatrixAux
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.SharedInfra.BoundaryDecomposition

/-!
# Local spaces of block-diagonal tensors

This file identifies the local MPS space \(G_L\) of a block-diagonal tensor with
the linear sum of the corresponding local spaces of its blocks.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12,
  proof lines 1430--1434, where
  \(S=\bigoplus_j\mathcal G_L^{A^j}\).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

namespace BlockSumGroundSpace

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The boundary parametrization of a block-diagonal tensor is the sum of the block
boundary parametrizations applied to the diagonal boundary blocks. -/
theorem groundSpaceMap_toTensorFromBlocks_eq_sum_diagonalBlock
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j)) (L : ℕ)
    (X : Matrix (Fin (∑ j : Fin r, dim j)) (Fin (∑ j : Fin r, dim j)) ℂ) :
    groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) L X =
      ∑ j : Fin r, groundSpaceMap (A j) L
        ((μ j) ^ L • Matrix.finSigmaDiagonalBlock X j) := by
  ext σ
  simp only [groundSpaceMap_apply, Finset.sum_apply]
  rw [trace_evalWord_toTensorFromBlocks_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [List.length_ofFn, Matrix.smul_mul, Matrix.mul_smul]

/-- The boundary parametrization of a block-diagonal tensor on a block-diagonal
boundary condition is the sum of the corresponding block boundary
parametrizations:
\[
  \Gamma_L^{\oplus_j\mu_jA_j}\!\left(\bigoplus_j X_j\right)
  =
  \sum_j \Gamma_L^{A_j}(\mu_j^L X_j).
\]

This is the block-diagonal boundary-condition identity used in PGVWC07,
Theorem 12, proof lines 1430--1434. -/
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
  simp [Matrix.finSigmaDiagonalBlock]

/-- A vector in the sum of the open-boundary block spaces has one
block-diagonal boundary matrix for the weighted direct-sum tensor. The
component represented by each diagonal block remains in its corresponding
open-boundary space. -/
theorem exists_blockDiagonal_boundary_of_mem_iSup_groundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0) {L : ℕ} {ψ : NSiteSpace d L}
    (hψ : ψ ∈ ⨆ j : Fin r, groundSpace (A j) L) :
    ∃ X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ,
      ψ = groundSpaceMap (toTensorFromBlocks (d := d) (μ := μ) A) L
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' X)) ∧
      ∀ j : Fin r,
        groundSpaceMap (A j) L ((μ j) ^ L • X j) ∈ groundSpace (A j) L := by
  classical
  obtain ⟨φ, hφ, hφsum⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp
      (fun j : Fin r => groundSpace (A j) L) ψ).mp hψ
  have hψφ : ψ = ∑ j : Fin r, φ j := by
    simpa [Finsupp.sum_fintype] using hφsum.symm
  have hφRange : ∀ j : Fin r, φ j ∈ (groundSpaceMap (A j) L).range := by
    intro j
    simpa [groundSpace] using hφ j
  choose Y hY using hφRange
  let X : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j => ((μ j) ^ L)⁻¹ • Y j
  refine ⟨X, ?_, ?_⟩
  · rw [groundSpaceMap_toTensorFromBlocks_eq_sum_blockDiagonal]
    calc
      ψ = ∑ j : Fin r, φ j := hψφ
      _ = ∑ j : Fin r, groundSpaceMap (A j) L ((μ j) ^ L • X j) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        have hpow : (μ j) ^ L ≠ 0 := pow_ne_zero L (hμ j)
        simp [X, hY j, hpow]
  · intro j
    have hpow : (μ j) ^ L ≠ 0 := pow_ne_zero L (hμ j)
    simpa [X, hY j, hpow] using hφ j

end BlockSumGroundSpace

open BlockSumGroundSpace

/-- One block's local space is contained in the local space of the block-diagonal
tensor when that block has nonzero weight.

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
        Matrix.finSigmaDiagonalBlock
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) Yσ) j =
          ((μ j) ^ L)⁻¹ • X := by
      ext a b
      simp [Matrix.finSigmaDiagonalBlock, Yσ]
    rw [hdiag]
    simp only [groundSpaceMap_apply]
    rw [smul_smul, mul_inv_cancel₀ hpow]
    simp
  · intro k _ hkj
    have hdiag :
        Matrix.finSigmaDiagonalBlock
            ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) Yσ) k = 0 := by
      ext a b
      simp [Matrix.finSigmaDiagonalBlock, Yσ, hkj]
    rw [hdiag]
    simp
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

/-- The local space of a block-diagonal tensor is the linear sum of the local
spaces of its blocks:
\[
  G_L\!\left(\bigoplus_j \mu_j A_j\right)=\bigvee_j G_L(A_j).
\]

The reverse inclusion uses \(\mu_j\ne0\) to insert
\((\mu_j^L)^{-1}X\) in the \(j\)-th diagonal boundary block.  This is the
local identity \(G_L(B)=S_L\) used in the proof of PGVWC07,
Theorem 12. -/
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
    exact Submodule.mem_iSup_of_mem j
      ⟨(μ j) ^ L • Matrix.finSigmaDiagonalBlock X j, rfl⟩
  · exact iSup_le fun j => groundSpace_block_le_toTensorFromBlocks μ A (hμ j) L

end MPSTensor
