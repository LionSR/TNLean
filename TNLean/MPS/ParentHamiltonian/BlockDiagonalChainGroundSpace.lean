/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockSumGroundSpace
import TNLean.MPS.ParentHamiltonian.CyclicSubmoduleIteration

/-!
# Chain constraints for block-diagonal tensors

This file combines the local block-diagonal ground-space identity with the
abstract cyclic-to-open propagation step used in the parent-Hamiltonian proof
of PGVWC07, Theorem 2blocks.2.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- The periodic chain ground space of a single block is contained in the
periodic chain ground space of the block-diagonal tensor.

For every cyclic window, the local identity
\[
  G_L\!\left(\bigoplus_k\mu_kA_k\right)=\bigvee_kG_L(A_k)
\]
sends \(G_L(A_j)\) into the local ground space of the block-diagonal tensor. -/
theorem chainGroundSpace_block_le_toTensorFromBlocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    {j : Fin r} (hμj : μ j ≠ 0)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    chainGroundSpace (A j) L N ≤
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N := by
  classical
  intro ψ hψ
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ ⊢
  intro i τ
  have hlocal : groundSpace (A j) L ≤
      groundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L := by
    exact groundSpace_block_le_toTensorFromBlocks μ A hμj L
  exact hlocal (hψ i τ)

/-- The sum of the blockwise periodic chain ground spaces is contained in the
periodic chain ground space of the block-diagonal tensor. -/
theorem iSup_chainGroundSpace_block_le_toTensorFromBlocks
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) :
    (⨆ j : Fin r, chainGroundSpace (A j) L N) ≤
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N := by
  exact iSup_le fun j =>
    chainGroundSpace_block_le_toTensorFromBlocks μ A (hμ j) hN hLN

/-- Boundary-condition equality for the block-diagonal periodic chain.

Let \(B=\bigoplus_j\mu_jA_j\). If closing the periodic boundary with
block-diagonal boundary conditions gives
\[
  \mathcal G_{N,L}(B)\subseteq\bigvee_j\mathcal G_{N,L}(A_j),
\]
then the already proved blockwise inclusion gives
\[
  \mathcal G_{N,L}(B)=\bigvee_j\mathcal G_{N,L}(A_j).
\]
This states the boundary-condition comparison for the block-diagonal periodic
chain as a single hypothesis; it does not prove that hypothesis. See
`docs/paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex`. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_chainGroundSpace_of_boundary_closing
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N)
    (hClose :
      chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
        ⨆ j : Fin r, chainGroundSpace (A j) L N) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N =
      ⨆ j : Fin r, chainGroundSpace (A j) L N :=
  le_antisymm hClose (iSup_chainGroundSpace_block_le_toTensorFromBlocks μ A hμ hN hLN)

/-- Periodic local constraints for a block-diagonal tensor propagate to the
linear sum of the block ground spaces.

Let \(B=\bigoplus_j\mu_jA_j\), with every \(\mu_j\ne0\), and set
\[
  S_M:=\bigvee_jG_M(A_j).
\]
If the sequence \(S_M\) satisfies
\[
  \mathbb C^d\otimes S_M\cap S_M\otimes\mathbb C^d=S_{M+1}
\]
for all \(M\ge L\), then
\[
  \mathcal G_{N,L}(B)\subseteq S_N.
\]
This is the conditional propagation step in the proof of PGVWC07, Theorem
12: the one-step identities propagate cyclic local constraints to
\(S_N\). The later source step is the boundary-condition comparison for
block-diagonal boundary conditions, replacing \(S_N\) by the periodic
block-chain sum. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_groundSpace
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j : Fin r, μ j ≠ 0)
    {L N : ℕ} (hN : 0 < N) (hL : 0 < L) (hLN : L ≤ N) [NeZero d]
    (hstep : ∀ M : ℕ, L ≤ M →
      ((⨅ b : Fin d,
          (⨆ j : Fin r, groundSpace (A j) M).comap (restrictLastₗ b)) ⊓
        (⨅ a : Fin d,
          (⨆ j : Fin r, groundSpace (A j) M).comap (restrictFirstₗ a))) =
        ⨆ j : Fin r, groundSpace (A j) (M + 1)) :
    chainGroundSpace (toTensorFromBlocks (d := d) (μ := μ) A) L N ≤
      ⨆ j : Fin r, groundSpace (A j) N := by
  classical
  let S : (M : ℕ) → Submodule ℂ (NSiteSpace d M) :=
    fun M => ⨆ j : Fin r, groundSpace (A j) M
  apply chainGroundSpace_le_of_local_le_restriction_intersection_submodules
    (A := toTensorFromBlocks (d := d) (μ := μ) A) (S := S) hN hL hLN
  · rw [groundSpace_toTensorFromBlocks_eq_iSup μ A hμ L]
  · intro M hM
    exact hstep M hM

end MPSTensor
