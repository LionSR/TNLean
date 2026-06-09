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
2blocks.2, before the directness of the block summands is used. -/
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
