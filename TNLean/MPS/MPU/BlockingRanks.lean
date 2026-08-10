/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPU.SourceFactors

/-!
# Source-cut ranks under physical blocking

This module proves the blocking upper bounds for the right and left source-cut
ranks in the proof of Proposition `index-well-defined` of
[Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], lines 697--703.
The first pair of results bounds a direct block one site longer. Iteration gives
the factor $d^{k-k_0}$ between any two direct blocking lengths $k_0 \leq k$.

The orientations follow the paper: the right rank $r$ is the rank of
$\mathcal M_1$, while the left rank $\ell$ is the rank of $\mathcal M_2$.
No simplicity or MPU hypothesis is needed for these rank inequalities.
-/

open scoped BigOperators

namespace MPOTensor

variable {d D : ℕ}

private noncomputable def blockHead (k : ℕ)
    (I : Fin (MPSTensor.blockPhysDim d (k + 1))) : Fin d :=
  MPSTensor.decodeBlock d (k + 1) I 0

private noncomputable def blockTail (k : ℕ)
    (I : Fin (MPSTensor.blockPhysDim d (k + 1))) :
    Fin (MPSTensor.blockPhysDim d k) :=
  (MPSTensor.decodeBlockEquiv d k).symm
    (fun q : Fin k => MPSTensor.decodeBlock d (k + 1) I q.succ)

private lemma wordOfBlock_succ (k : ℕ)
    (I : Fin (MPSTensor.blockPhysDim d (k + 1))) :
    MPSTensor.wordOfBlock d (k + 1) I =
      blockHead k I :: MPSTensor.wordOfBlock d k (blockTail k I) := by
  simp [MPSTensor.wordOfBlock, blockHead, blockTail, List.ofFn_succ]

private lemma blockTensor_succ_apply (U : MPOTensor d D) (k : ℕ)
    (I J : Fin (MPSTensor.blockPhysDim d (k + 1))) :
    blockTensor U (k + 1) I J =
      U (blockHead k I) (blockHead k J) *
        blockTensor U k (blockTail k I) (blockTail k J) := by
  simp only [blockTensor_apply, wordOfBlock_succ, evalWord_cons]

private noncomputable def rightSuccLeft (U : MPOTensor d D) (k : ℕ) :
    Matrix (Fin D × Fin (MPSTensor.blockPhysDim d (k + 1)))
      (Fin d × Fin r[blockTensor U k]) ℂ :=
  fun (α, J) (i, q) =>
    ∑ γ : Fin D, U i (blockHead k J) α γ *
      Matrix.conjTranspose (sourceSVD₁ (blockTensor U k)).V (γ, blockTail k J) q

private noncomputable def rightSuccRight (U : MPOTensor d D) (k : ℕ) :
    Matrix (Fin d × Fin r[blockTensor U k])
      (Fin (MPSTensor.blockPhysDim d (k + 1)) × Fin D) ℂ :=
  fun (i, q) (I, β) =>
    if i = blockHead k I then
      ((sourceSVD₁ (blockTensor U k)).diagonal *
        (sourceSVD₁ (blockTensor U k)).U) q (blockTail k I, β)
    else 0

private theorem sourceCutM₁_blockTensor_succ_factorization
    (U : MPOTensor d D) (k : ℕ) :
    sourceCutM₁ (blockTensor U (k + 1)) =
      rightSuccLeft U k * rightSuccRight U k := by
  classical
  let S := sourceSVD₁ (blockTensor U k)
  have hfactor : sourceCutM₁ (blockTensor U k) =
      Matrix.conjTranspose S.V * (S.diagonal * S.U) := by
    simpa [S, Matrix.mul_assoc] using S.factorization
  have hfactor_apply (row : Fin D × Fin (MPSTensor.blockPhysDim d k))
      (col : Fin (MPSTensor.blockPhysDim d k) × Fin D) :
      ∑ q, Matrix.conjTranspose S.V row q * (S.diagonal * S.U) q col =
        sourceCutM₁ (blockTensor U k) row col := by
    have h := congrArg (fun M => M row col) hfactor
    simpa only [Matrix.mul_apply] using h.symm
  ext ⟨α, J⟩ ⟨I, β⟩
  symm
  simp only [sourceCutM₁_apply, Matrix.mul_apply, rightSuccLeft, rightSuccRight]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single (blockHead k I)]
  · simp only [if_pos]
    change (∑ q, (∑ γ, U (blockHead k I) (blockHead k J) α γ *
      Matrix.conjTranspose S.V (γ, blockTail k J) q) *
        (S.diagonal * S.U) q (blockTail k I, β)) = _
    calc
      ∑ q, (∑ γ, U (blockHead k I) (blockHead k J) α γ *
          Matrix.conjTranspose S.V (γ, blockTail k J) q) *
          (S.diagonal * S.U) q (blockTail k I, β) =
          ∑ γ, U (blockHead k I) (blockHead k J) α γ *
            ∑ q, Matrix.conjTranspose S.V (γ, blockTail k J) q *
              (S.diagonal * S.U) q (blockTail k I, β) := by
            simp only [Finset.sum_mul, mul_assoc]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro γ _
            rw [Finset.mul_sum]
      _ = ∑ γ, U (blockHead k I) (blockHead k J) α γ *
            sourceCutM₁ (blockTensor U k) (γ, blockTail k J)
              (blockTail k I, β) := by
            apply Finset.sum_congr rfl
            intro γ _
            rw [hfactor_apply]
      _ = (U (blockHead k I) (blockHead k J) *
            blockTensor U k (blockTail k I) (blockTail k J)) α β := by
            simp only [sourceCutM₁_apply, Matrix.mul_apply]
      _ = blockTensor U (k + 1) I J α β := by
            rw [blockTensor_succ_apply]
  · intro i hi
    simp [hi]

private noncomputable def leftSuccLeft (U : MPOTensor d D) (k : ℕ) :
    Matrix (Fin D × Fin (MPSTensor.blockPhysDim d (k + 1)))
      (Fin d × Fin ℓ[blockTensor U k]) ℂ :=
  fun (α, I) (j, q) =>
    ∑ γ : Fin D, U (blockHead k I) j α γ *
      Matrix.conjTranspose (sourceSVD₂ (blockTensor U k)).V (γ, blockTail k I) q

private noncomputable def leftSuccRight (U : MPOTensor d D) (k : ℕ) :
    Matrix (Fin d × Fin ℓ[blockTensor U k])
      (Fin (MPSTensor.blockPhysDim d (k + 1)) × Fin D) ℂ :=
  fun (j, q) (J, β) =>
    if j = blockHead k J then
      ((sourceSVD₂ (blockTensor U k)).diagonal *
        (sourceSVD₂ (blockTensor U k)).U) q (blockTail k J, β)
    else 0

private theorem sourceCutM₂_blockTensor_succ_factorization
    (U : MPOTensor d D) (k : ℕ) :
    sourceCutM₂ (blockTensor U (k + 1)) =
      leftSuccLeft U k * leftSuccRight U k := by
  classical
  let S := sourceSVD₂ (blockTensor U k)
  have hfactor : sourceCutM₂ (blockTensor U k) =
      Matrix.conjTranspose S.V * (S.diagonal * S.U) := by
    simpa [S, Matrix.mul_assoc] using S.factorization
  have hfactor_apply (row : Fin D × Fin (MPSTensor.blockPhysDim d k))
      (col : Fin (MPSTensor.blockPhysDim d k) × Fin D) :
      ∑ q, Matrix.conjTranspose S.V row q * (S.diagonal * S.U) q col =
        sourceCutM₂ (blockTensor U k) row col := by
    have h := congrArg (fun M => M row col) hfactor
    simpa only [Matrix.mul_apply] using h.symm
  ext ⟨α, I⟩ ⟨J, β⟩
  symm
  simp only [sourceCutM₂_apply, Matrix.mul_apply, leftSuccLeft, leftSuccRight]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single (blockHead k J)]
  · simp only [if_pos]
    change (∑ q, (∑ γ, U (blockHead k I) (blockHead k J) α γ *
      Matrix.conjTranspose S.V (γ, blockTail k I) q) *
        (S.diagonal * S.U) q (blockTail k J, β)) = _
    calc
      ∑ q, (∑ γ, U (blockHead k I) (blockHead k J) α γ *
          Matrix.conjTranspose S.V (γ, blockTail k I) q) *
          (S.diagonal * S.U) q (blockTail k J, β) =
          ∑ γ, U (blockHead k I) (blockHead k J) α γ *
            ∑ q, Matrix.conjTranspose S.V (γ, blockTail k I) q *
              (S.diagonal * S.U) q (blockTail k J, β) := by
            simp only [Finset.sum_mul, mul_assoc]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro γ _
            rw [Finset.mul_sum]
      _ = ∑ γ, U (blockHead k I) (blockHead k J) α γ *
            sourceCutM₂ (blockTensor U k) (γ, blockTail k I)
              (blockTail k J, β) := by
            apply Finset.sum_congr rfl
            intro γ _
            rw [hfactor_apply]
      _ = (U (blockHead k I) (blockHead k J) *
            blockTensor U k (blockTail k I) (blockTail k J)) α β := by
            simp only [sourceCutM₂_apply, Matrix.mul_apply]
      _ = blockTensor U (k + 1) I J α β := by
            rw [blockTensor_succ_apply]
  · intro j hj
    simp [hj]

/-- Blocking one additional site multiplies the right source-cut rank by at most $d$.

This is the one-site form of the right-rank upper bound in the proof of
arXiv:1703.09188, Proposition `index-well-defined`, lines 697--703. -/
theorem rightRank_blockTensor_succ_le (U : MPOTensor d D) (k : ℕ) :
    r[blockTensor U (k + 1)] ≤ d * r[blockTensor U k] := by
  rw [rightRank, sourceCutM₁_blockTensor_succ_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width (rightSuccLeft U k)).trans_eq (by simp))

/-- Blocking one additional site multiplies the left source-cut rank by at most $d$.

This is the one-site form of the left-rank upper bound in the proof of
arXiv:1703.09188, Proposition `index-well-defined`, lines 697--703. -/
theorem leftRank_blockTensor_succ_le (U : MPOTensor d D) (k : ℕ) :
    ℓ[blockTensor U (k + 1)] ≤ d * ℓ[blockTensor U k] := by
  rw [leftRank, sourceCutM₂_blockTensor_succ_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width (leftSuccLeft U k)).trans_eq (by simp))

/-- Between direct blocking lengths $k_0 \leq k$, the right rank grows by at most
$d^{k-k_0}$.

This is the right-rank inequality in the proof of arXiv:1703.09188,
Proposition `index-well-defined`, lines 697--703. -/
theorem rightRank_blockTensor_le_pow_mul (U : MPOTensor d D) {k₀ k : ℕ}
    (h : k₀ ≤ k) :
    r[blockTensor U k] ≤ d ^ (k - k₀) * r[blockTensor U k₀] := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
      calc
        r[blockTensor U (k + 1)] ≤ d * r[blockTensor U k] :=
          rightRank_blockTensor_succ_le U k
        _ ≤ d * (d ^ (k - k₀) * r[blockTensor U k₀]) :=
          Nat.mul_le_mul_left d ih
        _ = d ^ (k + 1 - k₀) * r[blockTensor U k₀] := by
          rw [Nat.succ_sub (by omega), pow_succ]
          simp [Nat.mul_assoc, Nat.mul_comm]

/-- Between direct blocking lengths $k_0 \leq k$, the left rank grows by at most
$d^{k-k_0}$.

This is the left-rank inequality in the proof of arXiv:1703.09188,
Proposition `index-well-defined`, lines 697--703. -/
theorem leftRank_blockTensor_le_pow_mul (U : MPOTensor d D) {k₀ k : ℕ}
    (h : k₀ ≤ k) :
    ℓ[blockTensor U k] ≤ d ^ (k - k₀) * ℓ[blockTensor U k₀] := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
      calc
        ℓ[blockTensor U (k + 1)] ≤ d * ℓ[blockTensor U k] :=
          leftRank_blockTensor_succ_le U k
        _ ≤ d * (d ^ (k - k₀) * ℓ[blockTensor U k₀]) :=
          Nat.mul_le_mul_left d ih
        _ = d ^ (k + 1 - k₀) * ℓ[blockTensor U k₀] := by
          rw [Nat.succ_sub (by omega), pow_succ]
          simp [Nat.mul_assoc, Nat.mul_comm]

end MPOTensor
