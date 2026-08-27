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
ranks in the proof of Proposition IV.2 (`index-well-defined`) of
[Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], lines 697--703.
The first pair of results bounds a direct block one site longer. Iteration gives
the factor $d^{k-k_0}$ between any two direct blocking lengths $k_0 \leq k$.

The orientations follow the paper: the right rank $r$ is the rank of
$\mathcal M_1$, while the left rank $\ell$ is the rank of $\mathcal M_2$.
No simplicity or MPU hypothesis is needed for these rank inequalities.

## Main results

* `rightRank_blockTensor_succ_le`: one-site right-rank bound.
* `leftRank_blockTensor_succ_le`: one-site left-rank bound.
* `rightRank_blockTensor_le_pow_mul`: iterated right-rank bound.
* `leftRank_blockTensor_le_pow_mul`: iterated left-rank bound.
* `blockingRanks_eq_pow_mul_of_products`: simultaneous exact rank growth.
* `rightRank_blockTensor_eq_pow_mul_of_products`: exact right-rank growth.
* `leftRank_blockTensor_eq_pow_mul_of_products`: exact left-rank growth.
-/

open scoped BigOperators

namespace MPOTensor

variable {d D : ℕ}

private noncomputable def blockHead (k : ℕ)
    (I : Fin (Kraus.blockPhysDim d (k + 1))) : Fin d :=
  Kraus.decodeBlock d (k + 1) I 0

private noncomputable def blockTail (k : ℕ)
    (I : Fin (Kraus.blockPhysDim d (k + 1))) :
    Fin (Kraus.blockPhysDim d k) :=
  (Kraus.decodeBlockEquiv d k).symm
    (fun q : Fin k => Kraus.decodeBlock d (k + 1) I q.succ)

private lemma wordOfBlock_succ (k : ℕ)
    (I : Fin (Kraus.blockPhysDim d (k + 1))) :
    Kraus.wordOfBlock d (k + 1) I =
      blockHead k I :: Kraus.wordOfBlock d k (blockTail k I) := by
  simp [Kraus.wordOfBlock, blockHead, blockTail, List.ofFn_succ]

private lemma blockTensor_succ_apply (U : MPOTensor d D) (k : ℕ)
    (I J : Fin (Kraus.blockPhysDim d (k + 1))) :
    blockTensor U (k + 1) I J =
      U (blockHead k I) (blockHead k J) *
        blockTensor U k (blockTail k I) (blockTail k J) := by
  simp only [blockTensor_apply, wordOfBlock_succ, evalWord_cons]

private lemma sourceCutSVD_factorization_apply
    {α β : Type*} [Fintype α] [Fintype β] {M : Matrix α β ℂ} {r : ℕ}
    (S : SourceCutSVD M r) (row : α) (col : β) :
    ∑ q, Matrix.conjTranspose S.V row q * (S.diagonal * S.U) q col = M row col := by
  have hfactor : M = Matrix.conjTranspose S.V * (S.diagonal * S.U) := by
    simpa only [Matrix.mul_assoc] using S.factorization
  have h := congrArg (fun A => A row col) hfactor
  simpa only [Matrix.mul_apply] using h.symm

private noncomputable def rightSuccLeft (U : MPOTensor d D) (k : ℕ) :
    Matrix (Fin D × Fin (Kraus.blockPhysDim d (k + 1)))
      (Fin d × Fin r[blockTensor U k]) ℂ :=
  fun (α, J) (i, q) =>
    ∑ γ : Fin D, U i (blockHead k J) α γ *
      Matrix.conjTranspose (sourceSVD₁ (blockTensor U k)).V (γ, blockTail k J) q

private noncomputable def rightSuccRight (U : MPOTensor d D) (k : ℕ) :
    Matrix (Fin d × Fin r[blockTensor U k])
      (Fin (Kraus.blockPhysDim d (k + 1)) × Fin D) ℂ :=
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
  ext ⟨α, J⟩ ⟨I, β⟩
  symm
  simp only [sourceCutM₁_apply, Matrix.mul_apply, rightSuccLeft, rightSuccRight]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single (blockHead k I)]
  · simp only [ite_eq_left]
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
            rw [sourceCutSVD_factorization_apply S]
      _ = (U (blockHead k I) (blockHead k J) *
            blockTensor U k (blockTail k I) (blockTail k J)) α β := by
            simp only [sourceCutM₁_apply, Matrix.mul_apply]
      _ = blockTensor U (k + 1) I J α β := by
            rw [blockTensor_succ_apply]
  · intro i hi
    simp [hi]

/-- Blocking one additional site multiplies the right source-cut rank by at most $d$.

This is the one-site form of the right-rank upper bound in the proof of
arXiv:1703.09188, Proposition IV.2 (`index-well-defined`), lines 697--703. -/
theorem rightRank_blockTensor_succ_le (U : MPOTensor d D) (k : ℕ) :
    r[blockTensor U (k + 1)] ≤ d * r[blockTensor U k] := by
  rw [rightRank, sourceCutM₁_blockTensor_succ_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width (rightSuccLeft U k)).trans_eq (by simp))

/-- Blocking one additional site multiplies the left source-cut rank by at most $d$.

This is the one-site form of the left-rank upper bound in the proof of
arXiv:1703.09188, Proposition IV.2 (`index-well-defined`), lines 697--703. -/
theorem leftRank_blockTensor_succ_le (U : MPOTensor d D) (k : ℕ) :
    ℓ[blockTensor U (k + 1)] ≤ d * ℓ[blockTensor U k] := by
  calc ℓ[blockTensor U (k + 1)]
      = r[blockTensor (physicalAdjointTensor U) (k + 1)] := by
        rw [← physicalAdjointTensor_blockTensor,
          rightRank_physicalAdjointTensor]
    _ ≤ d * r[blockTensor (physicalAdjointTensor U) k] :=
        rightRank_blockTensor_succ_le (physicalAdjointTensor U) k
    _ = d * ℓ[blockTensor U k] := by
        rw [← physicalAdjointTensor_blockTensor,
          rightRank_physicalAdjointTensor]

/-- Between direct blocking lengths $k_0 \leq k$, the right rank grows by at most
$d^{k-k_0}$.

This is the right-rank inequality in the proof of arXiv:1703.09188,
Proposition IV.2 (`index-well-defined`), lines 697--703. -/
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
Proposition IV.2 (`index-well-defined`), lines 697--703. -/
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

/-- If the endpoint right--left rank products have their physical-dimension
values, then both blocking rank bounds are saturated.

This is the arithmetic saturation step in the proof of arXiv:1703.09188,
Proposition IV.2 (`index-well-defined`), line 703. The endpoint product
identities are supplied explicitly; a later application of the paper's
fundamental theorem will establish them for simple MPU blocks.

**Local fix (rank-product exponent):** Source line 703 prints $d^k$; consistently
with Theorem III.8 and the blocked physical dimension $d^k$, the endpoint
product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`. -/
theorem blockingRanks_eq_pow_mul_of_products (U : MPOTensor d D) {k₀ k : ℕ}
    (h : k₀ ≤ k) (hd : 0 < d)
    (hprod₀ : r[blockTensor U k₀] * ℓ[blockTensor U k₀] = d ^ (2 * k₀))
    (hprod : r[blockTensor U k] * ℓ[blockTensor U k] = d ^ (2 * k)) :
    r[blockTensor U k] = d ^ (k - k₀) * r[blockTensor U k₀] ∧
      ℓ[blockTensor U k] = d ^ (k - k₀) * ℓ[blockTensor U k₀] := by
  apply eq_and_eq_of_pos_of_le_of_mul_le_mul
  · exact Nat.pos_of_mul_pos_right (hprod.symm ▸ Nat.pow_pos hd)
  · exact Nat.pos_of_mul_pos_left (hprod.symm ▸ Nat.pow_pos hd)
  · exact rightRank_blockTensor_le_pow_mul U h
  · exact leftRank_blockTensor_le_pow_mul U h
  · rw [hprod]
    calc
      d ^ (k - k₀) * r[blockTensor U k₀] *
          (d ^ (k - k₀) * ℓ[blockTensor U k₀]) =
          d ^ (2 * (k - k₀)) *
            (r[blockTensor U k₀] * ℓ[blockTensor U k₀]) := by ring
      _ = d ^ (2 * (k - k₀)) * d ^ (2 * k₀) := by rw [hprod₀]
      _ = d ^ (2 * k) := by
        rw [← pow_add]
        congr 1
        omega
    exact le_rfl

/-- The right source-cut rank attains its blocking upper bound when
$r_{k₀}\ell_{k₀}=d^{2k₀}$ and $r_k\ell_k=d^{2k}$.

This is the right-rank conclusion of the saturation step in the proof of
arXiv:1703.09188, Proposition IV.2 (`index-well-defined`), line 703.

**Local fix (rank-product exponent):** Source line 703 prints $d^k$; consistently
with Theorem III.8 and the blocked physical dimension $d^k$, the endpoint
product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`. -/
theorem rightRank_blockTensor_eq_pow_mul_of_products (U : MPOTensor d D) {k₀ k : ℕ}
    (h : k₀ ≤ k) (hd : 0 < d)
    (hprod₀ : r[blockTensor U k₀] * ℓ[blockTensor U k₀] = d ^ (2 * k₀))
    (hprod : r[blockTensor U k] * ℓ[blockTensor U k] = d ^ (2 * k)) :
    r[blockTensor U k] = d ^ (k - k₀) * r[blockTensor U k₀] :=
  (blockingRanks_eq_pow_mul_of_products U h hd hprod₀ hprod).1

/-- The left source-cut rank attains its blocking upper bound when
$r_{k₀}\ell_{k₀}=d^{2k₀}$ and $r_k\ell_k=d^{2k}$.

This is the left-rank conclusion of the saturation step in the proof of
arXiv:1703.09188, Proposition IV.2 (`index-well-defined`), line 703.

**Local fix (rank-product exponent):** Source line 703 prints $d^k$; consistently
with Theorem III.8 and the blocked physical dimension $d^k$, the endpoint
product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`. -/
theorem leftRank_blockTensor_eq_pow_mul_of_products (U : MPOTensor d D) {k₀ k : ℕ}
    (h : k₀ ≤ k) (hd : 0 < d)
    (hprod₀ : r[blockTensor U k₀] * ℓ[blockTensor U k₀] = d ^ (2 * k₀))
    (hprod : r[blockTensor U k] * ℓ[blockTensor U k] = d ^ (2 * k)) :
    ℓ[blockTensor U k] = d ^ (k - k₀) * ℓ[blockTensor U k₀] :=
  (blockingRanks_eq_pow_mul_of_products U h hd hprod₀ hprod).2

end MPOTensor
