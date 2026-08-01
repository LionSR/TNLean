/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Entropy.MutualInformationOperatorSchmidt
import TNLean.MPS.MPDO.MutualInfoBridge

/-!
# Finite-chain mutual-information bound for matrix product operators

This file bounds the mutual information across every contiguous cut of a fixed
positive matrix product operator by twice the natural logarithm of its operator
bond dimension. The proof combines the bipartite interpretation of the chain
mutual information with the ordinary operator-Schmidt-rank bound across the two
virtual bonds.

The result concerns each fixed finite chain. It makes no assertion about a
thermodynamic limit of the mutual information.

## Main declarations

* `MPOTensor.mutualInfoChain_le_two_log_bondDim`: the sharp finite-chain bound
  in the operator bond dimension.
* `MPOTensor.mutualInfoChain_le_four_log_bondDim`: the source-facing
  coefficient appearing in arXiv:1606.00608, Proposition 4.5.
* `MPOTensor.IsMPDO.mutualInfoChain_le_two_log_bondDim`: the family-level
  specialization for a positive chain length.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

private theorem bondDim_pos_of_mpo_trace_ne_zero
    (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (htr : (mpo M N).trace ≠ 0) :
    0 < D := by
  let ρ := bipartitionedNormalizedMPO M N L (N - L) (by omega)
  have hρtr : ρ.trace = 1 :=
    bipartitionedNormalizedMPO_trace M N L (N - L) (by omega) htr
  have hρne : ρ ≠ 0 := by
    intro hzero
    have : (0 : ℂ) = 1 := by simpa only [hzero, Matrix.trace_zero] using hρtr
    exact zero_ne_one this
  have hrank_pos : 0 < Matrix.operatorSchmidtRank ρ :=
    Matrix.operatorSchmidtRank_pos_of_ne_zero ρ hρne
  have hrank_le : Matrix.operatorSchmidtRank ρ ≤ D * D :=
    operatorSchmidtRank_bipartitionedNormalizedMPO_le M N L (N - L) (by omega)
  have hDD : 0 < D * D := lt_of_lt_of_le hrank_pos hrank_le
  exact Nat.pos_of_mul_pos_right hDD

/-- The mutual information across any contiguous cut of a fixed positive
length-`N` MPO operator with nonzero trace is at most twice the natural
logarithm of the MPO tensor's operator bond dimension:
\[
  I_L(M,N) \leq 2\log D.
\]

No positive-chain-length, interior-cut, global MPDO, local-purification,
canonical-form, or positive-bond-dimension assumption is needed. Positivity of
`D` follows from the nonzero normalized state and the estimate that its
ordinary operator-Schmidt rank is at most `D²`. Endpoint cuts are included.

This strengthens the finite-chain estimate in arXiv:1606.00608,
Proposition 4.5, lines 795--809 and 1316--1321. -/
theorem mutualInfoChain_le_two_log_bondDim
    (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef)
    (htr : (mpo M N).trace ≠ 0) :
    mutualInfoChain M N L hL hM ≤ 2 * Real.log D := by
  let ρ := bipartitionedNormalizedMPO M N L (N - L) (by omega)
  have hρpos : ρ.PosSemidef :=
    bipartitionedNormalizedMPO_posSemidef M N L (N - L) (by omega) hM
  have hρtr : ρ.trace = 1 :=
    bipartitionedNormalizedMPO_trace M N L (N - L) (by omega) htr
  have hρne : ρ ≠ 0 := by
    intro hzero
    have : (0 : ℂ) = 1 := by simpa only [hzero, Matrix.trace_zero] using hρtr
    exact zero_ne_one this
  have hrank_pos : 0 < Matrix.operatorSchmidtRank ρ :=
    Matrix.operatorSchmidtRank_pos_of_ne_zero ρ hρne
  have hrank_le : Matrix.operatorSchmidtRank ρ ≤ D * D :=
    operatorSchmidtRank_bipartitionedNormalizedMPO_le M N L (N - L) (by omega)
  have hD : 0 < D :=
    bondDim_pos_of_mpo_trace_ne_zero M N L hL htr
  rw [mutualInfoChain_eq_mutualInformation M N L hL hM]
  calc
    Entropy.mutualInformation ρ hρpos.isHermitian ≤
        Real.log (Matrix.operatorSchmidtRank ρ) :=
      Entropy.mutualInformation_le_log_operatorSchmidtRank ρ ⟨hρpos, hρtr⟩
    _ ≤ Real.log ((D : ℝ) * D) := by
      apply Real.log_le_log (by exact_mod_cast hrank_pos)
      rw [← Nat.cast_mul]
      exact_mod_cast hrank_le
    _ = 2 * Real.log D := by
      rw [Real.log_mul (by exact_mod_cast hD.ne') (by exact_mod_cast hD.ne')]
      ring

/-- The finite-chain estimate with the coefficient `4` stated in
arXiv:1606.00608, Proposition 4.5. This is a thin consequence of the stronger
bound `I_L(M,N) ≤ 2 log D`; it concerns a fixed chain only and does not include
the proposition's thermodynamic-limit assertion. -/
theorem mutualInfoChain_le_four_log_bondDim
    (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef)
    (htr : (mpo M N).trace ≠ 0) :
    mutualInfoChain M N L hL hM ≤ 4 * Real.log D := by
  have hD : 0 < D :=
    bondDim_pos_of_mpo_trace_ne_zero M N L hL htr
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  exact (mutualInfoChain_le_two_log_bondDim M N L hL hM htr).trans (by linarith)

/-- An MPDO has the finite-chain mutual-information bound
`I_L(M,N) ≤ 2 log D` at every positive chain length with nonzero trace, where
`D` is the operator bond dimension. -/
theorem IsMPDO.mutualInfoChain_le_two_log_bondDim
    {M : MPOTensor d D} (hM : IsMPDO M) (N L : ℕ) (hN : 0 < N)
    (hL : L ≤ N) (htr : (mpo M N).trace ≠ 0) :
    mutualInfoChain M N L hL (hM N hN) ≤ 2 * Real.log D :=
  _root_.MPOTensor.mutualInfoChain_le_two_log_bondDim M N L hL (hM N hN) htr

end MPOTensor
