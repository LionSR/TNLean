/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.Entropy.MutualInformation.OperatorSchmidt
import TNLean.MPS.Operator.DensityOperator.AreaLaw

/-!
# Finite-chain mutual-information bound for matrix product operators

This file bounds the mutual information across every contiguous cut of a fixed
positive matrix product operator by twice the natural logarithm of its operator
bond dimension. Opening the two virtual bonds at the cut gives an
operator-Schmidt decomposition of the bipartitioned normalized state with
`D * D` product terms, and the mutual information of a bipartite state is at
most the logarithm of its operator-Schmidt rank.

The result concerns each fixed finite chain. It makes no assertion about a
thermodynamic limit of the mutual information.

## Main declarations

* `MPOTensor.bipartitionedNormalizedMPO_hasOperatorSchmidtDecomposition`,
  `MPOTensor.operatorSchmidtRank_bipartitionedNormalizedMPO_le`: the
  operator-Schmidt decomposition at a contiguous cut and its rank bound.
* `MPOTensor.mutualInfoChain_le_two_log_bondDim`: the sharp finite-chain bound
  in the operator bond dimension.
* `MPOTensor.IsMPDO.mutualInfoChain_le_four_log_bondDim`: the source-facing
  coefficient appearing in arXiv:1606.00608, Proposition 4.5.

## References

* arXiv:1606.00608, lines 792--797 and Appendix C, lines 1316--1321.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The left-block factor obtained by opening the two virtual bonds of a
periodic MPO at a contiguous cut.  The normalization scalar is absorbed into
this factor. -/
noncomputable def periodicCutLeftFactor (M : MPOTensor d D) (N L : ℕ)
    (a b : Fin D) : Matrix (Fin (d ^ L)) (Fin (d ^ L)) ℂ :=
  fun x x' ↦
    (mpo M N).trace⁻¹ *
      evalWord M (List.ofFn (finFunctionFinEquiv.symm x))
        (List.ofFn (finFunctionFinEquiv.symm x')) a b

/-- The right-block factor obtained by opening the two virtual bonds of a
periodic MPO at a contiguous cut. Its virtual indices are reversed because
\(\operatorname{tr}(AB) = \sum_{a,b} A_{ab} B_{ba}\). -/
noncomputable def periodicCutRightFactor (M : MPOTensor d D) (K : ℕ)
    (a b : Fin D) : Matrix (Fin (d ^ K)) (Fin (d ^ K)) ℂ :=
  fun y y' ↦
    evalWord M (List.ofFn (finFunctionFinEquiv.symm y))
      (List.ofFn (finFunctionFinEquiv.symm y')) b a

/-- Opening the two virtual bonds at a contiguous cut gives an explicit
operator-Schmidt decomposition of a normalized periodic MPO with `D * D`
product terms.

The statement is purely algebraic: it requires neither positivity nor a
nonzero trace. The factor `(mpo M N).trace⁻¹` uses the convention \(0⁻¹ = 0\),
so a zero trace makes every left factor zero. -/
theorem bipartitionedNormalizedMPO_hasOperatorSchmidtDecomposition
    (M : MPOTensor d D) (N L K : ℕ) (h : N = L + K) :
    Matrix.HasOperatorSchmidtDecomposition
      (bipartitionedNormalizedMPO M N L K h) (D * D) := by
  subst N
  refine ⟨fun t ↦ periodicCutLeftFactor M (L + K) L
      (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2,
    fun t ↦ periodicCutRightFactor M K
      (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2, ?_⟩
  ext ⟨x, y⟩ ⟨x', y'⟩
  rw [← finProdFinEquiv.sum_comp]
  simp [bipartitionedNormalizedMPO, normalizedMPO, chainBipartitionEquiv,
    biSplitEquiv, blockSplitEquiv_symm_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, periodicCutLeftFactor, periodicCutRightFactor,
    mpoMatrixEntry, List.ofFn_fin_append, evalWord_append, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The operator-Schmidt rank across a contiguous cut of a normalized periodic
MPO is at most the number \(D^2\) of ordered pairs of virtual-boundary indices.
No positivity or local-purification hypothesis is used. -/
theorem operatorSchmidtRank_bipartitionedNormalizedMPO_le
    (M : MPOTensor d D) (N L K : ℕ) (h : N = L + K) :
    Matrix.operatorSchmidtRank (bipartitionedNormalizedMPO M N L K h) ≤ D * D :=
  Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    (bipartitionedNormalizedMPO_hasOperatorSchmidtDecomposition M N L K h)

private theorem bondDim_pos_of_mpo_trace_ne_zero
    (M : MPOTensor d D) (N : ℕ) (htr : (mpo M N).trace ≠ 0) :
    0 < D := by
  apply Nat.pos_of_ne_zero
  intro hD
  subst D
  apply htr
  simp [mpo, mpoMatrixEntry, Matrix.trace]

/-- The mutual information across any contiguous cut of a fixed positive
length-`N` MPO operator with nonzero trace is at most twice the natural
logarithm of the MPO tensor's operator bond dimension:
\[
  I_L(M,N) \leq 2\log D.
\]

No positive-chain-length, interior-cut, global MPDO, local-purification,
canonical-form, or positive-bond-dimension assumption is needed. Positivity of
`D` follows because a zero-dimensional bond gives a zero finite-chain trace.
The cuts `L = 0` and `L = N` are included.

This strengthens the finite-chain estimate invoked in the proof of
arXiv:1606.00608, Proposition 4.5; see the normalization convention at lines
792--797 and the Appendix argument at lines 1316--1321. -/
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
    bondDim_pos_of_mpo_trace_ne_zero M N htr
  calc
    mutualInfoChain M N L hL hM = Entropy.mutualInformation ρ hρpos.isHermitian := rfl
    _ ≤ Real.log (Matrix.operatorSchmidtRank ρ) :=
      Entropy.mutualInformation_le_log_operatorSchmidtRank ρ ⟨hρpos, hρtr⟩
    _ ≤ Real.log ((D : ℝ) * D) := by
      apply Real.log_le_log (by exact_mod_cast hrank_pos)
      rw [← Nat.cast_mul]
      exact_mod_cast hrank_le
    _ = 2 * Real.log D := by
      rw [Real.log_mul (by exact_mod_cast hD.ne') (by exact_mod_cast hD.ne')]
      ring

/-- The finite-chain estimate with coefficient `4` invoked for positive matrix
product density operators in the proof of arXiv:1606.00608, Proposition 4.5;
see the normalization convention at lines 792--797 and the Appendix argument
at lines 1316--1321.

This follows from the stronger bound `I_L(M,N) ≤ 2 log D`. It concerns a fixed
positive chain length and does not include the proposition's thermodynamic-limit
assertion. The nonzero-trace hypothesis makes explicit the paper's convention
of normalizing by the finite-chain trace.

**Local fix (finite-chain bound):** The local-purification argument cited in
the Appendix does not apply to every positive MPO. The proof instead uses the
periodic-cut operator-Schmidt estimate; see
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_mpdo_mutual_information_bound.pdf>. -/
theorem IsMPDO.mutualInfoChain_le_four_log_bondDim
    {M : MPOTensor d D} (hM : IsMPDO M) (N L : ℕ) (hN : 0 < N)
    (hL : L ≤ N) (htr : (mpo M N).trace ≠ 0) :
    mutualInfoChain M N L hL (hM N hN) ≤ 4 * Real.log D := by
  have hD : 0 < D :=
    bondDim_pos_of_mpo_trace_ne_zero M N htr
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  exact (mutualInfoChain_le_two_log_bondDim M N L hL (hM N hN) htr).trans
    (by linarith)

end MPOTensor
