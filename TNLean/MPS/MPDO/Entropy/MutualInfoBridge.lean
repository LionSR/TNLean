/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.Entropy.StrongSubadditivity.MutualInformationMonotone
import TNLean.MPS.Operator.DensityOperator.MutualInfoMonotone
import QICLean.Entropy.MutualInformation.OperatorSchmidt

/-!
# Contiguous-chain mutual information as bipartite mutual information

This file identifies the block-entropy expression for the mutual information of
a periodic matrix product density operator with the ordinary bipartite mutual
information of the normalized density operator, reindexed across the contiguous
cut after the first `L` sites.

It also contains the following results.

* `MPOTensor.mutualInfoChain_le_two_log_bondDim`,
  `MPOTensor.IsMPDO.mutualInfoChain_le_four_log_bondDim`: finite-chain mutual-information bound for
  matrix product operators.

## References

* arXiv:1606.00608, lines 792--797 and Appendix C, lines 1338--1340.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPOTensor

section MutualInfoBridge

variable {d D : ℕ}

/-- Split a length-`N` configuration into consecutive blocks of lengths `L`
and `K`, and flatten each block to a finite index. -/
noncomputable def chainBipartitionEquiv (d N L K : ℕ) (h : N = L + K) :
    (Fin N → Fin d) ≃ Fin (d ^ L) × Fin (d ^ K) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl (Fin d))).trans
    (biSplitEquiv d L K)

/-- The normalized `N`-site MPO, viewed as a bipartite matrix across the
contiguous cut after `L` sites.

Source: arXiv:1606.00608, lines 792--797. -/
noncomputable def bipartitionedNormalizedMPO (M : MPOTensor d D)
    (N L K : ℕ) (h : N = L + K) :
    Matrix (Fin (d ^ L) × Fin (d ^ K)) (Fin (d ^ L) × Fin (d ^ K)) ℂ :=
  (normalizedMPO M N).submatrix (chainBipartitionEquiv d N L K h).symm
    (chainBipartitionEquiv d N L K h).symm

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
    biSplitEquiv, MPOTensor.blockSplitEquiv_symm_apply, Matrix.sum_apply,
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

/-- Positivity of the normalized state is preserved by the bipartition
reindexing. -/
theorem bipartitionedNormalizedMPO_posSemidef (M : MPOTensor d D)
    (N L K : ℕ) (h : N = L + K) (hM : (mpo M N).PosSemidef) :
    (bipartitionedNormalizedMPO M N L K h).PosSemidef := by
  exact (normalizedMPO_posSemidef M N hM).submatrix _

/-- A normalized periodic MPO has unit trace whenever its unnormalized trace
is nonzero. -/
theorem bipartitionedNormalizedMPO_trace (M : MPOTensor d D)
    (N L K : ℕ) (h : N = L + K) (htr : (mpo M N).trace ≠ 0) :
    (bipartitionedNormalizedMPO M N L K h).trace = 1 := by
  rw [bipartitionedNormalizedMPO, Matrix.trace_submatrix_equiv,
    normalizedMPO_trace M N htr]

private theorem append_sub_self {K : ℕ} {n : Type*} (u : Fin K → n)
    (g : Fin (K - K) → n) (h : K = K + (K - K)) :
    Fin.append u g ∘ Fin.cast h = u := by
  rw [Fin.append_right_nil u g (Nat.sub_self K)]
  funext i
  simp

/-- Keeping all `N` sites of the normalized MPO leaves the state unchanged. -/
theorem reducedBlockState_full (M : MPOTensor d D) (N : ℕ) :
    reducedBlockState M N N (le_refl N) = normalizedMPO M N := by
  ext i j
  simp only [reducedBlockState, MPOTensor.blockReducedState, Matrix.partialTraceRight_apply,
    Matrix.submatrix_apply, MPOTensor.blockSplitEquiv_symm_apply, blockReindexEquiv,
    Equiv.arrowCongr_symm, Equiv.refl_symm, finCongr_symm]
  let : Unique (Fin (N - N) → Fin d) :=
    { default := fun i ↦ (Fin.cast (Nat.sub_self N) i).elim0
      uniq := fun _ ↦ funext fun i ↦ (Fin.cast (Nat.sub_self N) i).elim0 }
  rw [Fintype.sum_unique]
  have hi :
      ((finCongr (Nat.add_sub_cancel' (le_refl N))).arrowCongr (Equiv.refl (Fin d)))
          (Fin.append i default) =
        Fin.append i default ∘ Fin.cast (Nat.add_sub_cancel' (le_refl N)).symm := rfl
  have hj :
      ((finCongr (Nat.add_sub_cancel' (le_refl N))).arrowCongr (Equiv.refl (Fin d)))
          (Fin.append j default) =
        Fin.append j default ∘ Fin.cast (Nat.add_sub_cancel' (le_refl N)).symm := rfl
  rw [hi, hj, append_sub_self, append_sub_self]

/-- The first marginal at the contiguous cut is the first-`L` reduced state,
up to the standard flattening of configurations.

Source: arXiv:1606.00608, lines 792--797 and Appendix C, lines 1338--1340. -/
theorem bipartitionedNormalizedMPO_traceRight (M : MPOTensor d D) (N L : ℕ)
    (hL : L ≤ N) :
    Matrix.traceRight
        (bipartitionedNormalizedMPO M N L (N - L) (by omega)) =
      (reducedBlockState M N L hL).submatrix finFunctionFinEquiv.symm
        finFunctionFinEquiv.symm := by
  ext i j
  simp only [Matrix.traceRight_apply, bipartitionedNormalizedMPO, Matrix.submatrix_apply,
    chainBipartitionEquiv, biSplitEquiv, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, MPOTensor.blockSplitEquiv_symm_apply,
    Equiv.arrowCongr_symm, Equiv.refl_symm, finCongr_symm]
  rw [MPOTensor.reducedBlockState_eq_sum]
  let f : (Fin (N - L) → Fin d) → ℂ := fun w ↦
    M.normalizedMPO N
      ((Fin.append (finFunctionFinEquiv.symm i) w) ∘
        Fin.cast (show N = L + (N - L) by omega))
      ((Fin.append (finFunctionFinEquiv.symm j) w) ∘
        Fin.cast (show N = L + (N - L) by omega))
  change (∑ x : Fin (d ^ (N - L)), f (finFunctionFinEquiv.symm x)) = ∑ w, f w
  exact Fintype.sum_equiv finFunctionFinEquiv.symm _ f (fun _ ↦ rfl)

/-- The second marginal at the contiguous cut is the reduced state on `N-L`
sites, up to the standard flattening of configurations. Translation invariance
moves the final `N-L` sites to the beginning of the periodic chain.

Source: arXiv:1606.00608, lines 792--797 and Appendix C, lines 1338--1340. -/
theorem bipartitionedNormalizedMPO_traceLeft (M : MPOTensor d D) (N L : ℕ)
    (hL : L ≤ N) :
    Matrix.traceLeft
        (bipartitionedNormalizedMPO M N L (N - L) (by omega)) =
      (reducedBlockState M N (N - L) (Nat.sub_le N L)).submatrix
        finFunctionFinEquiv.symm finFunctionFinEquiv.symm := by
  ext i j
  simp only [Matrix.traceLeft_apply, bipartitionedNormalizedMPO, Matrix.submatrix_apply,
    chainBipartitionEquiv, biSplitEquiv, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, MPOTensor.blockSplitEquiv_symm_apply,
    Equiv.arrowCongr_symm, Equiv.refl_symm, finCongr_symm]
  let f : (Fin L → Fin d) → ℂ := fun x ↦
    M.normalizedMPO N
      ((Fin.append x (finFunctionFinEquiv.symm i)) ∘
        Fin.cast (show N = L + (N - L) by omega))
      ((Fin.append x (finFunctionFinEquiv.symm j)) ∘
        Fin.cast (show N = L + (N - L) by omega))
  change (∑ x : Fin (d ^ L), f (finFunctionFinEquiv.symm x)) = _
  rw [Fintype.sum_equiv finFunctionFinEquiv.symm _ f (fun _ ↦ rfl)]
  have key :=
    window_block_entropy M (p := L) (m := N - L) (s := 0)
      (show N = L + (N - L) + 0 by omega)
      (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)
  rw [← key]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Fintype.sum_unique]
  dsimp only [f]
  congr 1 <;> funext k
  all_goals rw [Fin.append_right_nil _ _ rfl]
  all_goals simp only [Function.comp_apply, Fin.cast_eq_self]

/-- The block-entropy expression `I_L` is the ordinary bipartite mutual
information of the normalized MPO across the contiguous `L | (N-L)` cut.

This is the identification used in arXiv:1606.00608, lines 792--797 and in the
data-processing argument of Appendix C, lines 1338--1340. No trace-one
assumption is needed for this entropy identity. -/
theorem mutualInfoChain_eq_mutualInformation (M : MPOTensor d D) (N L : ℕ)
    (hL : L ≤ N) (hM : (mpo M N).PosSemidef) :
    mutualInfoChain M N L hL hM =
      Entropy.mutualInformation
        (bipartitionedNormalizedMPO M N L (N - L) (by omega))
        ((normalizedMPO_isHermitian M N hM).submatrix
          (chainBipartitionEquiv d N L (N - L) (by omega)).symm) := by
  simp only [mutualInfoChain, blockEntropy, Entropy.mutualInformation,
    _root_.mutualInformation]
  have hright :
      vonNeumannEntropy
          (Matrix.traceRight
            (bipartitionedNormalizedMPO M N L (N - L) (by omega)))
          (Matrix.traceRight_isHermitian
            ((normalizedMPO_isHermitian M N hM).submatrix
              (chainBipartitionEquiv d N L (N - L) (by omega)).symm)) =
        vonNeumannEntropy (reducedBlockState M N L hL)
          (reducedBlockState_isHermitian M N L hL hM) := by
    rw [vonNeumannEntropy_congr (bipartitionedNormalizedMPO_traceRight M N L hL) _
      ((reducedBlockState_isHermitian M N L hL hM).submatrix _),
      vonNeumannEntropy_submatrix_equiv]
  have hleft :
      vonNeumannEntropy
          (Matrix.traceLeft
            (bipartitionedNormalizedMPO M N L (N - L) (by omega)))
          (Matrix.traceLeft_isHermitian
            ((normalizedMPO_isHermitian M N hM).submatrix
              (chainBipartitionEquiv d N L (N - L) (by omega)).symm)) =
        vonNeumannEntropy (reducedBlockState M N (N - L) (Nat.sub_le N L))
          (reducedBlockState_isHermitian M N (N - L) (Nat.sub_le N L) hM) := by
    rw [vonNeumannEntropy_congr (bipartitionedNormalizedMPO_traceLeft M N L hL) _
      ((reducedBlockState_isHermitian M N (N - L) (Nat.sub_le N L) hM).submatrix _),
      vonNeumannEntropy_submatrix_equiv]
  have hfull :
      vonNeumannEntropy (reducedBlockState M N N (le_refl N))
          (reducedBlockState_isHermitian M N N (le_refl N) hM) =
        vonNeumannEntropy (normalizedMPO M N) (normalizedMPO_isHermitian M N hM) := by
    exact vonNeumannEntropy_congr (reducedBlockState_full M N) _ _
  have hjoint :
      vonNeumannEntropy
          (bipartitionedNormalizedMPO M N L (N - L) (by omega))
          ((normalizedMPO_isHermitian M N hM).submatrix
            (chainBipartitionEquiv d N L (N - L) (by omega)).symm) =
        vonNeumannEntropy (normalizedMPO M N) (normalizedMPO_isHermitian M N hM) := by
    exact vonNeumannEntropy_submatrix_equiv
      (chainBipartitionEquiv d N L (N - L) (by omega)).symm
      (normalizedMPO M N) (normalizedMPO_isHermitian M N hM)
  rw [hright, hleft, hfull, hjoint]

end MutualInfoBridge

section MutualInfoAreaLaw

/-!
## Finite-chain mutual-information bound for matrix product operators

This file bounds the mutual information across every contiguous cut of a fixed
positive matrix product operator by twice the natural logarithm of its operator
bond dimension. The proof combines the bipartite interpretation of the chain
mutual information with the ordinary operator-Schmidt-rank bound across the two
virtual bonds.

The result concerns each fixed finite chain. It makes no assertion about a
thermodynamic limit of the mutual information.

### Main declarations

* `MPOTensor.mutualInfoChain_le_two_log_bondDim`: the sharp finite-chain bound
  in the operator bond dimension.
* `MPOTensor.IsMPDO.mutualInfoChain_le_four_log_bondDim`: the source-facing
  coefficient appearing in arXiv:1606.00608, Proposition 4.5.
-/

variable {d D : ℕ}

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

end MutualInfoAreaLaw

end MPOTensor
