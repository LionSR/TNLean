/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Inhomogeneous.InhomogeneousPreparation
import TNLean.MPS.CanonicalForm.FixedPointApproximation.ApproximationError
import TNLean.MPS.Tensor.Chain.BlockTensor
import TNLean.MPS.Preparation.Circuit.RemainderBlocks
import TNLean.MPS.Preparation.Inhomogeneous.InhomogeneousSequence
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QICLean.Analysis.Real.PowerExponential
import TNLean.MPS.CanonicalForm.FixedPointApproximation.SecondOrderOverlap
import QICLean.Analysis.Norm.NormedRingTelescoping

/-!
# Normalized pair approximation from ordered transfer mixing

The state made from the positive parts of the actual inhomogeneous blocks is compared with
the product of the pairs of one faithful reference state. Ordered mixed-transfer telescoping
controls the unnormalized overlap, while the actual whole-ring transfer matrix controls the
normalization. The resulting normalized error is linear in the number of blocks times the
local transfer error, with constants independent of the chain and its partition.

This supplies a quantitative sufficient condition for the pair approximation in
arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS". A nonzero target is
needed when interpreting its normalization as a physical unit vector. It is not silently
inferred from a bound that only guarantees nonvanishing for sufficiently long rings.

**Scope restriction (ordered mixing):** the quantitative ordered-product bounds and common
faithful reference state are additional hypotheses, not consequences of the source's
qualitative finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

It also contains the following results.

* `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_min_of_rate`,
  `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_min_of_ordered_mixing`: explicit
  blocking scale and physical preparation depth.
* `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing`,
  `MPSPreparation.exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_ordered_mixing`:
  physical logarithmic-depth preparation from ordered mixing.
* `MPSPreparation.exists_norm_polarPos_sub_le_transferMatrix`,
  `MPSPreparation.exists_norm_trace_prod_polarPos_sub_one_le`: ordered mixing and the overlap of
  inhomogeneous positive parts.

## References

* arXiv:2307.01696, eq. (5) and paragraph "Inhomogeneous short-range correlated MPS".
* arXiv:2103.13367, Supplemental Material, proof of Theorem MPS_classification (ordered overlaps).

## Pair-approximation rate from actual ordered mixing

Ordered transfer products within `K exp(-r ℓ)` of one faithful normalized reference
produce a normalized pair error at most `Cp K N exp(-r q)` on remainder-absorbing blocks.
The constant `Cp` depends only on the bond dimension and reference state, before the
physical dimension, chain, ring length and blocking scale are chosen.

This is an additional quantitative sufficient condition for arXiv:2307.01696's
inhomogeneous preparation scheme, not a consequence of its qualitative convergence
assumption. A nonzero periodic target is required.

### References

* [arXiv:2307.01696](https://arxiv.org/abs/2307.01696),
  the inhomogeneous short-range correlated MPS discussion.
  The uniform ordered-mixing estimate is an additional quantitative hypothesis.
-/

section InhomogeneousOverlap

/-!
## Ordered mixing and the overlap of inhomogeneous positive parts

A quantitative bound on the transfer matrix of each actual blocked tensor gives a bound on
its positive polar factor. Telescoping the ordered mixed-transfer product then controls its
trace. All norm-conversion constants depend only on the common bond dimension and faithful
reference state, before the physical dimensions, tensors, and number of blocks are chosen.

These are quantitative sufficient conditions for the pair approximation used in
arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS". They are not deduced
from individual sitewise spectral gaps or from qualitative convergence of the pair error.

**Scope restriction (ordered mixing):** the quantitative ordered-product bounds and common
faithful reference state are additional hypotheses, not consequences of the source's
qualitative finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### References

* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".
* arXiv:2103.13367, Supplemental Material, eqs. (19), (21), (26), and (29)--(34).
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace MPSPreparation

/-- Transfer-matrix error bounds the positive-part error, with constants uniform
in the physical dimension and tensor. The transfer and Gram matrices carry their `L²`
operator norms; their reshuffling costs only a bond-dimension-dependent constant.

This is the ordered-transfer version of the Gram rearrangement and square-root estimate
in arXiv:2103.13367, Supplemental Material, equations (19), (21), and (26). -/
theorem exists_norm_polarPos_sub_le_transferMatrix
    {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d : ℕ} (A : MPSTensor d D),
      ‖Matrix.polarPos (physicalMatrix A) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := by
  classical
  obtain ⟨K, hK, hgram⟩ := exists_norm_gram_transferMatrix_sub_le D
  have hpd : (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).PosDef :=
    (Matrix.PosDef.transpose_iff.2 hσ).kronecker Matrix.PosDef.one
  obtain ⟨L, hL, hlip⟩ := hpd.isStrictlyPositive.exists_norm_sqrt_sub_sqrt_le
  refine ⟨L * K, by positivity, fun {d} A => ?_⟩
  have hsqrt := hlip _ (Matrix.posSemidef_conjTranspose_mul_self (physicalMatrix A)).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at hsqrt
  rw [mul_assoc]
  exact hsqrt.trans (mul_le_mul_of_nonneg_left (hgram A σ hσ.posSemidef).1 hL)

/-- The ordered mixed-transfer product of positive parts is close to trace one when each
actual tensor has transfer matrix close to the common rank-one fixed point. No equality
between the tensors, and no commutation between their transfer maps, is assumed.

The estimate is `C M δ exp(C M δ)` for transfer-matrix error at most `δ`; `C` depends only on
the faithful trace-one state and its bond dimension. This is the telescoping argument of
arXiv:2103.13367, Supplemental Material, equations (29)--(34), for ordered factors. -/
theorem exists_norm_trace_prod_polarPos_sub_one_le
    {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : ℕ} [NeZero M] (d : Fin M → ℕ)
      (A : ∀ j, MPSTensor (d j) D) {δ : ℝ}, 0 ≤ δ →
      (∀ j, ‖transferMatrix (Kraus.transferMap (A j)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ) →
      ‖Matrix.trace (List.ofFn fun j => transferMatrix
          (Kraus.mixedMapLM (polarPosTensor (A j)) (fixedPointTensor σ))).prod - 1‖ ≤
        C * (M * δ) * Real.exp (C * (M * δ)) := by
  classical
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨Kp, hKp, hp⟩ := exists_norm_polarPos_sub_le_transferMatrix hσ
  let Ψ := LinearMap.toContinuousLinearMap
    (transferMatrixLM ∘ₗ mixedMapLMLeft (fixedPointTensor σ) ∘ₗ ofPhysicalMatrixLM)
  let trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  let T := transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))
  let c := ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ + ‖T‖
  let K := c * (‖Ψ‖ * Kp)
  have hc : 0 ≤ c := by positivity
  have hK : 0 ≤ K := by positivity
  let C := ‖trL‖ * c * K + K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun {M} _ d A δ hδ hA => ?_⟩
  let X : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    if h : j < M then transferMatrix
      (Kraus.mixedMapLM (polarPosTensor (A ⟨j, h⟩)) (fixedPointTensor σ)) else T
  have hX : ∀ j, ‖X j - T‖ ≤ ‖Ψ‖ * Kp * δ := by
    intro j
    dsimp only [X]
    split_ifs with hj
    · have heq : transferMatrix
          (Kraus.mixedMapLM (polarPosTensor (A ⟨j, hj⟩)) (fixedPointTensor σ)) - T =
          Ψ (Matrix.polarPos (physicalMatrix (A ⟨j, hj⟩)) -
            (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [map_sub]
        congr 1
        change T = transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrix
          (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix
            (virtualPairEquiv D) id)) (fixedPointTensor σ))
        rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one]
      rw [heq, mul_assoc]
      exact (Ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((hp _).trans (mul_le_mul_of_nonneg_left (hA _) hKp)) (norm_nonneg _))
    · rw [sub_self, norm_zero]; positivity
  have htel := norm_prod_range_sub_pow_le_of_isIdempotentElem
    (isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr)
    (c := c) (le_add_of_nonneg_left (norm_nonneg _))
    (le_add_of_nonneg_right (norm_nonneg _)) hX M
  have htrace : Matrix.trace ((List.range M).map X).prod - 1 =
      trL (((List.range M).map X).prod - T ^ M) := by
    change _ = Matrix.trace _
    rw [Matrix.trace_sub, trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      mpvOverlap_fixedPointTensor_self hσ.posSemidef htr]
  have hgeom := one_add_pow_sub_one_le_mul_exp
    (show 0 ≤ c * (‖Ψ‖ * Kp * δ) by positivity) M
  have hprod : (List.ofFn fun j => transferMatrix
        (Kraus.mixedMapLM (polarPosTensor (A j)) (fixedPointTensor σ))) =
      (List.range M).map X := by
    refine List.ext_getElem (by simp) fun j hj _ => ?_
    have hjM : j < M := by simpa using hj
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [List.getElem_range]
    dsimp only [X]
    rw [dite_eq_left hjM]
  rw [hprod, htrace]
  calc ‖trL (((List.range M).map X).prod - T ^ M)‖
      ≤ ‖trL‖ * ‖((List.range M).map X).prod - T ^ M‖ := trL.le_opNorm _
    _ ≤ ‖trL‖ * (c * ((1 + c * (‖Ψ‖ * Kp * δ)) ^ M - 1)) := by gcongr
    _ ≤ ‖trL‖ * (c * (M * (c * (‖Ψ‖ * Kp * δ)) *
        Real.exp (M * (c * (‖Ψ‖ * Kp * δ))))) := by gcongr
    _ = ‖trL‖ * c * K * (M * δ) * Real.exp (K * (M * δ)) := by dsimp [K]; ring_nf
    _ ≤ C * (M * δ) * Real.exp (C * (M * δ)) := by
      have hKC : K ≤ C := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (norm_nonneg trL) hc) hK]
      have hKC' : ‖trL‖ * c * K ≤ C := by dsimp [C]; linarith
      gcongr

end MPSPreparation

end InhomogeneousOverlap

section InhomogeneousApproximationError

section

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator
open Kraus (blockPhysDim decodeBlockEquiv)

namespace MPSPreparation

/-- The norm squared of the actual periodic chain is the trace of the transfer matrix of its
whole blocked tensor. This identifies the normalization with an ordered transfer product. -/
theorem ofReal_norm_chainState_sq {d D N : ℕ} [NeZero D] (A : MPSChainTensor d D N) :
    ((‖chainState A‖ ^ 2 : ℝ) : ℂ) =
      Matrix.trace (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A))) := by
  classical
  rw [← pow_one (transferMatrix _), trace_transferMatrix_transferMap_pow_eq_mpvOverlap]
  rw [EuclideanSpace.norm_sq_eq, mpvOverlap]
  push_cast
  let e := (Equiv.funUnique (Fin 1) (Fin (blockPhysDim d N))).trans (decodeBlockEquiv d N)
  refine (Fintype.sum_equiv e _ _ fun t => ?_).symm
  simp only [chainState_apply, ← Complex.mul_conj']
  have ht : mpv (MPSChainTensor.blockTensor A) t = MPSChainTensor.coeff A (e t) := by
    simp [e, Equiv.funUnique, Equiv.piUnique, mpv, coeff, List.ofFn_succ,
      List.ofFn_zero, MPSChainTensor.blockTensor, MPSChainTensor.coeff]
  simp only [ht, starRingEnd_apply]

/-- The overlap of the product of fixed-point pairs with the positive-part state is the
trace of the ordered product of their mixed transfer matrices. -/
theorem inner_pairFamilyVector_chainPosState {d D N M : ℕ} [NeZero M]
    (A : MPSChainTensor d D N) {ℓ : Fin M → ℕ} (hN : ∑ j, ℓ j = N)
    (σ : Matrix (Fin D) (Fin D) ℂ) :
    ⟪pairFamilyVector (fun _ : Fin M => fixedPointPair σ), chainPosState A hN⟫_ℂ =
      Matrix.trace (List.ofFn fun j => transferMatrix
        (Kraus.mixedMapLM (polarPosTensor (chainBlockTensor A hN j))
          (fixedPointTensor σ))).prod := by
  rw [← sum_mpvFamily_mul_star_mpv, PiLp.inner_apply]
  simp only [RCLike.inner_apply, pairFamilyVector_apply, pairFamilyState_const,
    chainPosState_apply, mpv_fixedPointTensor]
  rfl

/-- The whole-ring transfer error controls the normalization uniformly. The constant depends
only on the bond dimension, not the chain length or physical dimension. -/
theorem exists_abs_norm_chainState_sq_sub_one_le {D : ℕ}
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d N : ℕ} (A : MPSChainTensor d D N),
      |‖chainState A‖ ^ 2 - 1| ≤ K *
        ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := by
  have := Matrix.neZero_of_trace_eq_one htr
  let trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  refine ⟨‖trL‖, norm_nonneg _, fun {d N} A => ?_⟩
  have htrace : Matrix.trace (transferMatrix (Kraus.transferMap (fixedPointTensor σ))) = 1 := by
    simpa only [pow_one] using
      (trace_transferMatrix_transferMap_pow_eq_mpvOverlap (fixedPointTensor σ) 1).trans
        (mpvOverlap_fixedPointTensor_self hσ htr 1)
  have heq : ((‖chainState A‖ ^ 2 - 1 : ℝ) : ℂ) =
      trL (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))) := by
    change _ = Matrix.trace _
    rw [Matrix.trace_sub, htrace, Complex.ofReal_sub, Complex.ofReal_one,
      ofReal_norm_chainState_sq]
  have h := trL.le_opNorm (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
    transferMatrix (Kraus.transferMap (fixedPointTensor σ)))
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Uniform normalized pair approximation from actual blocked transfer matrices. If every
block and the whole ring have transfer error at most `δ` relative to one faithful normalized
reference state, the pair error is at most `C M δ`. The constant is chosen before the tensor,
physical dimension, ring, partition, and error. No injectivity of the blocked tensors is
required.

This is a sufficient-condition version of arXiv:2307.01696, paragraph "Inhomogeneous
short-range correlated MPS". The bound also holds algebraically for a zero target, but a
physical normalization requires the target to be nonzero. -/
theorem exists_one_sub_norm_inner_chainPosState_le
    {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d N M : ℕ} [NeZero M]
      (A : MPSChainTensor d D N) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N) {δ : ℝ},
      0 ≤ δ →
      (∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor A hN j)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ) →
      ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ →
      1 - ‖⟪pairFamilyVector (fun _ : Fin M => fixedPointPair σ),
        (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ ≤ C * (M * δ) := by
  obtain ⟨Co, hCo, hover⟩ := exists_norm_trace_prod_polarPos_sub_one_le hσ htr
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le hσ.posSemidef htr
  let C := Co + Kn
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C * Real.exp C + 1, by positivity, fun {d N M} _ A ℓ hN δ hδ hA hwhole => ?_⟩
  let Ω := pairFamilyVector (fun _ : Fin M => fixedPointPair σ)
  let v := chainPosState A hN
  have hΩ : ‖Ω‖ = 1 := norm_pairFamilyVector fun _ => by
    rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
  have ho : ‖⟪Ω, v⟫_ℂ - 1‖ ≤ Co * (M * δ) * Real.exp (Co * (M * δ)) := by
    rw [inner_pairFamilyVector_chainPosState]
    exact hover (fun j => blockPhysDim d (ℓ j)) (chainBlockTensor A hN) hδ hA
  have hn : |‖v‖ ^ 2 - 1| ≤ Kn * δ := by
    rw [← norm_chainState_eq A hN]
    exact (hnorm A).trans (mul_le_mul_of_nonneg_left hwhole hKn)
  have ha : |1 - ‖⟪Ω, v⟫_ℂ‖| ≤ Co * (M * δ) * Real.exp (Co * (M * δ)) := by
    calc |1 - ‖⟪Ω, v⟫_ℂ‖| = |‖(1 : ℂ)‖ - ‖⟪Ω, v⟫_ℂ‖| := by rw [norm_one]
      _ ≤ ‖⟪Ω, v⟫_ℂ - 1‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
      _ ≤ _ := ho
  have herr := one_sub_norm_inner_smul_inv_norm_le hΩ.le ha hn
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hCoC : Co ≤ C := by dsimp [C]; linarith
  have hsmall : 1 - ‖⟪Ω, (‖v‖ : ℂ)⁻¹ • v⟫_ℂ‖ ≤
      C * (M * δ) * Real.exp (C * (M * δ)) := by
    have hexp : 1 ≤ Real.exp (C * (M * δ)) := Real.one_le_exp (by positivity)
    have ho' : Co * (M * δ) * Real.exp (Co * (M * δ)) ≤
        Co * (M * δ) * Real.exp (C * (M * δ)) := by gcongr
    have hn' : Kn * δ ≤ Kn * (M * δ) * Real.exp (C * (M * δ)) := by
      calc Kn * δ ≤ Kn * (M * δ) := by gcongr; exact le_mul_of_one_le_left hδ hM
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hexp
    dsimp only [C]
    nlinarith
  exact le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) hsmall
    (by linarith only [norm_nonneg ⟪Ω, (‖v‖ : ℂ)⁻¹ • v⟫_ℂ])

end MPSPreparation

end

section

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

/-- **Actual ordered mixing implies the pair rate.** Every positive nonwrapping contiguous
block has transfer error at most `K exp(-r ℓ)`. The remainder-absorbing partition has
normalized pair error at most `Cp K N exp(-r q)` for each `1 ≤ q ≤ N`.

This extracts the quantitative hypothesis used by the physical preparation results, with
`Cp` independent of the chain and ring length. Source: arXiv:2307.01696, paragraph
"Inhomogeneous short-range correlated MPS", under the additional ordered-mixing condition. -/
theorem exists_isPairApproximable_of_ordered_mixing {D : ℕ}
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (d N : ℕ) [NeZero N] (A : MPSChainTensor d D N)
      (K r : ℝ), 0 < K → 0 < r → chainState A ≠ 0 →
      (∀ {M : ℕ} (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
        ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
            Kraus.transferMap (A (blockSite hN j i))).prod) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
            K * Real.exp (-(r * ℓ j))) →
      ∀ q : ℕ, 0 < q → q ≤ N →
        ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
          (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
          IsPairApproximable (ofChain A) hN
            (Cp * K * ((N : ℝ) ^ 1 * Real.exp (-(r * q)))) := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := exists_one_sub_norm_inner_chainPosState_le hσ htr
  refine ⟨Cp, hCp, fun d N _ A K r hK hr hne hmix q hq hqN => ?_⟩
  let ℓ := remainderBlockLengths q N
  have hsum := sum_remainderBlockLengths hq hqN
  have hM := Nat.div_pos hqN hq
  let : NeZero (N / q) := ⟨hM.ne'⟩
  have hℓq : ∀ j, q ≤ ℓ j := le_remainderBlockLengths q N
  have hℓ2q : ∀ j, ℓ j ≤ 2 * q := fun j => (remainderBlockLengths_lt_two_mul hq j).le
  refine ⟨N / q, hM, ℓ, hsum, hℓq, hℓ2q, ?_⟩
  have hpos : chainPosState (zeroPad (ofChain A)) hsum ≠ 0 := by
    rw [zeroPad_ofChain]
    intro hz
    have hn := norm_chainState_eq A hsum
    rw [hz, norm_zero] at hn
    exact hne (norm_eq_zero.mp hn)
  have hpair : padPairs (ofChain A) ℓ (fun _ => fixedPointPair σ) =
      fun _ : Fin (N / q) => fixedPointPair σ := by
    funext j p
    simp [padPairs, padPair, Matrix.zeroPad, rightBond, leftBond, ofChain]
    rfl
  refine ⟨hpos, fun _ => fixedPointPair σ, (fun _ => ?_), ?_⟩
  · change ∑ p : Fin D × Fin D, star (fixedPointPair σ p) * fixedPointPair σ p = 1
    rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
  rw [hpair, zeroPad_ofChain]
  let δ := K * Real.exp (-(r * q))
  have hblock : ∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor A hsum j)) -
      transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ := by
    intro j
    rw [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    refine (hmix ℓ hsum j (hq.trans_le (hℓq j))).trans ?_
    dsimp [δ]
    gcongr
    exact hℓq j
  have hwhole : ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
      transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ := by
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi := blockSite_singleton hsingle
    have h := hmix (fun _ : Fin 1 => N) hsingle 0
      (Nat.pos_of_ne_zero (NeZero.ne N))
    simp only [hi] at h
    rw [MPSChainTensor.transferMap_blockTensor]
    refine h.trans ?_
    dsimp [δ]
    gcongr
  have herr := hp A ℓ hsum (show 0 ≤ δ by positivity) hblock hwhole
  refine herr.trans ?_
  dsimp [δ]
  simp only [pow_one]
  calc Cp * (((N / q : ℕ) : ℝ) * (K * Real.exp (-(r * q)))) =
      Cp * K * (((N / q : ℕ) : ℝ) * Real.exp (-(r * q))) := by ring
    _ ≤ Cp * K * (N * Real.exp (-(r * q))) := by gcongr; exact Nat.div_le_self N q

end MPSPreparation

end

end InhomogeneousApproximationError

section ExplicitPreparationScale

/-!
## Explicit blocking scale and physical preparation depth

For an error estimate `K N^k exp(-r q)`, choose
`q = ⌈a log(N/ε) + b⌉`, where `a ≥ max(k,1)/r` and
`b ≥ max(log K,0)/r + L + 3D + 1`. The rate is needed only at the selected usable
scale `q ≥ L`. Physical circuit depth is bounded by `C(d,D) min(N,q)`:
blocks between `q` and `2q` suffice when `q ≤ N`, and exact preparation handles `q > N`.
The normalized target must be nonzero, including in the exact branch.

This is a quantitative sufficient condition supplementing arXiv:2307.01696's
"Inhomogeneous short-range correlated MPS" paragraph. Its qualitative convergence assumption
does not imply the uniform rate used here; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### References

* [arXiv:2307.01696](https://arxiv.org/abs/2307.01696),
  the inhomogeneous short-range correlated MPS discussion.
  The quantitative rate and explicit-scale theorem here are additional sufficient conditions.

### Explicit physical scale from ordered mixing

For ordered transfer error `K exp(-r ℓ)` towards a common faithful normalized reference,
the sufficient block coefficient is `1/r`. An offset independent of the chain and ring
length gives the concrete scale `q = ⌈(1/r) log(N/ε) + b⌉` and physical depth
`T ≤ C(d,D) min(N,q)`. The pair rate is derived from the actual tensors.

This supplements arXiv:2307.01696's inhomogeneous scheme with a quantitative sufficient
condition. It does not assert optimality of the circuit-depth constant or derive mixing
from qualitative finite correlation. Nonzero targets remain an explicit hypothesis.

#### References

* [arXiv:2307.01696](https://arxiv.org/abs/2307.01696),
  the inhomogeneous short-range correlated MPS discussion.
  The explicit sufficient coefficient is a quantitative refinement.
-/

section

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- **Explicit scale, usable-scale cutoff, and physical depth.** The circuit constant depends
only on `d,D` and can be chosen as `max(2 Cb, Ce)`, where `Cb` is the block-preparation
constant and `Ce` the exact-preparation constant. The pair estimate is required only at the
selected scale when it does not exceed the ring length.

The uniform polynomial-exponential rate is an additional sufficient condition, not a
consequence asserted here of arXiv:2307.01696's qualitative inhomogeneous assumption. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_min_of_rate (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (N : ℕ) [NeZero N] (A : VaryingBondChain d D N), state A ≠ 0 →
      ∀ (K r : ℝ) (k L : ℕ) (a b ε : ℝ), 0 < K → 0 < r →
        max (k : ℝ) 1 / r ≤ a → max (Real.log K) 0 / r + L + 3 * D + 1 ≤ b →
        0 < ε → ε ≤ 1 →
        let q := ⌈a * Real.log (N / ε) + b⌉₊
        (0 < q → L ≤ q → q ≤ N →
          ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
            (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
            IsPairApproximable A hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) →
          3 * D + 1 ≤ q ∧ ∃ (ψ : MPVSpace d N) (T : ℕ),
            ‖ψ‖ = 1 ∧ T ≤ C * min N q ∧ IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
              1 - ‖⟪ψ, (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_of_isPairApproximable d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedChainState d D hd
  refine ⟨max (2 * Cb) Ce, fun N _ A hA K r k L a b ε hK hr ha hb hε hε1 => ?_⟩
  dsimp only
  intro hrate
  let q := ⌈a * Real.log (N / ε) + b⌉₊
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ha0 : 0 ≤ a := (div_nonneg (le_trans zero_le_one (le_max_right _ _)) hr.le).trans ha
  have hlog : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  have hQq : a * Real.log (N / ε) + b ≤ (q : ℝ) := Nat.le_ceil _
  have hbase : max (Real.log K) 0 / r + L + 3 * D + 1 ≤ (q : ℝ) := by
    linarith [mul_nonneg ha0 hlog]
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hLq : L ≤ q := by exact_mod_cast (show (L : ℝ) ≤ q by linarith)
  have hDq : 3 * D + 1 ≤ q := by
    exact_mod_cast (show (3 : ℝ) * D + 1 ≤ q by linarith)
  refine ⟨hDq, ?_⟩
  by_cases hqN : q ≤ N
  · obtain ⟨M, hM, ℓ, hsum, hℓq, hℓ2q, happ⟩ := hrate (by omega) hLq hqN
    let : NeZero M := ⟨hM.ne'⟩
    obtain ⟨ψ, hψ, hprep, herr⟩ := hCb ℓ hsum A (2 * q)
      (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))
      (fun j => (by omega : 3 * D ≤ q).trans (hℓq j)) hℓ2q happ
    refine ⟨ψ, Cb * (2 * q), hψ, ?_, hprep, herr.trans ?_⟩
    · rw [min_eq_right hqN, ← Nat.mul_assoc, Nat.mul_comm Cb 2]
      exact Nat.mul_le_mul_right q (le_max_left _ _)
    · exact mul_pow_mul_exp_neg_le_of_le hK hr hN1 hε hε1 ha (by linarith) hQq
  · obtain ⟨T, hT, hprep⟩ := hCe N (zeroPad A) (by rwa [← state_eq_chainState])
    have hu : ‖(‖state A‖ : ℂ)⁻¹ • state A‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]
    refine ⟨_, T, hu, ?_, ?_, ?_⟩
    · rw [min_eq_left (by omega : N ≤ q)]
      exact hT.trans (Nat.mul_le_mul_right N (le_max_right _ _))
    · simpa only [← state_eq_chainState] using hprep
    · rw [inner_self_eq_norm_sq_to_K, hu]
      simpa using hε.le

end MPSPreparation

end

section

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

/-- **Selected block coefficient `1/r` from actual ordered mixing.** The physical circuit
constant depends only on `d,D`; the offset depends only on the fixed faithful reference and
mixing constants. The actual ring is prepared exactly when the selected scale exceeds it.

The sufficient scale is a quantitative refinement associated with arXiv:2307.01696, not a
claim that the optimal physical circuit depth has the same coefficient. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_min_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosDef → σ.trace = 1 →
      ∀ (K r : ℝ), 0 < K → 0 < r → ∃ b : ℝ, 1 ≤ b ∧
        ∀ (N : ℕ) [NeZero N] (A : MPSChainTensor d D N), chainState A ≠ 0 →
          (∀ {M : ℕ} (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
            ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
                Kraus.transferMap (A (blockSite hN j i))).prod) -
              transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
                K * Real.exp (-(r * ℓ j))) →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            let q := ⌈(1 / r) * Real.log (N / ε) + b⌉₊
            3 * D + 1 ≤ q ∧ ∃ (ψ : MPVSpace d N) (T : ℕ),
              ‖ψ‖ = 1 ∧ T ≤ C * min N q ∧
                IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
                1 - ‖⟪ψ, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_min_of_rate d D hd
  refine ⟨C, fun σ hσ htr K r hK hr => ?_⟩
  obtain ⟨Cp, hCp, hp⟩ := exists_isPairApproximable_of_ordered_mixing hσ htr
  let b : ℝ := max (Real.log (Cp * K)) 0 / r + 3 * D + 1
  have hb : 1 ≤ b := by
    have : 0 ≤ max (Real.log (Cp * K)) 0 / r + 3 * D := by positivity
    dsimp [b]
    linarith
  refine ⟨b, hb, fun N _ A hA hmix ε hε hε1 => ?_⟩
  have hstate : state (ofChain A) = chainState A := by
    rw [state_eq_chainState, zeroPad_ofChain]
  have h := hC N (ofChain A) (by rwa [hstate]) (Cp * K) r 1 0 (1 / r) b ε
    (mul_pos hCp hK) hr (by simp) (by simp [b]) hε hε1
  dsimp only at h ⊢
  rw [hstate] at h
  apply h
  intro hq _ hqN
  exact hp d N A K r hK hr hA hmix _ hq hqN

end MPSPreparation

end

end ExplicitPreparationScale

section InhomogeneousMixingPreparation

/-!
## Physical logarithmic-depth preparation from ordered mixing

Uniform exponential mixing of the actual ordered transfer products towards one faithful
trace-one state implies a uniform normalized pair-approximation rate, and hence physical
preparation in depth `O(log(N/ε))`. The constants are independent of the ring and partition.
The assumption concerns nonwrapping contiguous intervals in the chosen linear ordering,
not separate eigenvalue bounds on sites.

The all-positive-length theorem requires nonzero targets because the source compares
normalized quantum states. This retains finite short rings for which decay alone may not
exclude a zero periodic vector. The eventual theorem instead derives nonvanishing beyond
a uniform cutoff, without changing the family. Existing exact short-ring preparation
handles scales longer than the ring.

This is a quantitative sufficient condition for arXiv:2307.01696, paragraph "Inhomogeneous
short-range correlated MPS". The paper's qualitative finite-correlation definition alone
does not supply the ordered mixing hypothesis.

**Scope restriction (ordered mixing):** the quantitative ordered-product bounds and common
faithful reference state are additional hypotheses, not consequences of the source's
qualitative finite-correlation definition. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS" and the logarithmic
  blocking choice following Lemma 1 in the translation-invariant case.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

private theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing_from
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r) (N₀ : ℕ)
    (hne : ∀ (N : ℕ) [NeZero N], N₀ ≤ N → chainState (A N) ≠ 0)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := exists_isPairApproximable_of_ordered_mixing hσ htr
  let B (N : ℕ) := ofChain (A N)
  have hstate (N : ℕ) [NeZero N] : state (B N) = chainState (A N) := by
    rw [state_eq_chainState, zeroPad_ofChain]
  have hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N → N₀ ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (B N) hN (Cp * K * ((N : ℝ) ^ 1 * Real.exp (-(r * q)))) := by
    intro N _ q hq hqN hN₀
    exact hp d N (A N) K r hK hr (hne N hN₀) (hmix N) q hq hqN
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from
    d D hd B (Cp * K) r 1 (mul_pos hCp hK) hr N₀ hrate
  refine ⟨C, fun ε hε hε1 N _ hN₀ => ?_⟩
  simpa only [hstate] using hC ε hε hε1 N hN₀

/-- Actual ordered transfer mixing gives normalized physical preparation in logarithmic
accuracy-dependent depth. Fix `K,r > 0` and one faithful normalized reference state before
the ring length is chosen. Every positive nonwrapping contiguous block has transfer-matrix error at
most `K exp(-r ℓ)`, in the `L²` operator norm. Then the normalized nonzero chain states can
be approximated to error `ε` in depth `C log(N/ε)`.

The finite-dimensional norm conversions and overlap estimates have constants depending only
on the fixed bond dimension and reference state. The pair-approximation rate is proved from
the tensors, rather than supplied as a hypothesis. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hne : ∀ (N : ℕ) [NeZero N], chainState (A N) ≠ 0)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing_from
    d D hd A hσ htr K r hK hr 0 (fun N _ _ => hne N) hmix
  exact ⟨C, fun ε hε hε1 N _ => hC ε hε hε1 N (Nat.zero_le N)⟩

/-- Uniform ordered mixing alone gives physical logarithmic-depth preparation of the
original family at every sufficiently large ring length. The cutoff is chosen before
`N` and `ε`: the whole-ring norm estimate makes the squared norm at least `1/2` beyond
that cutoff. No nonzero condition is imposed on finitely many short rings, and no tensor
in the physical family is replaced.

This quantitative sufficient condition includes normal families with vanishing short
periodic vectors; it does not derive ordered mixing from qualitative finite correlation.
See `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ N₀ : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le hσ.posSemidef htr
  let L := Kn * K + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((Real.log L - Real.log (1 / 2 : ℝ)) / r)
  have hne (N : ℕ) [NeZero N] (hcut : N₀ ≤ N) : chainState (A N) ≠ 0 := by
    have hsmall : L * Real.exp (-(r * N)) ≤ 1 / 2 :=
      mul_exp_neg_mul_le_of_div_log_le hL hr (by norm_num)
        (hN₀.trans (Nat.cast_le.mpr hcut))
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi := blockSite_singleton hsingle
    have ht := hmix N (fun _ : Fin 1 => N) hsingle 0
      (Nat.pos_of_ne_zero (NeZero.ne N))
    simp only [hi] at ht
    rw [← MPSChainTensor.transferMap_blockTensor] at ht
    have hb : |‖chainState (A N)‖ ^ 2 - 1| ≤ 1 / 2 := by
      calc |‖chainState (A N)‖ ^ 2 - 1|
          ≤ Kn * ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A N))) -
            transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := hnorm _
        _ ≤ Kn * (K * Real.exp (-(r * N))) := mul_le_mul_of_nonneg_left ht hKn
        _ ≤ L * Real.exp (-(r * N)) := by
            dsimp only [L]
            nlinarith [Real.exp_pos (-(r * N))]
        _ ≤ 1 / 2 := hsmall
    intro hz
    norm_num [hz] at hb
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing_from
    d D hd A hσ htr K r hK hr N₀ hne hmix
  exact ⟨N₀, C, hC⟩

end MPSPreparation

end InhomogeneousMixingPreparation
