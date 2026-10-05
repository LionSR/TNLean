/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousOverlap
import TNLean.MPS.Preparation.InhomogeneousPreparation
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Chain.Transfer

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

## References

* arXiv:2307.01696, eq. (5) and paragraph "Inhomogeneous short-range correlated MPS".
* arXiv:2103.13367, Supplemental Material, proof of Theorem MPS_classification (ordered overlaps).
-/

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

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
