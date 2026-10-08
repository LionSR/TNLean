/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SecondOrderOverlap
import TNLean.Algebra.NormedRingTelescoping

/-!
# Ordered mixing and the overlap of inhomogeneous positive parts

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

## References

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
