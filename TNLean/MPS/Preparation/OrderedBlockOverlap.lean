/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrderedIdempotentTracePerturbation
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.PolarCompression

/-!
# Second-order mixed-transfer overlap for unequal block lengths

The ordered product of the mixed transfer matrices of positive polar factors has quadratic
trace error when there are at least two factors. Each factor is compressed by the same
fixed-point idempotent; positivity makes its compression coefficient real and nonnegative,
and unit-vector geometry bounds the coefficient's deficit to second order.

This is a project refinement of arXiv:2307.01696, Supplemental Material, proof of Lemma 1 and
extension to non-normal tensors, Lemma 1'(i), eq. `fid_err_gen_normal`. A single factor requires
the normalized squared-distance estimate, rather than an absolute trace estimate.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- The trace error for an ordered product of `M ≥ 2` mixed polar transfer matrices is of
second order. For block lengths `ℓ k ≥ q`, it is bounded by `C y exp(C y)` when `C y < 1`,
where `y = M exp(-2γq/ξ)` and `0 < γ < 1`.

This project refinement of arXiv:2307.01696, Supplemental Material, Lemma 1'(i),
`eq:fid_err_gen_normal`, uses the proved positivity and quadratic deficit of each compression
coefficient. No commutation between the mixed transfer matrices is required. -/
theorem exists_norm_trace_prod_transferMatrix_sub_one_le_sq (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hlam₁ : ‖lam₂‖ ≤ 1) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (ℓ : Fin M → ℕ) (q : ℕ), 2 ≤ M → (∀ k, q ≤ ℓ k) →
      C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) < 1 →
      ‖Matrix.trace (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM
          (polarPosTensor (blockTensor A (ℓ k))) (fixedPointTensor σ))).prod - 1‖ ≤
        C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) *
          Real.exp (C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q)) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨Kt, hKt, hT⟩ := exists_norm_map_polarPosTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
    (transferMatrixLM ∘ₗ mixedMapLMLeft (fixedPointTensor σ))
  obtain ⟨Kι, hKι, hι⟩ := exists_norm_map_polarPosTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
    (sqrtWeightLM (n := D * D) σ)
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hlam₁
  set τ := transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))
  have hτ : IsIdempotentElem τ :=
    isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr
  have hτtr : τ.trace = 1 := by
    have h := trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap
      (fixedPointTensor σ) (fixedPointTensor σ) 1
    rwa [pow_one, mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  obtain ⟨C₀, hC₀, hG⟩ := IsIdempotentElem.exists_norm_trace_prod_sub_one_le_sq hτ
    (tr := Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
    (fun a b => Matrix.trace_mul_comm a b) hτtr (norm_nonneg trL) trL.le_opNorm
  set K := Kt + Kι
  have hK : 0 ≤ K := add_nonneg hKt hKι
  refine ⟨C₀ * K ^ 2 + 1, by positivity, fun M ℓ q hM2 hq hsmall => ?_⟩
  set δ := K * x ^ q
  set y := (M : ℝ) * (x ^ 2) ^ q
  have hy0 : 0 ≤ y := by positivity
  set L : ℕ → ℕ := fun j => if h : j < M then ℓ ⟨j, h⟩ else q
  have hqL : ∀ j, q ≤ L j := fun j => by
    dsimp only [L]
    split_ifs with h
    · exact hq _
    · rfl
  set T : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    transferMatrix (Kraus.mixedMapLM (polarPosTensor (blockTensor A (L j))) (fixedPointTensor σ))
  set α : ℕ → ℂ := fun j =>
    (Kraus.mixedMapLM (polarPosTensor (blockTensor A (L j))) (fixedPointTensor σ) σ).trace
  have hcomp : ∀ j, τ * T j * τ = α j • τ := fun j =>
    transferMatrix_fixedPointTensor_mul_mul hσ.posSemidef _ _
  have hTd : ∀ j, ‖T j - τ‖ ≤ δ := fun j => by
    calc ‖T j - τ‖ ≤ Kt * x ^ (L j) := hT _
      _ ≤ Kt * x ^ q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (hqL j)) hKt
      _ ≤ δ := by dsimp only [δ, K]; nlinarith [pow_nonneg hx0 q]
  have hιd : ∀ j, ‖sqrtWeightLM σ (polarPosTensor (blockTensor A (L j))) -
      sqrtWeightLM σ (fixedPointTensor σ)‖ ≤ δ := fun j => by
    calc ‖sqrtWeightLM σ (polarPosTensor (blockTensor A (L j))) -
          sqrtWeightLM σ (fixedPointTensor σ)‖ ≤ Kι * x ^ (L j) := hι _
      _ ≤ Kι * x ^ q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (hqL j)) hKι
      _ ≤ δ := by dsimp only [δ, K]; nlinarith [pow_nonneg hx0 q]
  have hαpos : ∀ j, 0 ≤ α j := fun j =>
    mixedMapLM_polarPosTensor_fixedPointTensor_trace_nonneg _ hσ.posSemidef
  have hgeom : ∀ j, (α j).re ≤ 1 ∧ 1 - (α j).re =
      ‖sqrtWeightLM σ (polarPosTensor (blockTensor A (L j))) -
        sqrtWeightLM σ (fixedPointTensor σ)‖ ^ 2 / 2 := fun j =>
    mixedMapLM_polarPosTensor_fixedPointTensor_trace_geometry _ hσ.posSemidef htr (by
      rw [transferMap_blockTensor, Module.End.pow_apply, Function.iterate_fixed hfix]
      exact htr)
  have hαre : ∀ j, α j = ((α j).re : ℂ) := fun j =>
    Complex.ext rfl (by simp [(Complex.nonneg_iff.1 (hαpos j)).2])
  have hα1 : ∀ j, ‖α j‖ ≤ 1 := fun j => by
    rw [hαre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.nonneg_iff.1 (hαpos j)).1]
    exact (hgeom j).1
  have hαsq : ∀ j, ‖1 - α j‖ ≤ δ ^ 2 := fun j => by
    rw [hαre, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hgeom j).1), (hgeom j).2]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hιd j) 2
    nlinarith only [h2, sq_nonneg δ]
  have hy : (M : ℝ) * δ ^ 2 = K ^ 2 * y := by
    simp only [δ, y]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]
    ring
  have hsmall' : C₀ * (M * δ ^ 2) < 1 := by
    rw [hy]
    calc C₀ * (K ^ 2 * y) = C₀ * K ^ 2 * y := by ring
      _ ≤ (C₀ * K ^ 2 + 1) * y := mul_le_mul_of_nonneg_right (by linarith) hy0
      _ < 1 := hsmall
  have h := hG T α δ M hM2 hcomp hTd hα1 hαsq hsmall'
  have hprod : (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM
      (polarPosTensor (blockTensor A (ℓ k))) (fixedPointTensor σ))) = (List.range M).map T := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < M := by simpa using h1
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [List.getElem_range]
    dsimp only [T, L]
    rw [dite_eq_left hi]
  rw [← hprod, hy] at h
  refine h.trans ?_
  have hC : C₀ * K ^ 2 ≤ C₀ * K ^ 2 + 1 := by linarith
  calc C₀ * (K ^ 2 * y) * Real.exp (C₀ * (K ^ 2 * y))
      = C₀ * K ^ 2 * y * Real.exp (C₀ * K ^ 2 * y) := by ring_nf
    _ ≤ (C₀ * K ^ 2 + 1) * y * Real.exp ((C₀ * K ^ 2 + 1) * y) := by gcongr

end MPSTensor
