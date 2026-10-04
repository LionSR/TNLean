/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SecondOrderOverlap

/-!
# Positivity of the polar compression coefficient

For a tensor `B` with positive polar factor `P` and a positive semidefinite matrix `σ`,
let `P_∞` be the fixed-point tensor. The compression coefficient
`α = Tr(E_{P,P_∞}(σ))` is the trace of the product of `P` with
`(√σ)ᵀ ⊗ σ`, and is therefore real and nonnegative. If `Tr σ = Tr(E_B(σ)) = 1`, the
weighted tensors `(Pⁱ√σ)ᵢ` and `(P_∞ⁱ√σ)ᵢ` are unit vectors. Consequently `α ≤ 1` and
`1 - α = ‖(Pⁱ√σ)ᵢ - (P_∞ⁱ√σ)ᵢ‖² / 2`.

These identities refine the mixed-transfer comparison of arXiv:2103.13367, Supplemental
Material, after eq. `eq:a_tensor`, and apply to the positive factors in arXiv:2307.01696,
eqs. `eq:B_TM` and `eq:app_error`. They require neither injectivity nor normality. The
quadratic identity is a project result, rather than the first-order estimate printed in
the latter source.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators InnerProductSpace

namespace MPSTensor

variable {n D : ℕ}

/-- The compression coefficient of a tensor `X` read from a `D² × D²` matrix `H`, against the
fixed-point tensor of `σ`, is a trace: `Tr(∑ᵢ Xⁱ σ (P_∞ⁱ)†) = Tr(H ((√σ)ᵀ ⊗ σ))`. -/
theorem trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor
    (H : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (σ : Matrix (Fin D) (Fin D) ℂ) :
    (Kraus.mixedMapLM (ofPhysicalMatrixLM H) (fixedPointTensor σ) σ).trace =
      (H * ((CFC.sqrt σ)ᵀ ⊗ₖ σ)).trace := by
  rw [Kraus.mixedMapLM_apply, Matrix.trace_sum]
  rw [← (virtualPairEquiv D).symm.sum_comp]
  have hS : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := Matrix.conjTranspose_cfc_sqrt σ
  simp only [ofPhysicalMatrixLM, LinearMap.coe_mk, AddHom.coe_mk, fixedPointTensor,
    virtualPairEquiv, Equiv.symm_symm, Equiv.symm_apply_apply, Matrix.conjTranspose_mul, hS,
    Matrix.conjTranspose_single, star_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ofPhysicalMatrix, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, id, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.single_apply, Fintype.sum_prod_type, ite_and, ite_mul, one_mul, zero_mul,
    Finset.sum_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const_zero, mul_ite, mul_zero]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- For a Hermitian `H` and a Hermitian `σ`, the compression coefficient of
`trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor` is real: `Tr(H W)` with `W = (√σ)ᵀ ⊗ σ`
Hermitian. -/
theorem im_trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor
    {H : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hH : H.IsHermitian)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.IsHermitian) :
    (Kraus.mixedMapLM (ofPhysicalMatrixLM H) (fixedPointTensor σ) σ).trace.im = 0 := by
  rw [trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor]
  have hW : ((CFC.sqrt σ)ᵀ ⊗ₖ σ)ᴴ = (CFC.sqrt σ)ᵀ ⊗ₖ σ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_cfc_sqrt, hσ.eq]
  have h : star (H * ((CFC.sqrt σ)ᵀ ⊗ₖ σ)).trace = (H * ((CFC.sqrt σ)ᵀ ⊗ₖ σ)).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hW, hH.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

/-- The compression coefficient of a positive polar factor against the fixed-point tensor
is nonnegative: it is `Tr(P ((√σ)ᵀ ⊗ σ))`, a trace product of positive matrices.

Project refinement of the polar-factor overlap comparison in arXiv:2307.01696,
eqs. `eq:B_TM` and `eq:app_error`. -/
theorem mixedMapLM_polarPosTensor_fixedPointTensor_trace_nonneg (B : MPSTensor n D)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ (Kraus.mixedMapLM (polarPosTensor B) (fixedPointTensor σ) σ).trace := by
  change 0 ≤ (Kraus.mixedMapLM (ofPhysicalMatrixLM (Matrix.polarPos (physicalMatrix B)))
    (fixedPointTensor σ) σ).trace
  rw [trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor]
  exact (Matrix.posSemidef_polarPos _).trace_mul_nonneg
    ((Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg σ)).transpose.kronecker hσ)

/-- If the weighted positive and fixed-point tensors are normalized, their real compression
coefficient is at most one, and its deficit is exactly half their squared distance.

Project second-order identity for the polar factors in arXiv:2307.01696,
eqs. `eq:B_TM` and `eq:app_error`. -/
theorem mixedMapLM_polarPosTensor_fixedPointTensor_trace_geometry (B : MPSTensor n D)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hB : (Kraus.transferMap B σ).trace = 1) :
    (Kraus.mixedMapLM (polarPosTensor B) (fixedPointTensor σ) σ).trace.re ≤ 1 ∧
      1 - (Kraus.mixedMapLM (polarPosTensor B) (fixedPointTensor σ) σ).trace.re =
        ‖sqrtWeightLM σ (polarPosTensor B) - sqrtWeightLM σ (fixedPointTensor σ)‖ ^ 2 / 2 := by
  have hi := norm_sqrtWeightLM_fixedPointTensor hσ htr
  have hq : ‖sqrtWeightLM σ (polarPosTensor B)‖ = 1 :=
    norm_sqrtWeightLM_eq_one hσ (by rw [transferMap_polarPosTensor]; exact hB)
  have hdist := one_sub_re_inner_eq_norm_sub_sq_div_two (𝕜 := ℂ) hi hq
  rw [inner_sqrtWeightLM hσ, norm_sub_rev] at hdist
  have hre : RCLike.re (Kraus.mixedMapLM (polarPosTensor B)
      (fixedPointTensor σ) σ).trace =
      (Kraus.mixedMapLM (polarPosTensor B) (fixedPointTensor σ) σ).trace.re := rfl
  rw [hre] at hdist
  constructor
  · nlinarith [sq_nonneg ‖sqrtWeightLM σ (polarPosTensor B) -
      sqrtWeightLM σ (fixedPointTensor σ)‖]
  · exact hdist

end MPSTensor
