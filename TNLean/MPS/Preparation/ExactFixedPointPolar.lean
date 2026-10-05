/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PositivePartRate

/-!
# Exact positive polar factors at the transfer fixed point

If a tensor has transfer map `X ↦ Tr(X) σ`, its physical Gram matrix is
`σᵀ ⊗ 1`. For positive semidefinite `σ`, the positive polar factor is therefore
exactly the fixed-point tensor. If `σ` is positive definite, the tensor is
injective.

These are exact versions of the rearrangement and polar-factor comparison in
arXiv:2307.01696, equation `eq:B_TM`.
They apply to each sufficiently long block after a nilpotent transfer transient
has vanished, without a correlation-length prescription or a separate
injectivity assumption.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder MatrixOrder

namespace MPSTensor

variable {n D : ℕ}

private theorem physicalGram_eq_fixedPoint (B : MPSTensor n D)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hB : ∀ X : Matrix (Fin D) (Fin D) ℂ, Kraus.transferMap B X = X.trace • σ) :
    (physicalMatrix B)ᴴ * physicalMatrix B =
      σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
  exact Matrix.ext fun a b => by
    rw [conjTranspose_physicalMatrix_mul_apply, hB, transpose_kronecker_one_apply]

/-- The positive polar tensor is exactly the fixed-point tensor when the transfer
map is `X ↦ Tr(X) σ` and `σ` is positive semidefinite. This is the exact endpoint
of the polar-factor comparison in arXiv:2307.01696, equation `eq:B_TM`. -/
theorem polarPosTensor_eq_fixedPointTensor_of_transferMap_eq_trace_smul
    (B : MPSTensor n D) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (hB : ∀ X : Matrix (Fin D) (Fin D) ℂ, Kraus.transferMap B X = X.trace • σ) :
    polarPosTensor B = fixedPointTensor σ := by
  have hP : Matrix.polarPos (physicalMatrix B) =
      (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [Matrix.polarPos, physicalGram_eq_fixedPoint B σ hB, sqrt_transpose_kronecker_one hσ]
  exact funext fun i => funext fun a => funext fun b => by
    simpa only [polarPosTensor, ofPhysicalMatrix, Matrix.submatrix_apply,
      hP, virtualPairEquiv, Matrix.of_apply, Equiv.apply_symm_apply, id_eq] using
      (congrFun (congrFun (fixedPointTensor_reshape_eq σ)
        (finProdFinEquiv.symm i)) (a, b)).symm

/-- A tensor with transfer map `X ↦ Tr(X) σ` is injective when `σ` is positive
definite: its physical Gram matrix `σᵀ ⊗ 1` is invertible. This is the exact
fixed-point case of arXiv:2307.01696, equation `eq:B_TM`. -/
theorem isInjective_of_transferMap_eq_trace_smul
    (B : MPSTensor n D) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (hB : ∀ X : Matrix (Fin D) (Fin D) ℂ, Kraus.transferMap B X = X.trace • σ) :
    Kraus.IsInjective B := by
  classical
  have hG : ((physicalMatrix B)ᴴ * physicalMatrix B).PosDef := by
    rw [physicalGram_eq_fixedPoint B σ hB]
    exact (Matrix.PosDef.transpose_iff.2 hσ).kronecker Matrix.PosDef.one
  apply Submodule.eq_top_iff'.mpr
  intro X
  obtain ⟨v, hv⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hG.isUnit)
    (fun p : Fin D × Fin D => X p.1 p.2)
  have hc : (v ᵥ* (physicalMatrix B)ᴴ) ᵥ* physicalMatrix B =
      (fun p : Fin D × Fin D => X p.1 p.2) := by
    rw [Matrix.vecMul_vecMul]
    exact hv
  have hX : (∑ i : Fin n, (v ᵥ* (physicalMatrix B)ᴴ) i • B i) = X := by
    ext a b
    simpa [Matrix.vecMul, dotProduct, physicalMatrix, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] using congrFun hc (a, b)
  rw [← hX]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end MPSTensor
