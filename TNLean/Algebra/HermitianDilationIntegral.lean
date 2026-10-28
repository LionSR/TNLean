/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianDilation
import TNLean.Algebra.TraceExpIntegralBounds
import QICLean.Analysis.OperatorMean.BlockDiagonal
import QICLean.Analysis.LiebOperatorConcave
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Hermitian dilation and Bochner integration

The square-matrix Hermitian dilation is a real-linear isometry. Hence its Bochner
integral commutes with the dilation, including functions whose integrability has
not been supplied. For bounded measurable matrix families, the norm of the
integrated squared dilation is bounded by the maximum of the two actual
integrated Gram-matrix norms. The required integrability is derived.

These are the integral dilation identities used in Tropp, *User-friendly tail
bounds for sums of random matrices*, equations (2.12)--(2.13) and Remark 3.11:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open MeasureTheory

namespace Matrix

/-- The Hermitian dilation as a real-linear isometry for the operator norm.
This combines the real-linearity and norm identity in Tropp, equation (2.12). -/
noncomputable def hermitianDilationLinearIsometry {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n] :
    Matrix n n ℂ →ₗᵢ[ℝ] Matrix (n ⊕ n) (n ⊕ n) ℂ where
  toFun := hermitianDilation
  map_add' A B := by
    simpa [Fin.sum_univ_two] using hermitianDilation_sum (fun i : Fin 2 ↦ ![A, B] i)
  map_smul' c A := hermitianDilation_real_smul A c
  norm_map' := norm_hermitianDilation

/-- Hermitian dilation commutes with the Bochner integral. The real-linear
isometry supplies the identity without an integrability premise; Tropp, Remark 3.11. -/
theorem integral_hermitianDilation {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] [Nonempty n] (P : Measure Ω) (Y : Ω → Matrix n n ℂ) :
    (∫ ω, hermitianDilation (Y ω) ∂P) = hermitianDilation (∫ ω, Y ω ∂P) :=
  hermitianDilationLinearIsometry.integral_comp_comm Y

private theorem posSemidef_fromBlocks_diag
    {n : Type*} [Finite n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A 0 0 B).PosSemidef := by
  classical
  let _ := Fintype.ofFinite n
  have hleft := hA.mul_mul_conjTranspose_same
    (fromRows (1 : Matrix n n ℂ) (0 : Matrix n n ℂ))
  have hright := hB.mul_mul_conjTranspose_same
    (fromRows (0 : Matrix n n ℂ) (1 : Matrix n n ℂ))
  rw [fromRows_mul, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromRows_mul_fromCols] at hleft hright
  simp only [conjTranspose_one, conjTranspose_zero, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul] at hleft hright
  simpa only [fromBlocks_add, zero_add, add_zero] using hleft.add hright

private theorem norm_fromBlocks_diag_le_max
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖fromBlocks A 0 0 B‖ ≤ max ‖A‖ ‖B‖ := by
  have hmax : 0 ≤ max ‖A‖ ‖B‖ := (norm_nonneg A).trans (le_max_left _ _)
  have hAc : A ≤ (max ‖A‖ ‖B‖) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap A hmax hA.nonneg).mp (le_max_left _ _)
  have hBc : B ≤ (max ‖A‖ ‖B‖) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap B hmax hB.nonneg).mp (le_max_right _ _)
  have hcap : fromBlocks A 0 0 B ≤ (max ‖A‖ ‖B‖) •
      (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
    rw [Matrix.le_iff]
    have hp := posSemidef_fromBlocks_diag (Matrix.le_iff.mp hAc) (Matrix.le_iff.mp hBc)
    convert hp using 1
    simp only [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg,
      fromBlocks_add, smul_zero, neg_zero, add_zero]
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _
    (le_trans (norm_nonneg A) (le_max_left _ _)) (posSemidef_fromBlocks_diag hA hB).nonneg).mpr
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hcap)

/-- The integrated dilation variance is bounded by the maximum of the actual two
Gram variance norms. Bounded measurability derives the necessary integrability.
This is the integral domination used in Tropp, Theorem 1.6. -/
theorem norm_integral_hermitianDilation_sq_le
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → Matrix n n ℂ}
    (hYm : AEStronglyMeasurable Y P) {R : ℝ} (hbound : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R) :
    ‖∫ ω, hermitianDilation (Y ω) ^ 2 ∂P‖ ≤
      max ‖∫ ω, Y ω * (Y ω)ᴴ ∂P‖ ‖∫ ω, (Y ω)ᴴ * Y ω ∂P‖ := by
  let E : Matrix n n ℂ →L[ℂ] Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks₁₁L
  let F : Matrix n n ℂ →L[ℂ] Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks₂₂L
  let A : Matrix n n ℂ := ∫ ω, Y ω * (Y ω)ᴴ ∂P
  let B : Matrix n n ℂ := ∫ ω, (Y ω)ᴴ * Y ω ∂P
  have hiA := integrable_continuous_comp_of_ae_norm_le hYm hbound
    (by fun_prop : Continuous (fun Z : Matrix n n ℂ ↦ Z * Zᴴ))
  have hiB := integrable_continuous_comp_of_ae_norm_le hYm hbound
    (by fun_prop : Continuous (fun Z : Matrix n n ℂ ↦ Zᴴ * Z))
  have hA : A.PosSemidef := integral_posSemidef_of_ae
    (Filter.Eventually.of_forall fun ω ↦ posSemidef_self_mul_conjTranspose (Y ω))
  have hB : B.PosSemidef := integral_posSemidef_of_ae
    (Filter.Eventually.of_forall fun ω ↦ posSemidef_conjTranspose_mul_self (Y ω))
  have hpoint (ω : Ω) : hermitianDilation (Y ω) ^ 2 =
      E (Y ω * (Y ω)ᴴ) + F ((Y ω)ᴴ * Y ω) := by
    rw [hermitianDilation_sq]
    simp only [E, F, fromBlocks₁₁L, fromBlocks₂₂L, LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk, fromBlocks_add, zero_add, add_zero]
  have heq : (∫ ω, hermitianDilation (Y ω) ^ 2 ∂P) = fromBlocks A 0 0 B := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_add (E.integrable_comp hiA) (F.integrable_comp hiB),
      E.integral_comp_comm hiA, F.integral_comp_comm hiB]
    simp only [E, F, fromBlocks₁₁L, fromBlocks₂₂L, LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk, fromBlocks_add, zero_add, add_zero]
    rfl
  rw [heq]
  exact norm_fromBlocks_diag_le_max hA hB

end Matrix
