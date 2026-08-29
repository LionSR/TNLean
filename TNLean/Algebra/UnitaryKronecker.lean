/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Algebra.ComplexSqrt

/-!
# Unitary factors of a Kronecker product

This file proves that a unitary Kronecker product over the complex numbers has
unitary factors after reciprocal rescaling by one positive real number.  The
algebraic core is an entrywise characterization of two matrices whose
Kronecker product is the identity.

## Main results

- `Matrix.exists_eq_smul_one_of_kronecker_eq_one`: the two factors of a
  Kronecker product equal to the identity are reciprocal scalar matrices.
- `Matrix.exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup`:
  the factors of a unitary Kronecker product become unitary after reciprocal
  positive rescaling.
- `Matrix.exists_pos_real_smul_unitary_factors_of_kronecker_mem_unitaryGroup`:
  the equivalent factorization into a positive scalar and unitary matrices.
-/

open scoped ComplexOrder Kronecker

namespace Matrix

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]

/-- If a Kronecker product of two complex square matrices is the identity, then
its factors are reciprocal nonzero scalar matrices. -/
theorem exists_eq_smul_one_of_kronecker_eq_one
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (h : A ⊗ₖ B = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ A = c • 1 ∧ B = c⁻¹ • 1 := by
  classical
  let i₀ : m := Classical.choice inferInstance
  let j₀ : n := Classical.choice inferInstance
  have hdiag : A i₀ i₀ * B j₀ j₀ = 1 := by
    have := congrFun (congrFun h (i₀, j₀)) (i₀, j₀)
    simpa [kroneckerMap_apply] using this
  have hc : A i₀ i₀ ≠ 0 := fun hc ↦ by simp [hc] at hdiag
  refine ⟨A i₀ i₀, hc, ?_, ?_⟩
  · ext i i'
    have hij := congrFun (congrFun h (i, j₀)) (i', j₀)
    simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq] at hij
    rw [show B j₀ j₀ = (A i₀ i₀)⁻¹ by
      exact eq_inv_of_mul_eq_one_right hdiag] at hij
    simp only [smul_apply, one_apply]
    split_ifs with hii
    · subst i'
      simp only [true_and, ↓reduceIte] at hij
      simpa [hc] using eq_inv_of_mul_eq_one_left hij
    · have : A i i' = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right (inv_ne_zero hc)
        simpa [hii] using hij
      simp [this]
  · ext j j'
    have hij := congrFun (congrFun h (i₀, j)) (i₀, j')
    simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq] at hij
    simp only [smul_apply, one_apply]
    split_ifs with hjj
    · subst j'
      simp only [true_and, ↓reduceIte] at hij
      simpa [smul_eq_mul] using eq_inv_of_mul_eq_one_right hij
    · have : B j j' = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hc
        simpa [hjj] using hij
      simp [this]

variable [Fintype m] [Fintype n]

/-- If a Kronecker product is unitary, reciprocal positive rescalings of its
factors are unitary.  This is the tensor-factor step in FBC25, Lemma
`lem:deco` (arXiv:2502.20257, lines 1052--1066). -/
theorem exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup
    {K₁ : Matrix m m ℂ} {K₂ : Matrix n n ℂ}
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ) :
    ∃ δ : ℝ, 0 < δ ∧
      ((δ : ℂ)⁻¹ • K₁) ∈ Matrix.unitaryGroup m ℂ ∧
      ((δ : ℂ) • K₂) ∈ Matrix.unitaryGroup n ℂ := by
  classical
  have hgram : (K₁ᴴ * K₁) ⊗ₖ (K₂ᴴ * K₂) = 1 := by
    rw [mul_kronecker_mul, ← conjTranspose_kronecker]
    exact mem_unitaryGroup_iff'.mp hK
  obtain ⟨c, hc, hK₁, hK₂⟩ := exists_eq_smul_one_of_kronecker_eq_one hgram
  have hc_nonneg : 0 ≤ c := by
    let i₀ : m := Classical.choice inferInstance
    have hpos := (posSemidef_conjTranspose_mul_self K₁).diag_nonneg (i := i₀)
    rw [hK₁] at hpos
    simpa using hpos
  let r : ℝ := c.re
  have hc_eq : c = (r : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [r] using (Complex.nonneg_iff.mp hc_nonneg).2.symm
  have hr_nonneg : 0 ≤ r := (Complex.nonneg_iff.mp hc_nonneg).1
  have hr_ne : r ≠ 0 := by
    intro hr
    apply hc
    rw [hc_eq, hr]
    exact Complex.ofReal_zero
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
  let δ := Real.sqrt r
  have hδ_pos : 0 < δ := Real.sqrt_pos.2 hr_pos
  have hδ_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ_pos.ne'
  have hδ_sq : (δ : ℂ) ^ 2 = (r : ℂ) := Complex.ofReal_sqrt_sq r hr_nonneg
  refine ⟨δ, hδ_pos, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    rw [show star ((δ : ℂ)⁻¹ • K₁) = (δ : ℂ)⁻¹ • K₁ᴴ by
      simp [star_eq_conjTranspose]]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hK₁, hc_eq]
    simp only [smul_smul]
    rw [← hδ_sq]
    field_simp
    simp
  · rw [mem_unitaryGroup_iff']
    rw [show star ((δ : ℂ) • K₂) = (δ : ℂ) • K₂ᴴ by
      simp [star_eq_conjTranspose]]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hK₂, hc_eq]
    simp only [smul_smul]
    rw [← hδ_sq]
    field_simp
    simp

/-- Equivalently, the factors of a unitary Kronecker product are a positive
real scalar and its reciprocal times unitary matrices.  This packages the
rescaled matrices from
`Matrix.exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup`
as elements of the matrix unitary groups. -/
theorem exists_pos_real_smul_unitary_factors_of_kronecker_mem_unitaryGroup
    {K₁ : Matrix m m ℂ} {K₂ : Matrix n n ℂ}
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ) :
    ∃ (δ : ℝ) (_ : 0 < δ) (W₁ : Matrix.unitaryGroup m ℂ)
      (W₂ : Matrix.unitaryGroup n ℂ),
      K₁ = (δ : ℂ) • (W₁ : Matrix m m ℂ) ∧
      K₂ = (δ : ℂ)⁻¹ • (W₂ : Matrix n n ℂ) := by
  obtain ⟨δ, hδ, hK₁, hK₂⟩ :=
    exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup hK
  let W₁ : Matrix.unitaryGroup m ℂ := ⟨(δ : ℂ)⁻¹ • K₁, hK₁⟩
  let W₂ : Matrix.unitaryGroup n ℂ := ⟨(δ : ℂ) • K₂, hK₂⟩
  have hδ_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  refine ⟨δ, hδ, W₁, W₂, ?_, ?_⟩
  · change K₁ = (δ : ℂ) • ((δ : ℂ)⁻¹ • K₁)
    rw [smul_smul, mul_inv_cancel₀ hδ_ne, one_smul]
  · change K₂ = (δ : ℂ)⁻¹ • ((δ : ℂ) • K₂)
    rw [smul_smul, inv_mul_cancel₀ hδ_ne, one_smul]

end Matrix
