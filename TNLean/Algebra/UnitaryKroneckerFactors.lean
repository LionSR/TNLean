/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import QICLean.Algebra.MatrixGramUnitary

/-!
# Unitary factors of a Kronecker product

A unitary Kronecker product of two nonempty finite square complex matrices has factors that are
unitary up to reciprocal positive rescalings.  This is the elementary matrix step used in the
proof of `lem:deco` in arXiv:2502.20257: if `K₁ ⊗ₖ K₂` is unitary, then for some `δ > 0`,
`δ⁻¹ K₁` and `δ K₂` are unitary.

The proof first extracts reciprocal scalar factors from an identity `A ⊗ₖ B = 1`.  Applying this
to the column Gram matrices gives the positive scalar.  The row Gram identities then follow from
the unitarity of the rescaled factors.
-/

open scoped ComplexOrder Matrix Kronecker

namespace Matrix

/-- If a Kronecker product of two nonempty square complex matrices is the identity, then its
factors are reciprocal nonzero scalar matrices. -/
theorem eq_smul_one_and_inv_smul_one_of_kronecker_eq_one
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (h : A ⊗ₖ B = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ A = c • 1 ∧ B = c⁻¹ • 1 := by
  classical
  let i₀ : m := Classical.choice inferInstance
  let j₀ : n := Classical.choice inferInstance
  have hdiag (i : m) (j : n) : A i i * B j j = 1 := by
    have hij := congr_fun (congr_fun h (i, j)) (i, j)
    simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using hij
  have hBdiag_ne (j : n) : B j j ≠ 0 := by
    intro hj
    simpa [hj] using hdiag i₀ j
  have hAdiag_ne (i : m) : A i i ≠ 0 := by
    intro hi
    simpa [hi] using hdiag i j₀
  refine ⟨A i₀ i₀, hAdiag_ne i₀, ?_, ?_⟩
  · ext i i'
    by_cases hii : i = i'
    · subst i'
      have hi := hdiag i j₀
      have hi₀ := hdiag i₀ j₀
      have heq : A i i = A i₀ i₀ := by
        apply mul_right_cancel₀ (hBdiag_ne j₀)
        exact hi.trans hi₀.symm
      simpa [Matrix.smul_apply, Matrix.one_apply] using heq
    · have hij := congr_fun (congr_fun h (i, j₀)) (i', j₀)
      have hzero : A i i' * B j₀ j₀ = 0 := by
        simpa [Matrix.kroneckerMap_apply, Matrix.one_apply, hii] using hij
      have : A i i' = 0 := (mul_eq_zero.mp hzero).resolve_right (hBdiag_ne j₀)
      simpa [Matrix.smul_apply, Matrix.one_apply, hii] using this
  · ext j j'
    by_cases hjj : j = j'
    · subst j'
      have hj := hdiag i₀ j
      have hc := hAdiag_ne i₀
      have heq : B j j = (A i₀ i₀)⁻¹ := by
        apply mul_left_cancel₀ hc
        rw [hj]
        exact (mul_inv_cancel₀ hc).symm
      simpa [Matrix.smul_apply, Matrix.one_apply] using heq
    · have hij := congr_fun (congr_fun h (i₀, j)) (i₀, j')
      have hzero : A i₀ i₀ * B j j' = 0 := by
        simpa [Matrix.kroneckerMap_apply, Matrix.one_apply, hjj] using hij
      have : B j j' = 0 := (mul_eq_zero.mp hzero).resolve_left (hAdiag_ne i₀)
      simpa [Matrix.smul_apply, Matrix.one_apply, hjj] using this

/-- **FBC25, Lemma `lem:deco`, matrix rescaling step.**

Let `K₁` and `K₂` be square complex matrices on nonempty finite index types. If their
Kronecker product is unitary, then there is a positive real number `δ` such that `δ⁻¹ K₁` and
`δ K₂` are unitary. Both the column and row Gram matrices of the original factors are the
corresponding reciprocal scalar multiples of the identity.

Source: arXiv:2502.20257, Lemma `lem:deco`, lines 1053--1066. -/
theorem exists_pos_rescaling_mem_unitaryGroup_of_kronecker
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] (K₁ : Matrix m m ℂ) (K₂ : Matrix n n ℂ)
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ) :
    ∃ δ : ℝ, 0 < δ ∧
      ((δ : ℂ)⁻¹ • K₁ ∈ Matrix.unitaryGroup m ℂ) ∧
      ((δ : ℂ) • K₂ ∈ Matrix.unitaryGroup n ℂ) ∧
      K₁ᴴ * K₁ = ((δ ^ 2 : ℝ) : ℂ) • 1 ∧
      K₁ * K₁ᴴ = ((δ ^ 2 : ℝ) : ℂ) • 1 ∧
      K₂ᴴ * K₂ = (((δ ^ 2 : ℝ) : ℂ)⁻¹) • 1 ∧
      K₂ * K₂ᴴ = (((δ ^ 2 : ℝ) : ℂ)⁻¹) • 1 := by
  classical
  have hcol : (K₁ᴴ * K₁) ⊗ₖ (K₂ᴴ * K₂) = 1 := by
    rw [Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker]
    exact Matrix.mem_unitaryGroup_iff'.mp hK
  obtain ⟨c, hc, hgram₁, hgram₂⟩ :=
    eq_smul_one_and_inv_smul_one_of_kronecker_eq_one (K₁ᴴ * K₁) (K₂ᴴ * K₂) hcol
  let i₀ : m := Classical.choice inferInstance
  have hc_nonneg : 0 ≤ c := by
    have hdiag : 0 ≤ (K₁ᴴ * K₁) i₀ i₀ := by
      simpa using (Matrix.posSemidef_conjTranspose_mul_self K₁).2 (Finsupp.single i₀ 1)
    rw [hgram₁] at hdiag
    simpa [Matrix.smul_apply, Matrix.one_apply] using hdiag
  have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg hc.symm
  let ω : ℝ := c.re
  have hω : 0 < ω := (Complex.pos_iff.mp hc_pos).1
  have hc_eq : c = (ω : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [ω] using (Complex.pos_iff.mp hc_pos).2.symm
  rw [hc_eq] at hgram₁ hgram₂
  let δ : ℝ := Real.sqrt ω
  have hδ : 0 < δ := Real.sqrt_pos.mpr hω
  have hδsq : δ ^ 2 = ω := Real.sq_sqrt hω.le
  have hstarδ : star (δ : ℂ) = (δ : ℂ) := Complex.conj_ofReal δ
  have hcastδsq : (δ : ℂ) * (δ : ℂ) = ((δ ^ 2 : ℝ) : ℂ) := by
    rw [← pow_two, ← Complex.ofReal_pow]
  have hinvδsq : (δ : ℂ)⁻¹ * (δ : ℂ)⁻¹ = (((δ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [← mul_inv, hcastδsq]
  have hW₁ : ((δ : ℂ)⁻¹ • K₁) ∈ Matrix.unitaryGroup m ℂ := by
    simpa [δ] using
      Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hω hgram₁
  have hscalar₂ : (δ : ℂ) * (δ : ℂ) * (ω : ℂ)⁻¹ = 1 := by
    rw [← pow_two, ← Complex.ofReal_pow, hδsq, mul_inv_cancel₀]
    exact_mod_cast hω.ne'
  have hW₂ : ((δ : ℂ) • K₂) ∈ Matrix.unitaryGroup n ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, hstarδ]
    rw [Matrix.smul_mul, Matrix.mul_smul, hgram₂, smul_smul, smul_smul, hscalar₂,
      one_smul]
  have hrepr₁ : K₁ = (δ : ℂ) • ((δ : ℂ)⁻¹ • K₁) := by
    rw [smul_smul]
    simp [hδ.ne']
  have hrepr₂ : K₂ = (δ : ℂ)⁻¹ • ((δ : ℂ) • K₂) := by
    rw [smul_smul]
    simp [hδ.ne']
  have hW₁row :
      ((δ : ℂ)⁻¹ • K₁) * ((δ : ℂ)⁻¹ • K₁)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hW₁
  have hW₂row : ((δ : ℂ) • K₂) * ((δ : ℂ) • K₂)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hW₂
  have hrow₁ : K₁ * K₁ᴴ = ((δ ^ 2 : ℝ) : ℂ) • 1 := by
    rw [hrepr₁, Matrix.conjTranspose_smul, hstarδ]
    rw [Matrix.smul_mul, Matrix.mul_smul, hW₁row, smul_smul, hcastδsq]
  have hrow₂ : K₂ * K₂ᴴ = (((δ ^ 2 : ℝ) : ℂ)⁻¹) • 1 := by
    rw [hrepr₂, Matrix.conjTranspose_smul, star_inv₀, hstarδ]
    rw [Matrix.smul_mul, Matrix.mul_smul, hW₂row, smul_smul, hinvδsq]
  refine ⟨δ, hδ, hW₁, hW₂, ?_, hrow₁, ?_, hrow₂⟩
  · simpa [hδsq] using hgram₁
  · simpa [hδsq] using hgram₂

end Matrix
