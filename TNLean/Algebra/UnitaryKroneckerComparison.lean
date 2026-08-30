/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryKronecker

/-!
# Comparison of matrix factorizations with unitary Kronecker gauges

This file isolates the matrix-algebraic core of the uniqueness argument for
three-legged decompositions of a matrix product unitary.  A chosen left inverse
and right inverse identify the comparison matrix between two factorizations.
When two such comparison matrices have unitary Kronecker product, their
reciprocal positive rescalings give the unitary gauges in the orientation of
the original decompositions.

## Main results

- `Matrix.factorization_comparison_of_one_sided_inverses`: compares two equal
  rectangular matrix factorizations using chosen one-sided inverses.
- `Matrix.exists_reciprocal_unitary_gauges_of_comparison`: converts two
  comparison matrices with unitary Kronecker product into reciprocal unitary
  gauges.
-/

open scoped Kronecker

namespace Matrix

/-- Suppose `X * Y` and `Xt * Yt` are the same matrix, `Lt` is a left inverse
of `Xt`, and `R` is a right inverse of `Y`.  Then `Lt * X` is the comparison
matrix between the two factorizations.

This is the one-sided-inverse step in FBC25, Lemma `lem:deco`
(arXiv:2502.20257, lines 1052--1066). -/
theorem factorization_comparison_of_one_sided_inverses
    {α β γ 𝕜 : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [Semiring 𝕜]
    {X Xt : Matrix α β 𝕜} {Y Yt : Matrix β γ 𝕜}
    {Lt : Matrix β α 𝕜} {R : Matrix γ β 𝕜}
    (hfac : X * Y = Xt * Yt) (hleft : Lt * Xt = 1) (hright : Y * R = 1) :
    Lt * X = Yt * R ∧ X = Xt * (Lt * X) ∧ Yt = (Lt * X) * Y := by
  have hK : Lt * X = Yt * R := by
    calc
      Lt * X = (Lt * X) * (Y * R) := by rw [hright, Matrix.mul_one]
      _ = Lt * (X * Y) * R := by simp only [Matrix.mul_assoc]
      _ = Lt * (Xt * Yt) * R := by rw [hfac]
      _ = (Lt * Xt) * Yt * R := by simp only [Matrix.mul_assoc]
      _ = Yt * R := by rw [hleft, Matrix.one_mul]
  refine ⟨hK, ?_, ?_⟩
  · calc
      X = X * (Y * R) := by rw [hright, Matrix.mul_one]
      _ = (X * Y) * R := by simp only [Matrix.mul_assoc]
      _ = (Xt * Yt) * R := by rw [hfac]
      _ = Xt * (Yt * R) := by simp only [Matrix.mul_assoc]
      _ = Xt * (Lt * X) := by rw [hK]
  · calc
      Yt = (Lt * Xt) * Yt := by rw [hleft, Matrix.one_mul]
      _ = Lt * (Xt * Yt) := by simp only [Matrix.mul_assoc]
      _ = Lt * (X * Y) := by rw [hfac]
      _ = (Lt * X) * Y := by simp only [Matrix.mul_assoc]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Nonempty m] [Nonempty n]

/-- Two comparison matrices whose Kronecker product `K₁ ⊗ₖ K₂` is unitary
determine unitary gauges with reciprocal positive scalars.  If the returned
scalar is `δ`, the source-oriented scalars are `δ⁻¹` for the first factor and
`δ` for the second, so their product is one.

The unitary matrices in the conclusion are the inverses, equivalently the
adjoints, of the unitary factors of the comparison matrices.  This is the
reciprocal-unitary-gauge step in FBC25, Lemma `lem:deco`
(arXiv:2502.20257, lines 1052--1066). -/
theorem exists_reciprocal_unitary_gauges_of_comparison
    {α₁ β₁ α₂ β₂ : Type*}
    {X₁ Xt₁ : Matrix α₁ m ℂ} {Y₁ Yt₁ : Matrix m β₁ ℂ}
    {X₂ Xt₂ : Matrix α₂ n ℂ} {Y₂ Yt₂ : Matrix n β₂ ℂ}
    {K₁ : Matrix m m ℂ} {K₂ : Matrix n n ℂ}
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ)
    (hX₁ : X₁ = Xt₁ * K₁) (hY₁ : Yt₁ = K₁ * Y₁)
    (hX₂ : X₂ = Xt₂ * K₂) (hY₂ : Yt₂ = K₂ * Y₂) :
    ∃ (δ : ℝ) (_ : 0 < δ) (W₁ : Matrix.unitaryGroup m ℂ)
      (W₂ : Matrix.unitaryGroup n ℂ),
      Xt₁ = (δ : ℂ)⁻¹ • (X₁ * (W₁ : Matrix m m ℂ)) ∧
      Yt₁ = (δ : ℂ) • (star (W₁ : Matrix m m ℂ) * Y₁) ∧
      Xt₂ = (δ : ℂ) • (X₂ * (W₂ : Matrix n n ℂ)) ∧
      Yt₂ = (δ : ℂ)⁻¹ • (star (W₂ : Matrix n n ℂ) * Y₂) ∧
      (δ : ℂ)⁻¹ * (δ : ℂ) = 1 := by
  classical
  obtain ⟨δ, hδ, U₁, U₂, hK₁, hK₂⟩ :=
    exists_pos_real_smul_unitary_factors_of_kronecker_mem_unitaryGroup hK
  have hδℂ : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  let W₁ : Matrix.unitaryGroup m ℂ := U₁⁻¹
  let W₂ : Matrix.unitaryGroup n ℂ := U₂⁻¹
  have hU₁W₁ : (U₁ : Matrix m m ℂ) * (W₁ : Matrix m m ℂ) = 1 := by
    change (U₁ : Matrix m m ℂ) * star (U₁ : Matrix m m ℂ) = 1
    exact U₁.2.2
  have hU₂W₂ : (U₂ : Matrix n n ℂ) * (W₂ : Matrix n n ℂ) = 1 := by
    change (U₂ : Matrix n n ℂ) * star (U₂ : Matrix n n ℂ) = 1
    exact U₂.2.2
  have hstarW₁ : star (W₁ : Matrix m m ℂ) = (U₁ : Matrix m m ℂ) := by
    simp [W₁]
  have hstarW₂ : star (W₂ : Matrix n n ℂ) = (U₂ : Matrix n n ℂ) := by
    simp [W₂]
  refine ⟨δ, hδ, W₁, W₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hX₁, hK₁, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hU₁W₁,
      Matrix.mul_one]
    ext i j
    simp [smul_apply, hδℂ]
  · rw [hY₁, hK₁, Matrix.smul_mul, hstarW₁]
  · rw [hX₂, hK₂, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hU₂W₂,
      Matrix.mul_one]
    ext i j
    simp [smul_apply, hδℂ]
  · rw [hY₂, hK₂, Matrix.smul_mul, hstarW₂]
  · exact inv_mul_cancel₀ hδℂ

end Matrix
