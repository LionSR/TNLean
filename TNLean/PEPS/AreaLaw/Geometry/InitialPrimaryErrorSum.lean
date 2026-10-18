/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales
import TNLean.PEPS.AreaLaw.Geometry.PrimaryCounting
import TNLean.PEPS.AreaLaw.Geometry.PolynomialBudget

/-!
# The weighted error sum for primary regions

Each layer contains at most a fixed multiple of the edge boundary in primary
regions. The scale assigned in the manuscript grows with the layer, so the
sum of its inverse hundredth powers has a uniform bound over every finite
set of layers. The coefficient is chosen before the geometric data, the
residue families, and the finite set of layers.

The estimate uses the existing primary indices for arbitrary integer residue
families, hence also for the joint choices of the initial construction. It
does not assert finiteness of the primary family over all layers. The scale
is written directly in the statement; assigning it to the actual templates
and identifying retained primary regions are separate geometric results.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:primary-scale`, lines 709–729,
especially line 714, and the primary error sum, lines 791–795.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The primary error-sum coefficient `32 (C_P ^ 100)⁻¹ B₀` with
`B₀ = polynomialDyadicBudget 0`. It is the coefficient `M_p` of the two-family
decomposition. Auxiliary to the explicit constant of Theorem 1.1
(`docs/notes/arealaw2d_explicit_constant.tex`).
Source: area-law Section 11, `geometry:primary-scale`, line 714, and the
primary error contribution, lines 791–795. -/
def primaryErrorSumConstant (C_P : ℝ) : ℝ :=
  32 * (C_P ^ 100)⁻¹ * polynomialDyadicBudget 0

/-- The primary error-sum coefficient is positive for `C_P > 0`. -/
theorem primaryErrorSumConstant_pos {C_P : ℝ} (hC_P : 0 < C_P) :
    0 < primaryErrorSumConstant C_P := by
  have := polynomialDyadicBudget_pos 0
  unfold primaryErrorSumConstant
  positivity

/-- **Primary error sum with an explicit coefficient.** The inverse hundredth
powers of the prescribed primary scales have boundary-weighted sum at most
`primaryErrorSumConstant C_P (2 C₀ + 1) ^ 2 |∂A|` over every finite set of layers.
Source: area-law Section 11, `geometry:primary-scale`, line 714, and the
primary error contribution, lines 791–795. -/
theorem primaryPitchIndices_error_sum_le {C_P : ℝ} (hC_P : 0 < C_P)
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (C : ℕ) (a b : ℕ → ℤ) (F : Finset ℕ) :
    let n : ℕ → ℕ := fun k ↦
      ⌈C_P * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊
    ∑ k ∈ F,
        ((primaryPitchIndices o k (fineScaleIndex k) (pitchScaleIndex k)
          (boundaryEndpoints Λ A) C (a k) (b k)).card : ℝ) *
          (((n k : ℝ) ^ 100)⁻¹) ≤
      primaryErrorSumConstant C_P * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  unfold primaryErrorSumConstant
  intro n
  set B := polynomialDyadicBudget 0
  have hBpos : 0 < B := polynomialDyadicBudget_pos 0
  have hB := sum_le_polynomialDyadicBudget 0
  have hn (k : ℕ) : C_P * (2 : ℝ) ^ k ≤ (n k : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_one_le (one_le_pow₀ (by norm_num))
        (by norm_num [Exponents.geometryDelta])) hC_P.le).trans (Nat.le_ceil _)
  have hpow (k : ℕ) : (n k : ℝ) ^ (-100 : ℝ) ≤
      (C_P * (2 : ℝ) ^ k) ^ (-100 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (hn k) (by norm_num)
  have hscaled (k : ℕ) : ((n k : ℝ) ^ 100)⁻¹ ≤
      (C_P ^ 100)⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (-100 : ℝ)) := by
    simpa only [Real.mul_rpow hC_P.le (by positivity : 0 ≤ (2 : ℝ) ^ k),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) k (-100 : ℝ),
      Real.rpow_neg (Nat.cast_nonneg (n k)) 100, Real.rpow_neg hC_P.le 100,
      Real.rpow_ofNat] using hpow k
  have hw (k : ℕ) : ((n k : ℝ) ^ 100)⁻¹ ≤
      (C_P ^ 100)⁻¹ * (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) :=
    (hscaled k).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        nlinarith only [mul_nonneg
          (show 0 ≤ 200 - (Exponents.geometryDelta : ℝ) by
            norm_num [Exponents.geometryDelta]) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
      (by positivity))
  have hc (k : ℕ) :
      ((primaryPitchIndices o k (fineScaleIndex k) (pitchScaleIndex k)
        (boundaryEndpoints Λ A) C (a k) (b k)).card : ℝ) ≤
        32 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
    exact_mod_cast card_primaryPitchIndices_boundary_le o k (fineScaleIndex k)
      (pitchScaleIndex k) Λ A C (a k) (b k) (le_pitchScaleIndex k)
  refine (Finset.sum_le_sum (fun k _ ↦
    mul_le_mul (hc k) (hw k) (by positivity) (by positivity))).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ ≤ 32 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
        ((C_P ^ 100)⁻¹ * B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (by simpa only [Real.rpow_zero, one_mul] using hB F) (by positivity))
        (by positivity)
    _ = _ := by ring

/-- The inverse hundredth powers of the prescribed primary scales have a
uniform boundary-weighted sum over every finite set of layers. The constant
may depend on the positive scale coefficient, but precedes the origin,
domain, cut, width, residues, and layers. No repair or boundary-positivity
hypothesis is needed. The constant is `primaryErrorSumConstant C_P`
(`primaryPitchIndices_error_sum_le`).
Source: area-law Section 11, `geometry:primary-scale`, line 714, and the
primary error contribution, lines 791–795. -/
theorem exists_uniform_primaryPitchIndices_error_sum_bound {C_P : ℝ}
    (hC_P : 0 < C_P) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C : ℕ) (a b : ℕ → ℤ) (F : Finset ℕ),
        let n : ℕ → ℕ := fun k ↦
          ⌈C_P * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊
        ∑ k ∈ F,
            ((primaryPitchIndices o k (fineScaleIndex k) (pitchScaleIndex k)
              (boundaryEndpoints Λ A) C (a k) (b k)).card : ℝ) *
              (((n k : ℝ) ^ 100)⁻¹) ≤
          M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card :=
  ⟨_, primaryErrorSumConstant_pos hC_P, primaryPitchIndices_error_sum_le hC_P⟩

end TNLean.PEPS.AreaLaw.Geometry
