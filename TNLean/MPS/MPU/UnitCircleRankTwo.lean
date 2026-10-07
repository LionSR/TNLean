/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic

/-!
# Unit-circle factorizations of dimension two

The circle–line intersection argument used for diagonal matrix product unitaries
of operator Schmidt rank at most two. The circuit argument is recorded separately
in `docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. Only the geometric lemmas,
with their explicitly stated factorization hypotheses, are formalized here.
-/

namespace Complex

/-- Three points on a vertical line with the same squared modulus cannot be distinct.
This is the circle–line intersection step in the proof of Lemma 1 of
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem eq_or_eq_or_eq_of_re_eq_of_normSq_eq (x y z : ℂ) (hxy : x.re = y.re) (hxz : x.re = z.re)
    (hxyN : Complex.normSq x = Complex.normSq y)
    (hxzN : Complex.normSq x = Complex.normSq z) : x = y ∨ x = z ∨ y = z := by
  have him : x.im ^ 2 = y.im ^ 2 := by
    simp only [Complex.normSq_apply, hxy] at hxyN
    nlinarith
  have himz : x.im ^ 2 = z.im ^ 2 := by
    simp only [Complex.normSq_apply, hxz] at hxzN
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with h | h <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp himz with h' | h' <;>
    simp_all [Complex.ext_iff]

/-- A real linear functional constant on three distinct unit-circle points is zero.
This is a step in the proof of Lemma 1 of
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem eq_zero_of_re_mul_eq_of_three_unit_points (k u v w : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w = 1) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hreuv : (k * u).re = (k * v).re) (hreuw : (k * u).re = (k * w).re) : k = 0 := by
  have hc := eq_or_eq_or_eq_of_re_eq_of_normSq_eq (k * u) (k * v) (k * w) hreuv hreuw
    (by simp [Complex.normSq_mul, hu, hv]) (by simp [Complex.normSq_mul, hu, hw])
  grind

/-- An affine function mapping three distinct unit-circle points to the unit circle
has a vanishing constant or linear coefficient. This is the three-value case in the
proof of Lemma 1 of `docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem eq_zero_or_eq_zero_of_three_unit_affine_values (a b u v w : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w = 1) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h0 : Complex.normSq (a + b * u) = 1)
    (h1 : Complex.normSq (a + b * v) = 1)
    (h2 : Complex.normSq (a + b * w) = 1) : a = 0 ∨ b = 0 := by
  simp only [Complex.normSq_add, hu, hv, hw, map_mul, mul_one] at h0 h1 h2
  have hlin : a * star b = 0 := by
    apply eq_zero_of_re_mul_eq_of_three_unit_points (a * star b) (star u) (star v) (star w)
      (by simpa using hu) (by simpa using hv) (by simpa using hw)
      (star_injective.ne huv) (star_injective.ne huw) (star_injective.ne hvw)
    all_goals
      simp only [mul_assoc, Complex.star_def]
      nlinarith
  simpa using mul_eq_zero.mp hlin

/-- For a unit-modulus factorization `a i + b i * t j`, either every row has only one
nonzero coefficient, or the unit-circle parameter `t` takes at most two values.
This is the geometric step in the exact diagonal rank-two circuit argument in
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`, Lemma 1. It does not itself
assert a quantum-circuit implementation. -/
theorem unitCircle_factorization_dichotomy {ι κ : Type*} [Nonempty κ] (a b : ι → ℂ) (t : κ → ℂ)
    (ht : ∀ j, Complex.normSq (t j) = 1)
    (hM : ∀ i j, Complex.normSq (a i + b i * t j) = 1) :
    (∀ i, a i = 0 ∨ b i = 0) ∨ ∃ j₀ j₁, ∀ j, t j = t j₀ ∨ t j = t j₁ := by
  classical
  by_cases hex : ∃ j k l, t j ≠ t k ∧ t j ≠ t l ∧ t k ≠ t l
  · obtain ⟨j, k, l, hjk, hjl, hkl⟩ := hex
    exact Or.inl fun i =>
      eq_zero_or_eq_zero_of_three_unit_affine_values (a i) (b i) (t j) (t k) (t l)
      (ht j) (ht k) (ht l) hjk hjl hkl (hM i j) (hM i k) (hM i l)
  · right
    let j₀ : κ := Classical.arbitrary κ
    by_cases hsame : ∀ j, t j = t j₀
    · exact ⟨j₀, j₀, fun j => Or.inl (hsame j)⟩
    · push Not at hsame
      obtain ⟨j₁, hj₁⟩ := hsame
      refine ⟨j₀, j₁, fun j => ?_⟩
      by_contra h
      push Not at h
      exact hex ⟨j₀, j₁, j, Ne.symm hj₁, Ne.symm h.1, Ne.symm h.2⟩

end Complex
