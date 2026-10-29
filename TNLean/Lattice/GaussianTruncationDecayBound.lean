/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PowerExponential

/-!
# Scalar bounds for Gaussian localization

The Gaussian error and the spatial localization error have different
exponential rates, and the latter carries a linear time prefactor.
Absorbing this prefactor gives half the smaller rate, with an explicit
constant independent of the number of sites. A second estimate controls the
three Gaussian-filter errors at the common window `T=l/(4v)`.

Source: Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `facld`,
lines 322–349 and 1562–1601.
-/

namespace TNLean.Lattice

/-- The three Gaussian-filter errors decay at rate `min(1/4, Δ/(8v))` for the
window `T=l/(4v)` and filter parameter `q=TΔ`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm`, lines 1562–1601. -/
theorem commutator_time_window_exp_bounds {v Δ l : ℝ} (hv : 0 < v) (hΔ : 0 < Δ)
    (hl : 0 ≤ l) :
    let T := l / (4 * v)
    let q := T * Δ
    let γ := min (1 / 4) (Δ / (8 * v))
    Real.exp (v * T - l / 2) ≤ Real.exp (-(γ * l)) ∧
      Real.exp (-(T * Δ) ^ 2 / (2 * q)) ≤ Real.exp (-(γ * l)) ∧
      Real.exp (-q / 2) ≤ Real.exp (-(γ * l)) := by
  let T := l / (4 * v)
  let q := T * Δ
  let γ := min (1 / 4) (Δ / (8 * v))
  have hvT : v * T = l / 4 := by dsimp [T]; field_simp
  have hqT : (T * Δ) ^ 2 / (2 * q) = q / 2 := by
    dsimp only [q]
    rcases eq_or_ne (T * Δ) 0 with h0 | h0
    · rw [h0]; simp
    · field_simp
  have hq8 : q / 2 = Δ / (8 * v) * l := by dsimp [q, T]; field_simp; ring
  have hγ4 : γ ≤ 1 / 4 := min_le_left _ _
  have hγ8 : γ ≤ Δ / (8 * v) := min_le_right _ _
  refine ⟨Real.exp_le_exp.mpr ?_, Real.exp_le_exp.mpr ?_, Real.exp_le_exp.mpr ?_⟩
  · change v * T - l / 2 ≤ -(γ * l)
    rw [hvT]
    nlinarith
  · change -(T * Δ) ^ 2 / (2 * q) ≤ -(γ * l)
    rw [neg_div, hqT, hq8]
    nlinarith
  · change -q / 2 ≤ -(γ * l)
    rw [neg_div, hq8]
    nlinarith

/-- Absorb a linear prefactor into half the smaller exponential decay rate.
Hastings, arXiv:cond-mat/0508554v3, eq. `facld`, lines 322–349. -/
lemma gaussian_truncation_bound_le_exp {a γ A w l : ℝ}
    (ha : 0 < a) (hγ : 0 < γ) (hA : 0 ≤ A) (hw : 0 ≤ w) (hl : 0 ≤ l) :
    let δ := min a γ
    3 * w * Real.exp (-(a * l) / 2) + A * w * l * Real.exp (-(γ * l)) ≤
      w * (3 + A / (Real.exp 1 * (δ / 2))) * Real.exp (-(δ / 2) * l) := by
  intro δ
  have hδ : 0 < δ := lt_min ha hγ
  have hfirst : Real.exp (-(a * l) / 2) ≤ Real.exp (-(δ / 2) * l) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left a γ])
  have hsecond : Real.exp (-(γ * l)) ≤ Real.exp (-(δ * l)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right a γ])
  have hlinear : l * Real.exp (-(δ * l)) ≤
      (1 / (Real.exp 1 * (δ / 2))) * Real.exp (-(δ / 2) * l) := by
    simpa only [pow_one, Nat.cast_one, add_halves, neg_mul] using
      TNLean.MPS.AreaLaw.Hastings.pow_mul_exp_neg_add_le
        (r := δ / 2) (half_pos hδ) hl 1
  calc 3 * w * Real.exp (-(a * l) / 2) + A * w * l * Real.exp (-(γ * l))
      ≤ 3 * w * Real.exp (-(δ / 2) * l) + A * w * (l * Real.exp (-(δ * l))) := by
        have h1 := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 3 * w by positivity)
        have h2 := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ A * w * l by positivity)
        nlinarith
    _ ≤ 3 * w * Real.exp (-(δ / 2) * l) + A * w *
        ((1 / (Real.exp 1 * (δ / 2))) * Real.exp (-(δ / 2) * l)) := by gcongr
    _ = _ := by ring

end TNLean.Lattice
