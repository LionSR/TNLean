/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The first Fourier mode of the cycle Laplacian

The nearest-neighbor cycle Laplacian with normalization
\((Lf)(x)=f(x)-(f(x+1)+f(x-1))/2\) has the first Fourier character as an
eigenvector. Its eigenvalue is \(1-\cos(2\pi/N)\), positive for \(N\ge2\)
and tending to zero as the cycle length grows. This is the one-magnon
coefficient equation for a periodic chain of singlet projections.
-/

open scoped Topology

namespace ZMod

/-- The cycle Laplacian normalized for a chain of singlet projections. -/
noncomputable def cycleLaplacian {N : ℕ} (f : ZMod N → ℂ) (x : ZMod N) : ℂ :=
  f x - (f (x + 1) + f (x - 1)) / 2

/-- An additive character is an eigenvector of the cycle Laplacian. -/
theorem cycleLaplacian_addChar {N : ℕ} (χ : AddChar (ZMod N) ℂ) (x : ZMod N) :
    cycleLaplacian χ x = (1 - (χ 1 + χ (-1)) / 2) * χ x := by
  simp only [cycleLaplacian, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

/-- The first nonconstant Fourier eigenvalue of the normalized cycle Laplacian. -/
noncomputable def cycleFourierGap (N : ℕ) : ℝ :=
  1 - Real.cos (2 * Real.pi / N)

/-- The mean of the forward and backward Fourier phases is the real cosine. -/
theorem stdAddChar_one_add_neg_one_div_two (N : ℕ) [NeZero N] :
    ((stdAddChar (1 : ZMod N)) + stdAddChar (-1 : ZMod N)) / 2 =
      (Real.cos (2 * Real.pi / N) : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  have hp : stdAddChar (1 : ZMod N) = Complex.exp (2 * Real.pi * Complex.I / N) := by
    simpa using stdAddChar_coe (N := N) 1
  have hm : stdAddChar (-1 : ZMod N) = Complex.exp (-(2 * Real.pi * Complex.I / N)) := by
    simpa only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, neg_div] using
      stdAddChar_coe (N := N) (-1)
  rw [hp, hm]
  push_cast
  congr 2
  all_goals congr 1
  all_goals ring

/-- The first standard Fourier character has eigenvalue
\(1-\cos(2\pi/N)\) for the normalized cycle Laplacian. -/
theorem cycleLaplacian_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    cycleLaplacian stdAddChar x = (cycleFourierGap N : ℂ) * stdAddChar x := by
  rw [cycleLaplacian_addChar, stdAddChar_one_add_neg_one_div_two]
  simp only [cycleFourierGap, Complex.ofReal_sub, Complex.ofReal_one]

/-- The first Fourier eigenvalue is positive for every cycle of length at least two. -/
theorem cycleFourierGap_pos {N : ℕ} (hN : 2 ≤ N) : 0 < cycleFourierGap N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_two hN'
  have hθle : 2 * Real.pi / N ≤ Real.pi :=
    (div_le_iff₀ hNpos).2 (by nlinarith [mul_le_mul_of_nonneg_left hN' Real.pi_pos.le])
  have hθpos : 0 < 2 * Real.pi / N := div_pos Real.two_pi_pos hNpos
  simpa only [cycleFourierGap, Real.cos_zero] using
    sub_pos.mpr (Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) le_rfl hθle hθpos)

/-- The first Fourier eigenvalue tends to zero as the cycle length grows. -/
theorem tendsto_cycleFourierGap_zero :
    Filter.Tendsto cycleFourierGap Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun N : ℕ => 1 - Real.cos (2 * Real.pi / N)) Filter.atTop (nhds 0)
  have hθ : Filter.Tendsto (fun N : ℕ => 2 * Real.pi / (N : ℝ)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.cos_zero, sub_self] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub ((Real.continuous_cos.tendsto 0).comp hθ)

/-- Arbitrarily long cycles have a positive Fourier eigenvalue below any
prescribed positive number. -/
theorem exists_large_cycleFourierGap_pos_lt {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 2 ≤ N ∧ 0 < cycleFourierGap N ∧ cycleFourierGap N < δ := by
  have hlt : ∀ᶠ N in Filter.atTop, cycleFourierGap N < δ :=
    tendsto_cycleFourierGap_zero.eventually (gt_mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hlt
  have htwo : 2 ≤ max (max M 2) N₀ :=
    (le_max_right M 2).trans (le_max_left _ _)
  exact ⟨max (max M 2) N₀, (le_max_left M 2).trans (le_max_left _ _),
    htwo, cycleFourierGap_pos htwo, hN₀ _ (le_max_right _ _)⟩

end ZMod
