/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SpectralRadiusPowerDecay

/-!
# Power bounds at a prescribed rate

Gelfand's formula bounds the powers of an element in a complex Banach algebra at
any prescribed nonnegative rate strictly above its spectral radius. The
multiplicative constant depends on the chosen rate.

## Main results

* `geometric_bound_of_spectralRadius_lt` gives the algebra-norm estimate.
* `geometric_apply_bound_of_spectralRadius_lt` gives the corresponding pointwise
  estimate for continuous linear endomorphisms.
-/

open scoped ENNReal NNReal

namespace TNLean.Spectral

/-- If the spectral radius of an element of a complex Banach algebra is strictly
smaller than a prescribed rate $\lambda$, then its powers satisfy
$\lVert a^n\rVert \le C\lambda^n$ for every $n$. The constant $C>0$ may depend
on the prescribed rate $\lambda$. -/
theorem geometric_bound_of_spectralRadius_lt
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (rate : ℝ≥0) (ha : spectralRadius ℂ a < (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * (rate : ℝ) ^ n := by
  have hrate_pos : 0 < (rate : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt
      (show (0 : ℝ≥0∞) ≤ spectralRadius ℂ a from bot_le) ha)
  have hev : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < rate ^ n := by
    have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
    filter_upwards [gelfand.eventually (eventually_lt_nhds ha),
      Filter.eventually_gt_atTop 0] with n hn hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff (Nat.cast_pos.mpr hn_pos)] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let S : ℝ := Finset.sum (Finset.range N) fun k => ‖a ^ k‖ / (rate : ℝ) ^ k
  let C : ℝ := S + 1
  refine ⟨C, by positivity, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hnorm : ‖a ^ n‖ ≤ (rate : ℝ) ^ n := by
      exact_mod_cast (hN n hn).le
    have hC_ge_one : 1 ≤ C := by
      have hS_nonneg : 0 ≤ S := by
        dsimp [S]
        positivity
      dsimp [C]
      linarith
    calc
      ‖a ^ n‖ ≤ (rate : ℝ) ^ n := hnorm
      _ = 1 * (rate : ℝ) ^ n := by ring
      _ ≤ C * (rate : ℝ) ^ n := by
        gcongr
  · have hn_lt : n < N := Nat.lt_of_not_ge hn
    have hterm : ‖a ^ n‖ / (rate : ℝ) ^ n ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun k => ‖a ^ k‖ / (rate : ℝ) ^ k)
        (by intro k hk; positivity)
        (Finset.mem_range.mpr hn_lt)
    have hterm' : ‖a ^ n‖ ≤ S * (rate : ℝ) ^ n := by
      exact (div_le_iff₀ (pow_pos hrate_pos n)).1 hterm
    have hS_le_C : S ≤ C := by
      dsimp [C]
      linarith
    calc
      ‖a ^ n‖ ≤ S * (rate : ℝ) ^ n := hterm'
      _ ≤ C * (rate : ℝ) ^ n := by
        gcongr

/-- If the spectral radius of a continuous linear endomorphism is strictly
smaller than a prescribed rate $\lambda$, then
$\lVert T^n x\rVert \le C\lambda^n\lVert x\rVert$ for every $n$ and $x$.
The constant $C>0$ may depend on the prescribed rate $\lambda$. -/
theorem geometric_apply_bound_of_spectralRadius_lt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V) (rate : ℝ≥0)
    (hT : spectralRadius ℂ T < (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ x : V, ‖(T ^ n) x‖ ≤ C * (rate : ℝ) ^ n * ‖x‖ := by
  rcases geometric_bound_of_spectralRadius_lt T rate hT with ⟨C, hC, hpow⟩
  exact ⟨C, hC, fun n x => (T ^ n).le_of_opNorm_le (hpow n) x⟩

end TNLean.Spectral
