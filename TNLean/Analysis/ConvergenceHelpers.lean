/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Convergence lemmas for complex sequences

Convergence lemmas for complex sequences, geometric series, and weighted sums.
These are used in the fundamental theorem proof chain but are fully general.

## Main results

- `bounded_mul_tendsto_zero`: bounded geometric × tending-to-zero → 0
- `geometric_mul_bounded_tendsto_zero`: geometric(< 1) × bounded → 0
- `sum_tendsto_one_of_diag`: diagonal-dominant weighted sum → 1
-/

open scoped BigOperators
open Filter

/-- If `‖c‖ ≤ 1` and `f N → 0`, then `c ^ N * f N → 0`. -/
lemma bounded_mul_tendsto_zero
    (c : ℂ) (f : ℕ → ℂ) (hc : ‖c‖ ≤ 1)
    (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun N => c ^ N * f N) atTop (nhds 0) := by
  have hfn : Tendsto (fun N => ‖f N‖) atTop (nhds 0) := by
    convert hf.norm using 1; simp only [norm_zero]
  apply squeeze_zero_norm (fun N => ?_) hfn
  calc ‖c ^ N * f N‖ = ‖c ^ N‖ * ‖f N‖ := norm_mul _ _
    _ = ‖c‖ ^ N * ‖f N‖ := by rw [norm_pow]
    _ ≤ 1 * ‖f N‖ := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (norm_nonneg _) hc) (norm_nonneg _)
    _ = ‖f N‖ := one_mul _

/-- If `‖c‖ < 1` and `‖f N‖ ≤ C` for all `N`, then `c ^ N * f N → 0`. -/
lemma geometric_mul_bounded_tendsto_zero
    (c : ℂ) (f : ℕ → ℂ) (C : ℝ) (hc : ‖c‖ < 1)
    (hbound : ∀ N, ‖f N‖ ≤ C) :
    Tendsto (fun N => c ^ N * f N) atTop (nhds 0) := by
  have hgeom : Tendsto (fun N => ‖c‖ ^ N * C) atTop (nhds 0) := by
    have h1 : Tendsto (fun N => (‖c‖ : ℝ) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rwa [Real.norm_of_nonneg (norm_nonneg c)])
    have h2 := h1.mul_const C
    simpa only [zero_mul] using h2
  apply squeeze_zero_norm (fun N => ?_) hgeom
  calc ‖c ^ N * f N‖ = ‖c ^ N‖ * ‖f N‖ := norm_mul _ _
    _ ≤ ‖c ^ N‖ * C := mul_le_mul_of_nonneg_left (hbound N) (norm_nonneg _)
    _ = ‖c‖ ^ N * C := by rw [norm_pow]

/-- In a weighted sum `∑ j, (μ j / μ₀) ^ N * g j N` where the `j₀`-th term has ratio 1 and
`g j₀ N → 1`, while all other ratios have norm `< 1` and their `g j N → 0`, the whole
sum → 1. -/
lemma sum_tendsto_one_of_diag
    {r : ℕ} {μ : Fin r → ℂ} {μ0 : ℂ} (hμ0 : μ0 ≠ 0)
    {j0 : Fin r} {g : Fin r → ℕ → ℂ}
    (hμj0 : μ j0 = μ0)
    (hdiag : Tendsto (g j0) atTop (nhds 1))
    (hratio : ∀ j, j ≠ j0 → ‖μ j / μ0‖ < 1)
    (hcross : ∀ j, j ≠ j0 → Tendsto (g j) atTop (nhds 0)) :
    Tendsto (fun N => ∑ j : Fin r, (μ j / μ0) ^ N * g j N) atTop (nhds 1) := by
  have hsplit : ∀ N, ∑ j, (μ j / μ0) ^ N * g j N =
      (μ j0 / μ0) ^ N * g j0 N +
      ∑ j ∈ Finset.univ.erase j0, (μ j / μ0) ^ N * g j N := by
    intro N; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
  simp_rw [hsplit]
  have h1 : Tendsto (fun N => (μ j0 / μ0) ^ N * g j0 N) atTop (nhds 1) := by
    simp only [hμj0, div_self hμ0, one_pow, one_mul]; exact hdiag
  have h2 : Tendsto (fun N => ∑ j ∈ Finset.univ.erase j0,
      (μ j / μ0) ^ N * g j N) atTop (nhds (0 : ℂ)) := by
    have := tendsto_finset_sum (Finset.univ.erase j0)
      (fun (j : Fin r) (hj : j ∈ Finset.univ.erase j0) =>
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
          (hratio j (Finset.ne_of_mem_erase hj))).mul
        (hcross j (Finset.ne_of_mem_erase hj)))
    simpa using this
  convert h1.add h2 using 1; simp only [add_zero]

/-- A finite sum of uniformly bounded coefficients times terms converging to
zero also converges to zero. -/
lemma tendsto_finset_sum_mul_zero_of_norm_le_one
    {ι : Type*} [Fintype ι]
    (coeff : ℕ → ι → ℂ)
    (f : ι → ℕ → ℂ)
    (hcoeff : ∀ N i, ‖coeff N i‖ ≤ 1)
    (hf : ∀ i, Tendsto (f i) atTop (nhds 0)) :
    Tendsto (fun N => ∑ i : ι, coeff N i * f i N) atTop (nhds 0) := by
  have hterm : ∀ i : ι,
      Tendsto (fun N => coeff N i * f i N) atTop (nhds 0) := by
    intro i
    have hnorm : Tendsto (fun N => ‖f i N‖) atTop (nhds (0 : ℝ)) := by
      simpa only [norm_zero] using (hf i).norm
    apply squeeze_zero_norm (fun N => ?_) hnorm
    calc
      ‖coeff N i * f i N‖ = ‖coeff N i‖ * ‖f i N‖ := norm_mul _ _
      _ ≤ 1 * ‖f i N‖ :=
        mul_le_mul_of_nonneg_right (hcoeff N i) (norm_nonneg _)
      _ = ‖f i N‖ := one_mul _
  simpa using
    tendsto_finset_sum (Finset.univ : Finset ι)
      (fun i _ => hterm i)
