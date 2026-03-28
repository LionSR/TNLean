/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Overlap.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergence helpers for MPV overlap arguments

General-purpose convergence lemmas used in the fundamental theorem proof chain.
These helpers do not depend on the BNT structure and are extracted from `Full.lean`
for reusability.

## Main results

- `bounded_mul_tendsto_zero`: bounded geometric × tending-to-zero → 0
- `geometric_mul_bounded_tendsto_zero`: geometric(< 1) × bounded → 0
- `geometric_mul_inner_tendsto_zero`: geometric(< 1) × Cauchy-Schwarz-bounded inner → 0
- `sum_tendsto_one_of_diag`: diagonal-dominant sum → 1
- `tendsto_inner_zero`: mpvOverlap → 0 implies mpvInner → 0
- `tendsto_inner_one`: mpvOverlap → 1 (self) implies mpvInner → 1
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-- `mpvOverlap → 0` implies `mpvInner → 0`, via the relation
`mpvOverlap = star ∘ mpvInner`. -/
lemma tendsto_inner_zero {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂)
    (hOv : Tendsto (fun N => mpvOverlap (d := d) X Y N) atTop (nhds 0)) :
    Tendsto (fun N => mpvInner (d := d) X Y N) atTop (nhds 0) := by
  simpa [mpvOverlap_eq_star_mpvInner] using hOv.star

/-- `mpvOverlap X X → 1` (self-overlap) implies `mpvInner X X → 1`, via the relation
`mpvOverlap = star ∘ mpvInner`. -/
lemma tendsto_inner_one {D : ℕ} (X : MPSTensor d D)
    (hOv : Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (nhds 1)) :
    Tendsto (fun N => mpvInner (d := d) X X N) atTop (nhds 1) := by
  simpa [mpvOverlap_eq_star_mpvInner] using hOv.star

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

/-- Geometric factor with `‖c‖ < 1` times a Cauchy-Schwarz-bounded inner product tends to
zero, given that both self-overlaps converge to 1. -/
lemma geometric_mul_inner_tendsto_zero {D₁ D₂ : ℕ} (c : ℂ)
    (X : MPSTensor d D₁) (Y : MPSTensor d D₂) (hc : ‖c‖ < 1)
    (hX : Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (nhds 1))
    (hY : Tendsto (fun N => mpvOverlap (d := d) Y Y N) atTop (nhds 1)) :
    Tendsto (fun N => c ^ N * mpvInner (d := d) X Y N) atTop (nhds 0) := by
  have hX_inner : Tendsto (fun N => mpvInner (d := d) X X N) atTop (nhds 1) :=
    tendsto_inner_one X hX
  have hY_inner : Tendsto (fun N => mpvInner (d := d) Y Y N) atTop (nhds 1) :=
    tendsto_inner_one Y hY
  obtain ⟨C_X, hC_X⟩ :=
    (Metric.isBounded_range_of_tendsto _ hX_inner).exists_norm_le
  obtain ⟨C_Y, hC_Y⟩ :=
    (Metric.isBounded_range_of_tendsto _ hY_inner).exists_norm_le
  have hXX_bdd : ∀ N, ‖mpvInner (d := d) X X N‖ ≤ C_X :=
    fun N => hC_X _ (Set.mem_range_self N)
  have hYY_bdd : ∀ N, ‖mpvInner (d := d) Y Y N‖ ≤ C_Y :=
    fun N => hC_Y _ (Set.mem_range_self N)
  -- ‖mpvState X N‖² = ‖mpvInner X X N‖ via inner_self_eq_norm_sq_to_K.
  have hXX_sq : ∀ N,
      ‖mpvState (d := d) X N‖ ^ 2 = ‖mpvInner (d := d) X X N‖ := fun N => by
    have heq : mpvInner (d := d) X X N = ↑(‖mpvState (d := d) X N‖ ^ 2 : ℝ) := by
      unfold mpvInner
      rw [inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hYY_sq : ∀ N,
      ‖mpvState (d := d) Y N‖ ^ 2 = ‖mpvInner (d := d) Y Y N‖ := fun N => by
    have heq : mpvInner (d := d) Y Y N = ↑(‖mpvState (d := d) Y N‖ ^ 2 : ℝ) := by
      unfold mpvInner
      rw [inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  -- Cauchy-Schwarz + AM-GM gives ‖mpvInner X Y N‖ ≤ (C_X + C_Y) / 2.
  apply geometric_mul_bounded_tendsto_zero c _ ((C_X + C_Y) / 2) hc
  intro N
  have h_cs : ‖mpvInner (d := d) X Y N‖ ≤
      ‖mpvState (d := d) X N‖ * ‖mpvState (d := d) Y N‖ := by
    unfold mpvInner; exact norm_inner_le_norm _ _
  calc ‖mpvInner (d := d) X Y N‖
      ≤ ‖mpvState (d := d) X N‖ * ‖mpvState (d := d) Y N‖ := h_cs
    _ ≤ (‖mpvState (d := d) X N‖ ^ 2 + ‖mpvState (d := d) Y N‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖mpvState (d := d) X N‖ - ‖mpvState (d := d) Y N‖)]
    _ = (‖mpvInner (d := d) X X N‖ + ‖mpvInner (d := d) Y Y N‖) / 2 := by
          rw [hXX_sq N, hYY_sq N]
    _ ≤ (C_X + C_Y) / 2 := by linarith [hXX_bdd N, hYY_bdd N]

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

end MPSTensor
