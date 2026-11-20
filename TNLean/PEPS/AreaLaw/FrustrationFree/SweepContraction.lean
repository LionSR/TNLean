/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DetectabilityLemma

/-!
# Contraction of one sweep of local filters

Let `h_0, …, h_{m-1}` be orthogonal projections on a complete inner product space, each failing
to commute with at most `d` of the others, and let `Ω` be a vector annihilated by all of them.
Suppose that `∑ h_k ≥ γ` on the orthogonal complement of `Ω`. The sweep
`D = (1 - h_{m-1}) ⋯ (1 - h_0)` fixes `Ω`, maps the complement of `Ω` to itself, and contracts
it by the factor

`θ = (1 + γ / (d + 1)²)^{-1/2}`,

so that `‖D^t v‖ ≤ θ^t ‖v‖` for every `v ⟂ Ω`. This is `eq:sweep` of the frustration-free
area-law note, where the bound is derived for the factors `(1 - k_i)^{1/2}` of positive
contractions `k_i`. Here it is derived for projections, the case the note reduces to through the
range projections of the terms, from QICLean's detectability lemma
`ContinuousLinearMap.re_inner_sum_complementProd_le`.

**Scope restriction (projections):** the note states `eq:sweep` for positive contractions `k_i`
and factors `(1 - k_i)^{1/2}`; this module proves it for projections only. The amplification step
applies it to the range projections of the terms, which satisfy every property of the filters the
note uses. Documented in `docs/paper-gaps/frustrationfree_sweep_range_projections.tex`.

## Main statements

* `ContinuousLinearMap.complementProd_apply_of_forall_apply_eq_zero`: the sweep fixes `Ω`.
* `ContinuousLinearMap.inner_complementProd_of_forall_apply_eq_zero`: the sweep preserves the
  overlap with `Ω`.
* `ContinuousLinearMap.norm_sq_complementProd_le_of_gap`: one sweep,
  `((d + 1)² + γ) ‖D v‖² ≤ (d + 1)² ‖v‖²` for `v ⟂ Ω`.
* `ContinuousLinearMap.norm_pow_complementProd_le_of_gap`: `‖D^t v‖ ≤ θ^t ‖v‖` for `v ⟂ Ω`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  paragraph "Contraction in one sweep", `eq:sweep`.
* A. Anshu, I. Arad and T. Vidick, *Simple proof of the detectability lemma and spectral gap
  amplification*, Phys. Rev. B 93, 205142 (2016).
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {h : ℕ → E →L[𝕜] E} {Ω : E}

omit [CompleteSpace E] in
/-- A sweep fixes every vector annihilated by its projections. -/
theorem complementProd_apply_of_forall_apply_eq_zero (hΩ : ∀ k, h k Ω = 0) (n : ℕ) :
    complementProd h n Ω = Ω := by
  induction n with
  | zero => rfl
  | succ n ih => rw [complementProd_succ_apply, ih, hΩ, sub_zero]

/-- A sweep of projections annihilating `Ω` preserves the overlap with `Ω`. -/
theorem inner_complementProd_of_forall_apply_eq_zero (hh : ∀ k, IsStarProjection (h k))
    (hΩ : ∀ k, h k Ω = 0) (v : E) (n : ℕ) :
    ⟪Ω, complementProd h n v⟫_𝕜 = ⟪Ω, v⟫_𝕜 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [complementProd_succ_apply, inner_sub_right, ← IsStarProjection.inner_apply_left (hh n),
      hΩ, inner_zero_left, sub_zero, ih]

open scoped Classical in
/-- **One sweep contracts the complement of the ground vector** (`eq:sweep` of the
frustration-free area-law note, for projections). Let `h_0, …, h_{m-1}` be projections annihilating
`Ω`, each failing to commute with at most `d` of the others, with `γ ‖v‖² ≤ ⟨v, ∑ h_k v⟩` for
every `v ⟂ Ω`. Then `((d + 1)² + γ) ‖D v‖² ≤ (d + 1)² ‖v‖²` for every `v ⟂ Ω`, where
`D = (1 - h_{m-1}) ⋯ (1 - h_0)`. Source: `docs/audits/2026-11-18_finite_range_frustration_free_
area_law.tex`, paragraph "Contraction in one sweep". -/
theorem norm_sq_complementProd_le_of_gap (hh : ∀ k, IsStarProjection (h k))
    (hΩ : ∀ k, h k Ω = 0) {m d : ℕ}
    (hd : ∀ i < m, ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h i) (h j))).card ≤ d)
    {γ : ℝ} (hgap : ∀ v : E, ⟪Ω, v⟫_𝕜 = 0 →
      γ * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, (∑ i ∈ Finset.range m, h i) v⟫_𝕜)
    {v : E} (hv : ⟪Ω, v⟫_𝕜 = 0) :
    (((d : ℝ) + 1) ^ 2 + γ) * ‖complementProd h m v‖ ^ 2 ≤ ((d : ℝ) + 1) ^ 2 * ‖v‖ ^ 2 := by
  have hDL := re_inner_sum_complementProd_le hh hd v
  have hlow := hgap _ ((inner_complementProd_of_forall_apply_eq_zero hh hΩ v m).trans hv)
  have hmass : ‖complementProd h m v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    have := sum_norm_sq_apply_complementProd hh v m
    have : 0 ≤ ∑ k ∈ Finset.range m, ‖h k (complementProd h k v)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  have hd0 : (0 : ℝ) ≤ 2 * d + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmass hd0]

open scoped Classical in
/-- **Repeated sweeps contract geometrically** (`eq:sweep` of the frustration-free area-law
note). Under the hypotheses of `norm_sq_complementProd_le_of_gap` with `0 ≤ γ`, every `v ⟂ Ω`
satisfies `‖D^t v‖ ≤ θ^t ‖v‖` with `θ = (1 + γ / (d + 1)²)^{-1/2}`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, `eq:sweep`. -/
theorem norm_pow_complementProd_le_of_gap (hh : ∀ k, IsStarProjection (h k))
    (hΩ : ∀ k, h k Ω = 0) {m d : ℕ}
    (hd : ∀ i < m, ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h i) (h j))).card ≤ d)
    {γ : ℝ} (hγ : 0 ≤ γ) (hgap : ∀ v : E, ⟪Ω, v⟫_𝕜 = 0 →
      γ * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, (∑ i ∈ Finset.range m, h i) v⟫_𝕜)
    (t : ℕ) {v : E} (hv : ⟪Ω, v⟫_𝕜 = 0) :
    ‖(complementProd h m ^ t) v‖ ≤ (√(1 + γ / ((d : ℝ) + 1) ^ 2))⁻¹ ^ t * ‖v‖ := by
  set D := complementProd h m
  set θ := (√(1 + γ / ((d : ℝ) + 1) ^ 2))⁻¹ with hθ
  have hd1 : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 := by positivity
  have hs : (0 : ℝ) < √(1 + γ / ((d : ℝ) + 1) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hθ0 : 0 ≤ θ := inv_nonneg.mpr hs.le
  have hone : ∀ w : E, ⟪Ω, w⟫_𝕜 = 0 → ‖D w‖ ≤ θ * ‖w‖ := by
    intro w hw
    have key := norm_sq_complementProd_le_of_gap hh hΩ hd hgap hw
    have hsq : (√(1 + γ / ((d : ℝ) + 1) ^ 2)) ^ 2 = 1 + γ / ((d : ℝ) + 1) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have h2 : (√(1 + γ / ((d : ℝ) + 1) ^ 2) * ‖D w‖) ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [mul_pow, hsq]
      have : (1 + γ / ((d : ℝ) + 1) ^ 2) * ‖D w‖ ^ 2 =
          ((((d : ℝ) + 1) ^ 2 + γ) * ‖D w‖ ^ 2) / ((d : ℝ) + 1) ^ 2 := by
        field_simp
      rw [this, div_le_iff₀ hd1]
      linarith
    have h3 : √(1 + γ / ((d : ℝ) + 1) ^ 2) * ‖D w‖ ≤ ‖w‖ :=
      (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg w) two_ne_zero).mp h2
    rw [hθ, inv_mul_eq_div, le_div_iff₀ hs, mul_comm]
    exact h3
  have horth : ∀ n : ℕ, ⟪Ω, (D ^ n) v⟫_𝕜 = 0 := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, inner_complementProd_of_forall_apply_eq_zero hh hΩ, ih]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_assoc]
    exact (hone _ (horth t)).trans (mul_le_mul_of_nonneg_left ih hθ0)

end ContinuousLinearMap
