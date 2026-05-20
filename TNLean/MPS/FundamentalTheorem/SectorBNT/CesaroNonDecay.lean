/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Fintype.BigOperators

/-!
# Cesàro non-decay for finite power sums on the closed unit disk

This module proves the pure-analytic lemma underlying the sector-coefficient
non-decay input used when the CPSV16 §II.C proof projects onto a matched BNT
block.  The lemma is independent of MPS data and is stated in terms of complex
numbers only.

## Main result

* `MPSTensor.CesaroNonDecay.sum_pow_not_tendsto_zero_of_unit_modulus`:
  for a finite family `μ : Fin r → ℂ` with `‖μ q‖ ≤ 1` for every `q` and
  some `q*` with `‖μ q*‖ = 1`, the sequence
  `N ↦ ∑ q, (μ q)^N` does not tend to `0` as `N → ∞`.

## Proof outline

The proof uses the elementary **Cesàro mean** identity.  Let
`c(N) := ∑_q (μ q)^N`.  If `c(N) → 0`, then
`|c(N)|² = c(N) · conj(c(N)) → 0`, and by `Filter.Tendsto.cesaro_smul`
the Cesàro mean of `|c|²` also tends to `0`.

Expanding the product gives
`|c(N)|² = ∑_{p,q} (μ_p · conj(μ_q))^N`, so the Cesàro mean is the
finite sum (over pairs) of Cesàro means of geometric sequences
`(μ_p · conj(μ_q))^N`.  Each such geometric Cesàro mean tends to:

* `1` when `μ_p · conj(μ_q) = 1`, since `1^N = 1` and the average of `T`
  ones over `T` is `1`;
* `0` when `μ_p · conj(μ_q) ≠ 1`, since the partial sum is bounded by
  `2 / ‖μ_p · conj(μ_q) - 1‖` (from the geometric-sum formula together
  with `‖z^N - 1‖ ≤ ‖z‖^N + 1 ≤ 2`), divided by `T → ∞`.

Therefore the Cesàro mean tends to the cardinality of
`{(p, q) : μ_p · conj(μ_q) = 1}`.  The diagonal pair `(q*, q*)`
contributes (since `μ_{q*} · conj(μ_{q*}) = ‖μ_{q*}‖² = 1`), so the
limit is `≥ 1 > 0`, contradicting the previous limit `0`.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, *Matrix Product Density
  Operators*, arXiv:1606.00608.  Line 246 gives the `|μ_k| ≤ 1` and
  `∃ k, |μ_k| = 1` normalization convention; line 1182 is the BNT
  projection step where a nonzero sector coefficient is needed.
* Cesàro mean limit: `Filter.Tendsto.cesaro_smul` in
  `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`.
-/

open scoped BigOperators
open Filter Topology

namespace MPSTensor
namespace CesaroNonDecay

/-- **Cesàro mean of a geometric sequence on the closed unit disk.**

For `z : ℂ` with `‖z‖ ≤ 1`, the average `(T)⁻¹ · ∑_{N < T} z^N` tends to:

* `1` if `z = 1` (each term is `1`);
* `0` if `z ≠ 1` (the partial sum is bounded by `2 / ‖z - 1‖`, divided
  by `T → ∞`).

Paper context: this is the analytic workhorse behind the line-246
normalization when it is used in the CPSV16 §II.C line-1182 projection
argument.  The unit case captures the contribution of pairs with
`μ_p · conj(μ_q) = 1`; the non-unit case shows all other pairs contribute
`0`. -/
lemma tendsto_cesaro_geom (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, z ^ N)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  classical
  by_cases hz1 : z = 1
  · subst hz1
    rw [if_pos rfl]
    -- Eventually (T ≥ 1), `(T)⁻¹ * T = 1`.
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTne : (T : ℂ) ≠ 0 := by
      have hTge : (1 : ℕ) ≤ T := hT
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hTge
    simp [one_pow, Finset.sum_const, Finset.card_range, inv_mul_cancel₀ hTne]
  · rw [if_neg hz1]
    -- Squeeze argument: `‖(T)⁻¹ * ∑ z^N‖ ≤ 2 / (T * ‖z - 1‖)` and the
    -- bound tends to `0`.
    have hzm1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hC_pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hzm1
    refine squeeze_zero_norm (a := fun T : ℕ => 2 / ((T : ℝ) * ‖z - 1‖)) ?_ ?_
    · intro T
      rw [geom_sum_eq hz1]
      by_cases hT0 : T = 0
      · subst hT0
        simp
      have hT_pos : (0 : ℝ) < (T : ℝ) := by
        have hTge : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT0
        exact_mod_cast hTge
      have hbnd : ‖z ^ T - 1‖ ≤ 2 := by
        calc ‖z ^ T - 1‖
            ≤ ‖z ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = ‖z‖ ^ T + 1 := by rw [norm_pow]; simp
          _ ≤ 1 + 1 := by
              have h1 : ‖z‖ ^ T ≤ 1 ^ T :=
                pow_le_pow_left₀ (norm_nonneg _) hz T
              simpa using h1
          _ = 2 := by norm_num
      rw [norm_mul, norm_inv, Complex.norm_natCast, norm_div]
      have hineq : (T : ℝ)⁻¹ * (‖z ^ T - 1‖ / ‖z - 1‖)
          ≤ (T : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hT_pos))
        exact div_le_div_of_nonneg_right hbnd (le_of_lt hC_pos)
      have heq : (2 : ℝ) / ((T : ℝ) * ‖z - 1‖)
          = (T : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
        field_simp
      change (T : ℝ)⁻¹ * (‖z ^ T - 1‖ / ‖z - 1‖) ≤ 2 / ((T : ℝ) * ‖z - 1‖)
      rw [heq]
      exact hineq
    · -- `T ↦ 2 / (T * ‖z - 1‖) = (2 / ‖z - 1‖) / T → 0`.
      have hcast : Tendsto (fun T : ℕ => (T : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have h0 := hcast.const_div_atTop (2 / ‖z - 1‖)
      refine h0.congr ?_
      intro T
      by_cases hT0 : T = 0
      · subst hT0
        simp
      · have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT0
        field_simp

/-- **Cesàro non-decay of a sum of `N`-th powers under the closed-unit-disk
normalization.**

Let `μ : Fin r → ℂ` satisfy `‖μ q‖ ≤ 1` for every `q` and let some
`q*` satisfy `‖μ q*‖ = 1`.  Then the sequence
`N ↦ ∑ q, (μ q)^N` does not tend to `0`.

This is the analytic lemma underlying the CPSV16 §II.A line-246
"`|μ_k| ≤ 1` and `∃ k, |μ_k| = 1`" normalization convention when that
normalization is read sector-by-sector in the CPSV16 §II.C line-1182
projection argument.

The proof is the elementary Cesàro-mean argument outlined in the module
docstring. -/
theorem sum_pow_not_tendsto_zero_of_unit_modulus
    {r : ℕ} (μ : Fin r → ℂ)
    (h_le : ∀ q, ‖μ q‖ ≤ 1)
    (h_unit : ∃ q, ‖μ q‖ = 1) :
    ¬ Tendsto (fun N : ℕ => ∑ q : Fin r, (μ q) ^ N) atTop (𝓝 0) := by
  classical
  intro hzero
  obtain ⟨q_star, hq_star⟩ := h_unit
  -- Let `c(N) = ∑ q, (μ q)^N`.  Its conjugate sequence also tends to `0`.
  set c : ℕ → ℂ := fun N => ∑ q : Fin r, (μ q) ^ N with hc_def
  have hconj_zero : Tendsto (fun N => (starRingEnd ℂ) (c N)) atTop (𝓝 0) := by
    have hcont : Continuous (starRingEnd ℂ) := Complex.continuous_conj
    have htend : Tendsto (starRingEnd ℂ) (𝓝 0) (𝓝 ((starRingEnd ℂ) 0)) :=
      hcont.tendsto 0
    have hcomp := htend.comp hzero
    simpa using hcomp
  -- `f N := c(N) · conj(c(N)) → 0 · 0 = 0`.
  have hf_zero :
      Tendsto (fun N : ℕ => c N * (starRingEnd ℂ) (c N)) atTop (𝓝 0) := by
    have h := hzero.mul hconj_zero
    simpa using h
  -- Cesàro mean (real-scalar form) of `f` also tends to `0`.
  have hCes_zero :
      Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ N ∈ Finset.range T, c N * (starRingEnd ℂ) (c N))
        atTop (𝓝 0) := hf_zero.cesaro_smul
  -- Convert the real-scalar Cesàro to multiplication by the complex inverse.
  have hCes_mul :
      Tendsto (fun T : ℕ =>
        (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, c N * (starRingEnd ℂ) (c N))
        atTop (𝓝 0) := by
    refine hCes_zero.congr ?_
    intro T
    rw [Complex.real_smul]
    congr 1
    push_cast
    rfl
  -- Re-express the Cesàro mean as a finite sum over pairs `(p, q)`.
  -- `c(N) · conj(c(N)) = ∑_{p, q} (μ p · conj (μ q))^N`.
  have hf_eq : ∀ N,
      c N * (starRingEnd ℂ) (c N)
        = ∑ pq : Fin r × Fin r, (μ pq.1 * (starRingEnd ℂ) (μ pq.2)) ^ N := by
    intro N
    have hconj_c : (starRingEnd ℂ) (c N)
        = ∑ q : Fin r, ((starRingEnd ℂ) (μ q)) ^ N := by
      simp [hc_def, map_sum, map_pow]
    rw [hc_def, hconj_c]
    rw [Finset.sum_mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [mul_pow]
  -- For each pair, compute the Cesàro limit using `tendsto_cesaro_geom`.
  -- Bound on `μ p · conj(μ q)`.
  have h_norm_pair : ∀ pq : Fin r × Fin r,
      ‖μ pq.1 * (starRingEnd ℂ) (μ pq.2)‖ ≤ 1 := by
    intro pq
    rw [norm_mul, Complex.norm_conj]
    have h1 := h_le pq.1
    have h2 := h_le pq.2
    have hnn : (0 : ℝ) ≤ ‖μ pq.2‖ := norm_nonneg _
    calc ‖μ pq.1‖ * ‖μ pq.2‖
        ≤ 1 * ‖μ pq.2‖ :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ ≤ 1 * 1 :=
          mul_le_mul_of_nonneg_left h2 zero_le_one
      _ = 1 := by ring
  -- The diagonal pair `(q_star, q_star)` has `μ_{q_star} · conj(μ_{q_star}) = 1`.
  have h_diag_eq_one :
      μ q_star * (starRingEnd ℂ) (μ q_star) = 1 := by
    have := Complex.mul_conj' (μ q_star)
    rw [hq_star] at this
    -- `this : μ q_star * conj (μ q_star) = ↑(1 : ℝ) ^ 2`
    simpa using this
  -- Per-pair Cesàro sequence.
  set g : (Fin r × Fin r) → ℕ → ℂ := fun pq T =>
    (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, (μ pq.1 * (starRingEnd ℂ) (μ pq.2)) ^ N
    with hg_def
  have hg_tendsto : ∀ pq : Fin r × Fin r,
      Tendsto (g pq) atTop
        (𝓝 (if μ pq.1 * (starRingEnd ℂ) (μ pq.2) = 1 then (1 : ℂ) else 0)) :=
    fun pq => tendsto_cesaro_geom _ (h_norm_pair pq)
  -- Finite sum of tendstos.
  have h_sum_tendsto :
      Tendsto (fun T : ℕ => ∑ pq : Fin r × Fin r, g pq T) atTop
        (𝓝 (∑ pq : Fin r × Fin r,
          (if μ pq.1 * (starRingEnd ℂ) (μ pq.2) = 1 then (1 : ℂ) else 0))) :=
    tendsto_finset_sum (Finset.univ : Finset (Fin r × Fin r))
      (fun pq _ => hg_tendsto pq)
  -- Identify this sum with the Cesàro of `f`.
  have h_cesaro_eq : ∀ T : ℕ,
      (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, c N * (starRingEnd ℂ) (c N)
        = ∑ pq : Fin r × Fin r, g pq T := by
    intro T
    have hcongr :
        ∑ N ∈ Finset.range T, c N * (starRingEnd ℂ) (c N)
          = ∑ N ∈ Finset.range T,
              ∑ pq : Fin r × Fin r,
                (μ pq.1 * (starRingEnd ℂ) (μ pq.2)) ^ N :=
      Finset.sum_congr rfl (fun N _ => hf_eq N)
    rw [hcongr, Finset.sum_comm, Finset.mul_sum]
  -- The Cesàro of `f` equals the per-pair sum, so it converges to the same
  -- limit.
  have hCes_zero' :
      Tendsto (fun T : ℕ => ∑ pq : Fin r × Fin r, g pq T) atTop (𝓝 0) := by
    refine hCes_mul.congr ?_
    intro T
    exact h_cesaro_eq T
  -- Uniqueness of limits forces the per-pair sum's limit to equal `0`.
  have h_limit_eq : (∑ pq : Fin r × Fin r,
      (if μ pq.1 * (starRingEnd ℂ) (μ pq.2) = 1 then (1 : ℂ) else 0))
        = 0 := tendsto_nhds_unique h_sum_tendsto hCes_zero'
  -- But the sum is positive: the diagonal `(q_star, q_star)` contributes `1`.
  set S : Finset (Fin r × Fin r) :=
    (Finset.univ : Finset (Fin r × Fin r)).filter
      fun pq => μ pq.1 * (starRingEnd ℂ) (μ pq.2) = 1 with hS_def
  have h_sum_eq : (∑ pq : Fin r × Fin r,
      (if μ pq.1 * (starRingEnd ℂ) (μ pq.2) = 1 then (1 : ℂ) else 0))
        = (S.card : ℂ) := by
    rw [hS_def, ← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hmem : (q_star, q_star) ∈ S := by
    rw [hS_def]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact h_diag_eq_one
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨_, hmem⟩
  rw [h_sum_eq] at h_limit_eq
  have hScast : (S.card : ℕ) = 0 := by exact_mod_cast h_limit_eq
  exact (Nat.pos_iff_ne_zero.mp hSpos) hScast

end CesaroNonDecay
end MPSTensor
