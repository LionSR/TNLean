/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Polynomially weighted dyadic decay

The geometric decay of the sparse-belt count absorbs every fixed power of the
layer index. The resulting numerical series is summable, and all of its finite
subsums have one positive bound chosen independently of the domain and cut.

These are auxiliary analytic ingredients of the exceptional-site count in
Section 11. They do not construct repairs or bound the number of descendants
of an actual mark.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:total-repairs`, lines 668–692;
  polynomial absorption is also used in lines 232–235.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter Topology

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every fixed real power of the layer index is eventually absorbed into half
of the fixed geometric decay exponent.
Source: Section 11, `geometry:total-repairs`, lines 668–692, and lines 232–235. -/
theorem exists_polynomial_dyadic_absorption (p : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ((k : ℝ) + 1) ^ p *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) ≤
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 4) := by
  let a : ℝ := (Exponents.geometryDelta : ℝ) * Real.log 2 / 4
  have ha : 0 < a := by
    have hδ : 0 < (Exponents.geometryDelta : ℝ) := by norm_num [Exponents.geometryDelta]
    exact div_pos (mul_pos hδ (Real.log_pos (by norm_num))) (by norm_num)
  have hshift : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun k : ℕ => ((k : ℝ) + 1) ^ p * Real.exp (-a * (k : ℝ)))
      atTop (𝓝 0) := by
    convert ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha).comp
      hshift).mul_const (Real.exp a) using 1
    · funext k
      simp only [Function.comp_apply]
      rw [mul_assoc, ← Real.exp_add,
        show -a * ((k : ℝ) + 1) + a = -a * (k : ℝ) by ring]
    · simp
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨K, fun k hk => ?_⟩
  have h := mul_le_mul_of_nonneg_right (hK k hk).le
    (Real.exp_nonneg (-a * (k : ℝ)))
  rw [Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num),
    Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num)]
  convert h using 1
  · rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    dsimp [a]
    ring
  · simp only [one_mul]
    congr 1
    dsimp [a]
    ring

/-- The polynomially weighted sparse-belt decay is summable over natural scales.
Source: Section 11, `geometry:total-repairs`, lines 668–692. -/
theorem summable_polynomial_dyadic_decay (p : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ p *
      (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) := by
  let q : ℝ := (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) / 4)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    norm_num [Exponents.geometryDelta]
  apply (summable_geometric_of_norm_lt_one hq).of_norm_bounded_eventually_nat
  obtain ⟨K, hK⟩ := exists_polynomial_dyadic_absorption p
  filter_upwards [Filter.eventually_ge_atTop K] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _))]
  have heq : q ^ k = (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [heq]
  exact hK k hk

/-- Every finite collection of scales has one strictly positive numerical budget.
The bound depends only on the real exponent and the fixed geometric constants.
Source: Section 11, `geometry:total-repairs`, lines 668–692. -/
theorem exists_uniform_polynomial_dyadic_sum_bound (p : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ F : Finset ℕ,
      ∑ k ∈ F, ((k : ℝ) + 1) ^ p *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) ≤ B := by
  let w : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ p *
    (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)
  have hw : ∀ k, 0 ≤ w k := fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨1 + ∑' k, w k, ?_, fun F => ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg hw)
  · have hsum := (summable_polynomial_dyadic_decay p).sum_le_tsum F (fun k _ => hw k)
    exact hsum.trans (by linarith)

end TNLean.PEPS.AreaLaw.Geometry
