/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Power-sum non-decay for unit-modulus complex families

This module proves a purely analytic fact about finite power sums of
unit-modulus complex numbers: the sequence

  `N ↦ ∑_q (μ q) ^ N`

does **not** tend to zero as `N → ∞`, provided the family `μ : Fin r → ℂ`
is nonempty and every `μ q` has modulus one.  The argument is the standard
Wiener / Cesaro one:

* `‖S N‖² = ∑_{q, q'} (μ q · star (μ q'))^N`.
* Cesaro-averaging in `N` produces, for each pair `(q, q')`,
  either `1` (when the unit-modulus ratio `μ q · star (μ q')` equals `1`)
  or `0` (when the unit-modulus ratio differs from `1`, the geometric
  sum is bounded uniformly in `T`).
* The Cesaro limit therefore equals the cardinality of the resonant set
  `{(q, q') | μ q · star (μ q') = 1}`, which contains the diagonal
  `{(q, q)}` and is therefore `≥ r > 0`; the assumption that the original
  sequence tends to zero would force the Cesaro mean to vanish, a
  contradiction.

This is the analytic ingredient used to discharge the load-bearing
`hNoCancel` hypothesis in the per-block projection argument of
arXiv:1606.00608, Theorem `thm1` (lines 1170--1192).  The MPS-side
discharge lives in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean`.

The module is purely about complex power sums; it has no MPS
dependencies and uses no `sorry`/`axiom`/`unsafe`.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608
  (2017), Theorem `thm1`, lines 1170--1192 (the unit-modulus power-sum
  non-decay used inside the per-block projection step).
-/

open scoped BigOperators
open Filter

namespace UnitModulusPowerSum

/-- For unit-modulus `ν ≠ 1`, the partial sums `∑_{N < T} ν^N` are uniformly
bounded in `T` by `2 / ‖ν - 1‖`. -/
lemma norm_geom_sum_le {ν : ℂ} (hν : ‖ν‖ = 1) (hne : ν ≠ 1) (T : ℕ) :
    ‖∑ N ∈ Finset.range T, ν ^ N‖ ≤ 2 / ‖ν - 1‖ := by
  classical
  have hsub : ν - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [geom_sum_eq hne T, norm_div]
  have hnum : ‖ν ^ T - 1‖ ≤ 2 := by
    calc ‖ν ^ T - 1‖
        ≤ ‖ν ^ T‖ + ‖(1 : ℂ)‖ := by
          have := norm_sub_le (ν ^ T) (1 : ℂ)
          simpa using this
      _ = 2 := by
          rw [norm_pow, hν, one_pow, norm_one]
          norm_num
  have hden_pos : 0 < ‖ν - 1‖ := norm_pos_iff.mpr hsub
  exact div_le_div_of_nonneg_right hnum hden_pos.le

/-- Cesaro average of unit-modulus powers vanishes when the base is not `1`. -/
lemma cesaro_geom_sum_tendsto_zero {ν : ℂ} (hν : ‖ν‖ = 1) (hne : ν ≠ 1) :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, ν ^ N)
      atTop (nhds 0) := by
  classical
  refine (tendsto_zero_iff_norm_tendsto_zero).mpr ?_
  have hbound : ∀ T : ℕ,
      ‖(T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, ν ^ N‖ ≤ (2 / ‖ν - 1‖) * (T : ℝ)⁻¹ := by
    intro T
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp
    · rw [norm_mul]
      have h1 : ‖(T : ℂ)⁻¹‖ = (T : ℝ)⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      rw [h1]
      have h2 := norm_geom_sum_le hν hne T
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
      calc (T : ℝ)⁻¹ * ‖∑ N ∈ Finset.range T, ν ^ N‖
          ≤ (T : ℝ)⁻¹ * (2 / ‖ν - 1‖) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hTpos.le)
        _ = (2 / ‖ν - 1‖) * (T : ℝ)⁻¹ := by ring
  -- The RHS tends to zero.
  have hRHS : Tendsto (fun T : ℕ => (2 / ‖ν - 1‖) * (T : ℝ)⁻¹)
      atTop (nhds 0) := by
    have hT : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (nhds 0) := by
      have hAtTop : Tendsto (fun T : ℕ => ((T : ℝ))) atTop atTop := by
        exact_mod_cast tendsto_natCast_atTop_atTop (R := ℝ)
      have := Filter.Tendsto.inv_tendsto_atTop hAtTop
      simpa [Function.comp] using this
    have := hT.const_mul (2 / ‖ν - 1‖)
    simpa using this
  refine squeeze_zero (fun T => norm_nonneg _) hbound hRHS

/-- Cesaro average of unit-modulus powers at the base `1` equals `1`. -/
lemma cesaro_geom_sum_one_tendsto_one :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ _N ∈ Finset.range T, (1 : ℂ) ^ _N)
      atTop (nhds 1) := by
  classical
  -- Show the sequence is eventually equal to 1 (for T ≥ 1).
  refine tendsto_const_nhds.congr' ?_
  refine (Filter.eventually_ge_atTop 1).mono ?_
  intro T hT
  have hTne : (T : ℂ) ≠ 0 := by
    have hT' : 0 < T := hT
    exact_mod_cast hT'.ne'
  simp [Finset.sum_const, Finset.card_range]
  field_simp

/-- **Power-sum of a finite, nonempty unit-modulus family does not tend
to zero.**

For `μ : Fin r → ℂ` with `r > 0` and `‖μ q‖ = 1` for every `q`, the
sequence `N ↦ ∑_q (μ q) ^ N` does not tend to `0` as `N → ∞`.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192 (the
unit-modulus power-sum non-decay used inside the per-block projection
step).  Proof via Cesaro averaging of `‖S N‖²` in `ℂ`. -/
theorem unitModulus_power_sum_not_tendsto_zero
    {r : ℕ} (hr : 0 < r) (μ : Fin r → ℂ) (hμ : ∀ q, ‖μ q‖ = 1) :
    ¬ Tendsto (fun N : ℕ => ∑ q : Fin r, (μ q) ^ N) atTop (nhds 0) := by
  classical
  intro hT
  set S : ℕ → ℂ := fun N => ∑ q : Fin r, (μ q) ^ N with hS_def
  -- Step 1: cast `‖S N‖^2` into `ℂ` and show it tends to 0.
  have hS_norm : Tendsto (fun N : ℕ => ‖S N‖) atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero.mp hT)
  have hSsq_ℝ : Tendsto (fun N : ℕ => (‖S N‖ : ℝ) ^ 2) atTop (nhds 0) := by
    have := hS_norm.mul hS_norm
    simpa [sq] using this
  have hSsq_ℂ :
      Tendsto (fun N : ℕ => ((‖S N‖ ^ 2 : ℝ) : ℂ)) atTop (nhds 0) := by
    have hcont : Tendsto (fun x : ℝ => (x : ℂ)) (nhds (0 : ℝ)) (nhds (0 : ℂ)) := by
      have := Complex.continuous_ofReal.tendsto (0 : ℝ)
      simpa using this
    exact hcont.comp hSsq_ℝ
  -- Step 2: Cesaro mean of `(‖S N‖^2 : ℂ)` tends to 0.
  have hCes :
      Tendsto
        (fun T : ℕ => (T : ℂ)⁻¹ *
          ∑ N ∈ Finset.range T, ((‖S N‖ ^ 2 : ℝ) : ℂ))
        atTop (nhds 0) := by
    have hsmul := hSsq_ℂ.cesaro_smul
    refine hsmul.congr ?_
    intro T
    rcases Nat.eq_zero_or_pos T with hT0 | hT0
    · subst hT0
      simp
    · -- (T : ℝ)⁻¹ • z = (T : ℂ)⁻¹ * z
      change ((T : ℝ))⁻¹ • (∑ N ∈ Finset.range T, ((‖S N‖ ^ 2 : ℝ) : ℂ))
          = (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, ((‖S N‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.real_smul]
      simp
  -- Step 3: ‖S N‖^2 expands as a complex double-sum over Fin r × Fin r.
  have hSqExpand : ∀ N : ℕ,
      ((‖S N‖ ^ 2 : ℝ) : ℂ)
        = ∑ p : Fin r × Fin r, (μ p.1 * star (μ p.2)) ^ N := by
    intro N
    have hnormSq : ((‖S N‖ ^ 2 : ℝ) : ℂ) = S N * star (S N) := by
      have h1 : Complex.normSq (S N) = ‖S N‖ ^ 2 :=
        Complex.normSq_eq_norm_sq (S N)
      have h2 : S N * (starRingEnd ℂ) (S N) = (Complex.normSq (S N) : ℂ) :=
        Complex.mul_conj (S N)
      have h3 : S N * star (S N) = ((‖S N‖ ^ 2 : ℝ) : ℂ) := by
        rw [show star (S N) = (starRingEnd ℂ) (S N) from rfl, h2, h1]
      exact h3.symm
    rw [hnormSq, hS_def]
    -- S N = ∑_q μ_q^N; star (S N) = ∑_q' star (μ_q')^N
    have hStar : star (∑ q : Fin r, (μ q) ^ N)
        = ∑ q : Fin r, (star (μ q)) ^ N := by
      rw [star_sum]
      refine Finset.sum_congr rfl ?_
      intro q _
      exact star_pow (μ q) N
    rw [hStar, Fintype.sum_mul_sum]
    -- Now want: ∑ i, ∑ j, μ i ^ N * star (μ j) ^ N
    --          = ∑ p : Fin r × Fin r, (μ p.1 * star (μ p.2)) ^ N
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, j⟩ _
    change (μ i) ^ N * (star (μ j)) ^ N = (μ i * star (μ j)) ^ N
    rw [mul_pow]
  -- Step 4: Cesaro mean of the double-sum tends to a positive count.
  have hPair_unit : ∀ p : Fin r × Fin r, ‖μ p.1 * star (μ p.2)‖ = 1 := by
    intro p
    rw [norm_mul, hμ p.1, norm_star, hμ p.2, one_mul]
  -- target is the count of pairs (q, q') with μ q * star (μ q') = 1.
  let resonant : Finset (Fin r × Fin r) :=
    Finset.univ.filter (fun p => μ p.1 * star (μ p.2) = 1)
  let target : ℂ :=
    ∑ p : Fin r × Fin r, if μ p.1 * star (μ p.2) = 1 then (1 : ℂ) else 0
  -- The diagonal {(q,q) | q : Fin r} ⊆ resonant, so resonant.card ≥ r.
  have hDiag_sub :
      (Finset.univ.image (fun q : Fin r => (q, q))) ⊆ resonant := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
    have hμq_sq : μ q * star (μ q) = 1 := by
      have h := Complex.mul_conj (μ q)
      have h2 : Complex.normSq (μ q) = 1 := by
        have := Complex.normSq_eq_norm_sq (μ q)
        rw [this, hμ q, one_pow]
      have h3 : μ q * (starRingEnd ℂ) (μ q) = 1 := by
        rw [h, h2]; norm_num
      rw [show star (μ q) = (starRingEnd ℂ) (μ q) from rfl]
      exact h3
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμq_sq⟩
  have hDiag_card : (Finset.univ.image (fun q : Fin r => (q, q))).card = r := by
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
    exact (Finset.card_univ : (Finset.univ : Finset (Fin r)).card = _).trans
      (Fintype.card_fin r)
  have hResonant_card_ge : r ≤ resonant.card := by
    have := Finset.card_le_card hDiag_sub
    rw [hDiag_card] at this
    exact this
  -- target = (resonant.card : ℂ).
  have htarget_card : target = (resonant.card : ℂ) := by
    change (∑ p : Fin r × Fin r,
        if μ p.1 * star (μ p.2) = 1 then (1 : ℂ) else 0) = (resonant.card : ℂ)
    rw [Finset.sum_boole]
  -- target ≠ 0.
  have htarget_ne : target ≠ 0 := by
    rw [htarget_card]
    have : 0 < resonant.card := lt_of_lt_of_le hr hResonant_card_ge
    exact_mod_cast this.ne'
  -- Cesaro mean of each summand tends to `if (ν p) = 1 then 1 else 0`.
  have hPair_cesaro : ∀ p : Fin r × Fin r,
      Tendsto
        (fun T : ℕ => (T : ℂ)⁻¹ *
          ∑ N ∈ Finset.range T, (μ p.1 * star (μ p.2)) ^ N)
        atTop
        (nhds (if μ p.1 * star (μ p.2) = 1 then (1 : ℂ) else 0)) := by
    intro p
    by_cases hν1 : μ p.1 * star (μ p.2) = 1
    · rw [if_pos hν1]
      have := cesaro_geom_sum_one_tendsto_one
      refine this.congr' ?_
      refine Filter.Eventually.of_forall ?_
      intro T
      rw [hν1]
    · rw [if_neg hν1]
      exact cesaro_geom_sum_tendsto_zero (hPair_unit p) hν1
  -- Sum of Cesaro limits is the Cesaro limit of the sum.
  have hSum_cesaro :
      Tendsto
        (fun T : ℕ => (T : ℂ)⁻¹ *
          ∑ N ∈ Finset.range T, ∑ p : Fin r × Fin r,
            (μ p.1 * star (μ p.2)) ^ N)
        atTop (nhds target) := by
    have hSum : Tendsto
        (fun T : ℕ => ∑ p : Fin r × Fin r,
          (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, (μ p.1 * star (μ p.2)) ^ N)
        atTop (nhds target) :=
      tendsto_finset_sum
        (Finset.univ : Finset (Fin r × Fin r))
        (fun p _ => hPair_cesaro p)
    refine hSum.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro T
    -- ∑ p, (T)⁻¹ * ∑ N, f p N = (T)⁻¹ * ∑ p, ∑ N, f p N = (T)⁻¹ * ∑ N, ∑ p, f p N
    change (∑ p : Fin r × Fin r, (T : ℂ)⁻¹ *
              ∑ N ∈ Finset.range T, (μ p.1 * star (μ p.2)) ^ N)
        = (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T,
              ∑ p : Fin r × Fin r, (μ p.1 * star (μ p.2)) ^ N
    rw [← Finset.mul_sum, Finset.sum_comm]
  -- Step 5: the two limits 0 and target must agree, but target ≠ 0.
  have hCes' : Tendsto
      (fun T : ℕ => (T : ℂ)⁻¹ *
        ∑ N ∈ Finset.range T,
          ∑ p : Fin r × Fin r, (μ p.1 * star (μ p.2)) ^ N)
      atTop (nhds 0) := by
    refine hCes.congr ?_
    intro T
    congr 1
    refine Finset.sum_congr rfl ?_
    intro N _
    exact hSqExpand N
  have hUnique : (0 : ℂ) = target := tendsto_nhds_unique hCes' hSum_cesaro
  exact htarget_ne hUnique.symm

end UnitModulusPowerSum
