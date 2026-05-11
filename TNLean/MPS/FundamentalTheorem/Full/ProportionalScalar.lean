/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.DominantWeight

/-!
# Scalar control for proportional MPV families

This module contains the elementary scalar estimates used in the proportional
block-selection step of the fundamental theorem. The statements are separated
from `NondecayingOverlap` to keep the block-selection file focused on the
overlap argument.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem `thm1`, lines 1170--1192.
-/

open scoped BigOperators
open Filter

namespace MPSTensor

section ProportionalScalar

/-- **Norm convergence for a scalar sequence between normalized vectors.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. This is the
analytic core used in the proportional block-selection argument: if
`x_N = c_N y_N` and both vector norms tend to one, then the scalar moduli tend
to one. -/
lemma tendsto_norm_scalar_of_tendsto_norm_one
    {E : ℕ → Type*} [∀ N, NormedAddCommGroup (E N)] [∀ N, NormedSpace ℂ (E N)]
    (x y : (N : ℕ) → E N) (c : ℕ → ℂ)
    (hxy : ∀ N : ℕ, x N = c N • y N)
    (hx_norm : Tendsto (fun N : ℕ => ‖x N‖) atTop (nhds (1 : ℝ)))
    (hy_norm : Tendsto (fun N : ℕ => ‖y N‖) atTop (nhds (1 : ℝ))) :
    Tendsto (fun N : ℕ => ‖c N‖) atTop (nhds (1 : ℝ)) := by
  have hRatio :
      Tendsto (fun N : ℕ => ‖x N‖ / ‖y N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hx_norm.div hy_norm one_ne_zero
  have hy_norm_ne : ∀ᶠ N in atTop, ‖y N‖ ≠ (0 : ℝ) :=
    hy_norm.eventually_ne one_ne_zero
  have hRatio_eq : (fun N : ℕ => ‖x N‖ / ‖y N‖) =ᶠ[atTop] fun N : ℕ => ‖c N‖ := by
    filter_upwards [hy_norm_ne] with N hN
    rw [hxy N, norm_smul]
    exact mul_div_cancel_right₀ (‖c N‖) hN
  exact Tendsto.congr' hRatio_eq hRatio

/-- **Eventual norm convergence for a scalar sequence between normalized vectors.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. Lemma `Lem1`
only supplies linear independence for all sufficiently large lengths, so the
scalar-normalization argument must tolerate replacing a lengthwise identity by
an eventual one. -/
lemma tendsto_norm_scalar_of_eventually_tendsto_norm_one
    {E : ℕ → Type*} [∀ N, NormedAddCommGroup (E N)] [∀ N, NormedSpace ℂ (E N)]
    (x y : (N : ℕ) → E N) (c : ℕ → ℂ)
    (hxy : ∀ᶠ N in atTop, x N = c N • y N)
    (hx_norm : Tendsto (fun N : ℕ => ‖x N‖) atTop (nhds (1 : ℝ)))
    (hy_norm : Tendsto (fun N : ℕ => ‖y N‖) atTop (nhds (1 : ℝ))) :
    Tendsto (fun N : ℕ => ‖c N‖) atTop (nhds (1 : ℝ)) := by
  have hRatio :
      Tendsto (fun N : ℕ => ‖x N‖ / ‖y N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hx_norm.div hy_norm one_ne_zero
  have hy_norm_ne : ∀ᶠ N in atTop, ‖y N‖ ≠ (0 : ℝ) :=
    hy_norm.eventually_ne one_ne_zero
  have hRatio_eq : (fun N : ℕ => ‖x N‖ / ‖y N‖) =ᶠ[atTop] fun N : ℕ => ‖c N‖ := by
    filter_upwards [hxy, hy_norm_ne] with N hN hN_ne
    rw [hN, norm_smul]
    exact mul_div_cancel_right₀ (‖c N‖) hN_ne
  exact Tendsto.congr' hRatio_eq hRatio

-- The two scalar-convergence statements below are named separately because
-- issue #1563 uses them as analytic steps in the CPSV16 lines 1170--1192
-- block-selection contradiction.

/-- **Norm convergence for the proportional scalar sequence.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. In the
proportional block-selection argument the scalar relating the two total MPV
families cannot vanish asymptotically once both weighted BNT state sums have
asymptotic norm one. This lemma isolates the purely analytic step: from
`x_N = c_N y_N`, `‖x_N‖ → 1`, and `‖y_N‖ → 1`, one gets `‖c_N‖ → 1`. -/
lemma tendsto_norm_weighted_mpvState_scalar_of_tendsto_norm_one
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ)
    (hState : ∀ N : ℕ,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (hA_norm : Tendsto
      (fun N : ℕ =>
        ‖∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N‖)
      atTop (nhds (1 : ℝ)))
    (hB_norm : Tendsto
      (fun N : ℕ =>
        ‖∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N‖)
      atTop (nhds (1 : ℝ))) :
    Tendsto (fun N : ℕ => ‖c N‖) atTop (nhds (1 : ℝ)) := by
  exact tendsto_norm_scalar_of_tendsto_norm_one
    (fun N : ℕ =>
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N)
    (fun N : ℕ =>
      ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)
    c hState hA_norm hB_norm

/-- **Geometrically damped vectors tend to zero.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. This is the
analytic estimate behind the dominant-weight normalization: a non-dominant
weight ratio has modulus strictly less than one, while the corresponding MPV
state norms remain bounded because their self-overlaps tend to one. -/
lemma tendsto_geometric_smul_of_tendsto_norm_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (v : ℕ → E) (hc : ‖c‖ < 1)
    (hv : Tendsto (fun N : ℕ => ‖v N‖) atTop (nhds (1 : ℝ))) :
    Tendsto (fun N : ℕ => c ^ N • v N) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hv).exists_norm_le
  have hgeom : Tendsto (fun N : ℕ => ‖c‖ ^ N * C) atTop (nhds 0) := by
    have hpow : Tendsto (fun N : ℕ => (‖c‖ : ℝ) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
        rwa [Real.norm_of_nonneg (norm_nonneg c)])
    simpa only [zero_mul] using hpow.mul_const C
  apply squeeze_zero (fun N => norm_nonneg _) ?_ hgeom
  intro N
  calc
    ‖c ^ N • v N‖ = ‖c ^ N‖ * ‖v N‖ := norm_smul _ _
    _ ≤ ‖c ^ N‖ * C := mul_le_mul_of_nonneg_left
      (by
        simpa [Real.norm_of_nonneg (norm_nonneg (v N))] using
          hC _ (Set.mem_range_self N))
      (norm_nonneg _)
    _ = ‖c‖ ^ N * C := by rw [norm_pow]

/-- **Dominant-weight-normalized BNT state sums have norm one asymptotically.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. After dividing a
weighted BNT MPV-state sum by a selected dominant weight, the dominant block
has coefficient one, all other coefficients have modulus strictly less than
one, and the BNT overlap normalization makes the tail vanish. Hence the
normalized sum has norm tending to one. -/
lemma tendsto_norm_weighted_mpvState_sum_of_dominant_ratio
    {d r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (j₀ : Fin r) (hμ0 : μ j₀ ≠ 0)
    (h_self : ∀ j : Fin r,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds 1))
    (h_ratio : ∀ j : Fin r, j ≠ j₀ → ‖μ j / μ j₀‖ < 1) :
    Tendsto
      (fun N : ℕ =>
        ‖∑ j : Fin r, (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N‖)
      atTop (nhds (1 : ℝ)) := by
  classical
  let tail := fun N : ℕ =>
    ∑ j ∈ Finset.univ.erase j₀, (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N
  have htail_norm : Tendsto (fun N : ℕ => ‖tail N‖) atTop (nhds (0 : ℝ)) := by
    have hmajor :
        Tendsto
          (fun N : ℕ =>
            ∑ j ∈ Finset.univ.erase j₀,
              ‖μ j / μ j₀‖ ^ N * ‖mpvState (d := d) (A j) N‖)
          atTop (nhds (0 : ℝ)) := by
      have hterm : ∀ j ∈ Finset.univ.erase j₀,
          Tendsto
            (fun N : ℕ => ‖μ j / μ j₀‖ ^ N * ‖mpvState (d := d) (A j) N‖)
            atTop (nhds (0 : ℝ)) := by
        intro j hj
        obtain ⟨C, hC⟩ :=
          (Metric.isBounded_range_of_tendsto _
            (tendsto_norm_mpvState_one (d := d) (A j) (h_self j))).exists_norm_le
        have hgeom : Tendsto (fun N : ℕ => ‖μ j / μ j₀‖ ^ N * C) atTop
            (nhds (0 : ℝ)) := by
          have hpow : Tendsto (fun N : ℕ => ‖μ j / μ j₀‖ ^ N) atTop
              (nhds (0 : ℝ)) :=
            tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
              simpa [Real.norm_of_nonneg (norm_nonneg (μ j / μ j₀))] using
                h_ratio j (Finset.ne_of_mem_erase hj))
          simpa only [zero_mul] using hpow.mul_const C
        apply squeeze_zero (fun N => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
          ?_ hgeom
        intro N
        exact mul_le_mul_of_nonneg_left
          (by
            simpa [Real.norm_of_nonneg (norm_nonneg (mpvState (d := d) (A j) N))] using
              hC _ (Set.mem_range_self N))
          (pow_nonneg (norm_nonneg _) _)
      simpa using tendsto_finset_sum (Finset.univ.erase j₀) hterm
    apply squeeze_zero (fun N => norm_nonneg _) ?_ hmajor
    intro N
    calc
      ‖tail N‖
          ≤ ∑ j ∈ Finset.univ.erase j₀,
              ‖(μ j / μ j₀) ^ N • mpvState (d := d) (A j) N‖ := by
            simpa [tail] using norm_sum_le (Finset.univ.erase j₀)
              (fun j => (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N)
      _ = ∑ j ∈ Finset.univ.erase j₀,
              ‖μ j / μ j₀‖ ^ N * ‖mpvState (d := d) (A j) N‖ := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [norm_smul, norm_pow]
  have hv0 : Tendsto (fun N : ℕ => ‖mpvState (d := d) (A j₀) N‖)
      atTop (nhds (1 : ℝ)) :=
    tendsto_norm_mpvState_one (d := d) (A j₀) (h_self j₀)
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          ‖∑ j : Fin r, (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N‖ -
            ‖mpvState (d := d) (A j₀) N‖)
        atTop (nhds (0 : ℝ)) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero
      (fun N => abs_nonneg _)
      ?_
      (show Tendsto (fun N : ℕ => ‖tail N‖) atTop (nhds (0 : ℝ)) from htail_norm)
    intro N
    have hsplit :
        ∑ j : Fin r, (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N =
          mpvState (d := d) (A j₀) N + tail N := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
      simp [tail, div_self hμ0]
    calc
      |‖∑ j : Fin r, (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N‖ -
          ‖mpvState (d := d) (A j₀) N‖|
          ≤ ‖(∑ j : Fin r, (μ j / μ j₀) ^ N • mpvState (d := d) (A j) N) -
              mpvState (d := d) (A j₀) N‖ := abs_norm_sub_norm_le _ _
      _ = ‖tail N‖ := by
            rw [hsplit]
            simp
  have hnorm_sum := hdiff.add hv0
  simpa only [sub_add_cancel, zero_add] using hnorm_sum

/-- **Dominant-weight-normalized BNT state sums have norm one asymptotically.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. This is the
same estimate as
`tendsto_norm_weighted_mpvState_sum_of_dominant_ratio`, written in the form
used directly after expanding a canonical-form tensor: divide the weighted
state sum by the selected dominant weight raised to the chain length. -/
lemma tendsto_norm_normalized_weighted_mpvState_sum_of_dominant
    {d r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (j₀ : Fin r) (hμ0 : μ j₀ ≠ 0)
    (h_self : ∀ j : Fin r,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds 1))
    (h_ratio : ∀ j : Fin r, j ≠ j₀ → ‖μ j / μ j₀‖ < 1) :
    Tendsto
      (fun N : ℕ =>
        ‖(μ j₀ ^ N)⁻¹ •
          (∑ j : Fin r, (μ j) ^ N • mpvState (d := d) (A j) N)‖)
      atTop (nhds (1 : ℝ)) := by
  have hratio :=
    tendsto_norm_weighted_mpvState_sum_of_dominant_ratio
      A j₀ hμ0 h_self h_ratio
  convert hratio using 1
  ext N
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  rw [div_pow]
  field_simp [pow_ne_zero N hμ0]

/-- **Scalar factor identity for dominant-weight normalization.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. Dividing the two
sides of a proportional weighted sum by nonzero weights \(\mu^N\) and
\(\nu^N\) changes the proportionality scalar from `c` to `c * (ν / μ) ^ N`. -/
lemma adjusted_scalar_factor_eq
    (c μ ν : ℂ) (N : ℕ) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    (μ ^ N)⁻¹ * c = (c * (ν / μ) ^ N) * (ν ^ N)⁻¹ := by
  field_simp [hμ, hν, pow_ne_zero N hμ, pow_ne_zero N hν]
  ring_nf
  have hpow : μ ^ N * μ⁻¹ ^ N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hμ, one_pow]
  calc
    c * ν ^ N = c * ν ^ N * 1 := by rw [mul_one]
    _ = c * ν ^ N * (μ ^ N * μ⁻¹ ^ N) := by rw [hpow]
    _ = c * ν ^ N * μ ^ N * μ⁻¹ ^ N := by ring

/-- **Norm convergence for the dominant-weight-normalized proportional scalar.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. The canonical-form
argument compares block sums after division by the selected dominant weights.
If the unnormalized sums satisfy `S_A(N) = c_N S_B(N)` and the two normalized
sums have norm tending to one, then the corrected scalar
`c_N(\nu/\mu)^N` has modulus tending to one. This avoids imposing any
dominant-weight normalization absent from the source statement. -/
lemma tendsto_norm_adjusted_weighted_mpvState_scalar_of_tendsto_norm_one
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hState : ∀ N : ℕ,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (hA_norm : Tendsto
      (fun N : ℕ =>
        ‖(μ ^ N)⁻¹ •
          (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N)‖)
      atTop (nhds (1 : ℝ)))
    (hB_norm : Tendsto
      (fun N : ℕ =>
        ‖(ν ^ N)⁻¹ •
          (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)‖)
      atTop (nhds (1 : ℝ))) :
    Tendsto (fun N : ℕ => ‖c N * (ν / μ) ^ N‖) atTop (nhds (1 : ℝ)) := by
  refine tendsto_norm_scalar_of_tendsto_norm_one
    (fun N : ℕ =>
      (μ ^ N)⁻¹ •
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N))
    (fun N : ℕ =>
      (ν ^ N)⁻¹ •
        (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (fun N : ℕ => c N * (ν / μ) ^ N) ?_ hA_norm hB_norm
  intro N
  change
    (μ ^ N)⁻¹ •
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
      (c N * (ν / μ) ^ N) •
        ((ν ^ N)⁻¹ •
          (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
  rw [hState N]
  rw [smul_smul, smul_smul]
  congr 1
  exact adjusted_scalar_factor_eq (c N) μ ν N hμ hν

/-- **Eventual norm convergence for the adjusted proportional scalar.**

Source context: arXiv:1606.00608, Theorem `thm1`, line 1182. In the
tail-reduction stage only sufficiently large lengths remain after applying
Lemma `Lem1`. The same dominant-weight normalization therefore yields modulus
convergence for the adjusted scalar from an eventual weighted-state identity. -/
lemma tendsto_norm_adjusted_weighted_mpvState_scalar_of_eventually_tendsto_norm_one
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (c : ℕ → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hState : ∀ᶠ N in atTop,
      (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
        c N • (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (hA_norm : Tendsto
      (fun N : ℕ =>
        ‖(μ ^ N)⁻¹ •
          (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N)‖)
      atTop (nhds (1 : ℝ)))
    (hB_norm : Tendsto
      (fun N : ℕ =>
        ‖(ν ^ N)⁻¹ •
          (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)‖)
      atTop (nhds (1 : ℝ))) :
    Tendsto (fun N : ℕ => ‖c N * (ν / μ) ^ N‖) atTop (nhds (1 : ℝ)) := by
  refine tendsto_norm_scalar_of_eventually_tendsto_norm_one
    (fun N : ℕ =>
      (μ ^ N)⁻¹ •
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N))
    (fun N : ℕ =>
      (ν ^ N)⁻¹ •
        (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
    (fun N : ℕ => c N * (ν / μ) ^ N) ?_ hA_norm hB_norm
  refine hState.mono ?_
  intro N hN
  change
    (μ ^ N)⁻¹ •
        (∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N) =
      (c N * (ν / μ) ^ N) •
        ((ν ^ N)⁻¹ •
          (∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N))
  rw [hN]
  rw [smul_smul, smul_smul]
  congr 1
  exact adjusted_scalar_factor_eq (c N) μ ν N hμ hν

/-- **Normalized weighted projections use the adjusted proportional scalar.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. In the
block-selection argument the proportional weighted projection identity is used
after division by selected nonzero dominant weights. This lemma records the
algebraic rewrite: if the unnormalized projected sums are related by `c_N`,
then the normalized projected sums are related by `c_N(\nu/\mu)^N`. -/
lemma normalized_weighted_mpvInner_eq_mul_adjusted_of_eq_mul
    {d rA rB D : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (X : MPSTensor d D) (c : ℕ → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hInner : ∀ N : ℕ,
      (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
        c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)) :
    ∀ N : ℕ,
      (μ ^ N)⁻¹ *
          (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
        (c N * (ν / μ) ^ N) *
          ((ν ^ N)⁻¹ *
            (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)) := by
  intro N
  let S : ℂ := ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N
  rw [hInner N]
  change (μ ^ N)⁻¹ * (c N * S) =
    (c N * (ν / μ) ^ N) * ((ν ^ N)⁻¹ * S)
  calc
    (μ ^ N)⁻¹ * (c N * S) = ((μ ^ N)⁻¹ * c N) * S := by ring
    _ = ((c N * (ν / μ) ^ N) * (ν ^ N)⁻¹) * S := by
      rw [adjusted_scalar_factor_eq (c N) μ ν N hμ hν]
    _ = (c N * (ν / μ) ^ N) * ((ν ^ N)⁻¹ * S) := by ring

end ProportionalScalar

end MPSTensor
