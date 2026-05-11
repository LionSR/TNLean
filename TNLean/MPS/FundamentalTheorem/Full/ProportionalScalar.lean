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

* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017), Theorem `thm1`, lines 1170--1192.
-/

open scoped Matrix BigOperators InnerProductSpace
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
  field_simp [hμ, hν, pow_ne_zero N hμ, pow_ne_zero N hν]
  ring_nf
  have hpow : μ ^ N * μ⁻¹ ^ N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hμ, one_pow]
  calc
    c N * ν ^ N = c N * ν ^ N * 1 := by rw [mul_one]
    _ = c N * ν ^ N * (μ ^ N * μ⁻¹ ^ N) := by rw [hpow]
    _ = c N * ν ^ N * μ ^ N * μ⁻¹ ^ N := by ring

end ProportionalScalar

end MPSTensor
