/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PolynomialFilterParameters

/-!
# A common filter scale at a fixed low-density bandwidth

For each positive bandwidth, one scalar constant is chosen before the chain,
Hamiltonian, count base and narrower energy width. The actual ceiling controls
both the physical residual needed for spectral-window comparison and the
polynomial count versus suppression tradeoff. The clipping threshold is the
window scale itself, so the five-region norm budget is seven times that scale.

The bandwidth dependence is explicit: the quantifiers are `∀ etaLD > 0, ∃ A`.
ALVV, arXiv:1602.08828v2, Assumption (LD), lines 281–284, fixes a positive
constant bandwidth. These are supporting parameters for Theorem `t:aisgapless`,
lines 1027–1041. All dependence on the fixed bandwidth is retained in the
scalar constant.
-/

namespace Real

/-- At a fixed positive low-density bandwidth, one degree controls the actual
residual comparison and the count-suppression tradeoff. The constant precedes
all count bases and widths. This supports ALVV, arXiv:1602.08828v2,
Assumption (LD), lines 281–284, and Theorem `t:aisgapless`, lines 1027–1041.
The residual estimate is calibrated at the same ceiling as the count. -/
theorem exists_fixed_bandwidth_low_density_filter_parameters
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ A : ℝ, 100 ≤ A ∧ 19 + etaLD ≤ A ∧
      ∀ (m : ℕ) (w : ℝ), 2 ≤ m → 0 < w →
      let g := min w 1
      let u := 1 + log (m : ℝ) + log (1 / g)
      let ell : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      21 ≤ ell ∧ 19 + etaLD ≤ (ell : ℝ) ∧
      log (D : ℝ) ≤ 22 * (A + 1) * (6 + 2 * log (A + 1)) / g * u ^ 3 ∧
      (∀ eta : ℝ, 0 ≤ eta → eta ≤ etaLD →
        let xi := (288 * exp (11 / 8)) * exp (-((ell : ℝ) - eta) / 8)
        xi ≤ 1 ∧ 2 * (6 + eta) * xi ≤ (1 / 200) * w ^ 2) ∧
      ∀ R : ℝ, 0 < R → R ≤ 7 * (ell : ℝ) →
        (D : ℝ) ^ 12 *
          (4 * exp (-(4 * (ell : ℝ) ^ 2 * sqrt ((4 * g / 5) / R)))) ≤
            1 / 100000 := by
  let C0 := 288 * exp (11 / 8)
  let C := C0 * exp (etaLD / 8)
  let epsilon := 1 / (400 * (6 + etaLD))
  let M := max 100 (max (19 + etaLD)
    ((max 0 (log (C / epsilon)) + 2 + 1 / 8) / (1 / 8)))
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hden : 0 < 6 + etaLD := by linarith only [hLD]
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hepsilon1 : epsilon ≤ 1 := by
    dsimp only [epsilon]
    apply (div_le_iff₀ (by positivity : 0 < 400 * (6 + etaLD))).mpr
    linarith only [hLD]
  obtain ⟨A, _hA, hA21, hAM, _hAlog, hall⟩ :=
    exists_dg_scalar_parameters (7 / 2) M (by norm_num)
  have hA100 : 100 ≤ A := (le_max_left _ _).trans hAM
  have hAeta : 19 + etaLD ≤ A :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hAM
  have hMtail : (max 0 (log (C / epsilon)) + 2 + 1 / 8) / (1 / 8) ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, hA100, hAeta, ?_⟩
  intro m w hm hw g u ell D
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hgw : g ≤ w := min_le_left _ _
  obtain ⟨_hlower, _hupper, hellA, _hcount, hlogD, htrade, htail⟩ := hall m g hm hg hg1
  have hell21 : (21 : ℝ) ≤ (ell : ℝ) := hA21.trans hellA
  refine ⟨by exact_mod_cast hell21, hAeta.trans hellA, hlogD, ?_, ?_⟩
  · intro eta heta0 hetaLD xi
    have htail' : C * exp (-(1 / 8) * ((ell : ℝ) - g)) ≤ epsilon * g ^ 2 := by
      simpa only [rpow_two] using
        htail C (1 / 8) epsilon 2 hC (by norm_num) hepsilon (by norm_num) hMtail
    have hxi : xi ≤ C * exp (-(1 / 8) * ((ell : ℝ) - g)) := by
      calc
        xi ≤ C0 * exp (etaLD / 8 + (-(1 / 8) * ((ell : ℝ) - g))) :=
          mul_le_mul_of_nonneg_left
            (exp_le_exp.mpr (by linarith only [hetaLD, hg.le])) hC0.le
        _ = C * exp (-(1 / 8) * ((ell : ℝ) - g)) := by
          rw [exp_add]
          dsimp only [C]
          ring
    have hsmall : xi ≤ epsilon * g ^ 2 := hxi.trans htail'
    have hg2 : g ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hg.le hg1 2
    have hxi1 : xi ≤ 1 := by
      calc
        xi ≤ epsilon * g ^ 2 := hsmall
        _ ≤ (1 : ℝ) * 1 := mul_le_mul hepsilon1 hg2 (sq_nonneg g) zero_le_one
        _ = 1 := one_mul 1
    refine ⟨hxi1, ?_⟩
    have hcoefficient : 2 * (6 + etaLD) * epsilon = 1 / 200 := by
      dsimp only [epsilon]
      field_simp [hden.ne']
      ring
    calc
      2 * (6 + eta) * xi ≤ 2 * (6 + eta) * (epsilon * g ^ 2) :=
        mul_le_mul_of_nonneg_left hsmall (by linarith only [heta0])
      _ ≤ 2 * (6 + etaLD) * (epsilon * g ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith only [hetaLD])
          (mul_nonneg hepsilon.le (sq_nonneg g))
      _ = (2 * (6 + etaLD) * epsilon) * g ^ 2 := by ring
      _ = (1 / 200 : ℝ) * g ^ 2 := by rw [hcoefficient]
      _ ≤ (1 / 200 : ℝ) * w ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hgw 2) (by norm_num)
  · intro R hR hRup
    exact htrade R hR (by linarith only [hRup])

end Real
