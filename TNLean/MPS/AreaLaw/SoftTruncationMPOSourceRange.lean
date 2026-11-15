/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SoftTruncatedHamiltonianMPO

/-!
# The soft-truncation MPO on the full scale range of the source

ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268, allows every order and scale
with `t′ < (ln 2 / 2) t`. On that range every heat time of the soft series is below `ln 2 / 2`,
so one base `b = 2 (√2 - 1) < 1` controls the corrected cluster estimate uniformly. The bond
dimension of the constructed tensors is bounded explicitly by a power of
`E = 2 max{1, N²} t 2^{m+1} / ξ`, a polynomial in `t 2^{m} N / ξ` for fixed local dimension.

**Local fix (cluster estimate and bond):** the proof uses the corrected interaction-label cluster
estimate in place of the false printed one, and the bond is polynomial in `t 2^{t′} n / ξ`
rather than in `t′ 2^{t′} n / ξ`; no computational running time is asserted. See
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The exponential of the source's limiting heat time `ln 2 / 2` is `√2`. Numerical auxiliary
to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exp_log_two_div_two : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf

/-- The uniform cluster base `2 (√2 - 1)` of the source's scale range lies strictly between
zero and one. Numerical auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`,
lines 1262–1268. -/
theorem softHeat_sourceRange_base_bounds :
    0 < 2 * (Real.sqrt 2 - 1) ∧ 2 * (Real.sqrt 2 - 1) < 1 := by
  have h1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor <;> linarith

/-- On the source's scale range `m < (ln 2 / 2) t`, every heat-time base of the soft series is
at most `2 (√2 - 1)`. Numerical auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`,
lines 1262–1268. -/
theorem softHeat_base_le_of_lt_log_two {m t : ℝ} (ht : 0 < t)
    (hscale : m < Real.log 2 / 2 * t) :
    2 * (Real.exp (m / t) - 1) ≤ 2 * (Real.sqrt 2 - 1) := by
  have hratio : m / t ≤ Real.log 2 / 2 := ((div_lt_iff₀ ht).mpr hscale).le
  have he := Real.exp_le_exp.mpr hratio
  rw [exp_log_two_div_two] at he
  linarith

/-- The logarithmic cluster order is at most `1 + log E / (-log b)` with
`E = 2 max{1, N²} W / ξ`, whenever the accuracy does not exceed the coefficient budget `W`.
Numerical auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem clusterOrder_le_one_add_log {N : ℕ} {W xi b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hxi : 0 < xi) (hxiW : xi ≤ W) :
    let E := 2 * max 1 ((N : ℝ) ^ 2) * W / xi
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    1 ≤ E ∧ (r : ℝ) ≤ 1 + Real.log E / (-Real.log b) := by
  intro E r
  have hW : 0 < W := hxi.trans_le hxiW
  have hc : 0 < -Real.log b := neg_pos.mpr (Real.log_neg hb0 hb1)
  have hM : 1 ≤ max 1 ((N : ℝ) ^ 2) := le_max_left _ _
  set x := xi / W with hx
  have hx0 : 0 < x := div_pos hxi hW
  have hx1 : x ≤ 1 := (div_le_one hW).mpr hxiW
  have hE : E = max 1 ((N : ℝ) ^ 2) * (2 / x) := by
    dsimp only [E]
    rw [hx]
    field_simp
  have hE1 : 1 ≤ E := by
    rw [hE]
    have h2x : 1 ≤ 2 / x := (one_le_div hx0).mpr (by linarith)
    nlinarith
  refine ⟨hE1, ?_⟩
  -- `log (1 + x) ≥ x / 2` on `(0, 1]`.
  have hlog1 : x / 2 ≤ Real.log (1 + x) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 1 + x) (by linarith)
    have hfrac : x / 2 ≤ 1 - (1 + x)⁻¹ := by
      rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring]
      exact div_le_div_of_nonneg_left hx0.le (by linarith) (by linarith)
    linarith
  have hloglog : Real.log (x / 2) ≤ Real.log (Real.log (1 + x)) :=
    Real.log_le_log (by positivity) hlog1
  have hnum : Real.log (max 1 ((N : ℝ) ^ 2)) - Real.log (Real.log (1 + x)) ≤ Real.log E := by
    rw [hE, Real.log_mul (by positivity) (by positivity), Real.log_div (by norm_num) hx0.ne',
      Real.log_div hx0.ne' (by norm_num)] at *
    linarith
  have hY : 0 ≤ Real.log E / (-Real.log b) := div_nonneg (Real.log_nonneg hE1) hc.le
  have hceil : (⌈(Real.log (max 1 ((N : ℝ) ^ 2)) - Real.log (Real.log (1 + x))) /
      (-Real.log b)⌉₊ : ℝ) ≤ 1 + Real.log E / (-Real.log b) := by
    have hmono := Nat.ceil_mono (div_le_div_of_nonneg_right hnum hc.le)
    have hlt := Nat.ceil_lt_add_one hY
    have : ((⌈(Real.log (max 1 ((N : ℝ) ^ 2)) - Real.log (Real.log (1 + x))) /
        (-Real.log b)⌉₊ : ℕ) : ℝ) ≤ (⌈Real.log E / (-Real.log b)⌉₊ : ℝ) := by
      exact_mod_cast hmono
    linarith
  dsimp only [r]
  rw [← hx]
  push_cast
  exact max_le (by linarith) hceil

/-- The cluster bond `r² q^r` is bounded by `(1 + log E / c)² q E^{log q / c}` with
`c = -log b`, a polynomial in `E` for fixed local dimension `q`. Numerical auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem clusterBond_le_rpow {N q : ℕ} {W xi b : ℝ} (hq : 1 ≤ q) (hb0 : 0 < b) (hb1 : b < 1)
    (hxi : 0 < xi) (hxiW : xi ≤ W) :
    let E := 2 * max 1 ((N : ℝ) ^ 2) * W / xi
    let c := -Real.log b
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ((r ^ 2 * q ^ r : ℕ) : ℝ) ≤
      (1 + Real.log E / c) ^ 2 * ((q : ℝ) * E ^ (Real.log q / c)) := by
  intro E c r
  obtain ⟨hE1, hr⟩ := clusterOrder_le_one_add_log (N := N) hb0 hb1 hxi hxiW
  change (r : ℝ) ≤ 1 + Real.log E / c at hr
  have hc : 0 < c := neg_pos.mpr (Real.log_neg hb0 hb1)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpow : (q : ℝ) ^ r ≤ (q : ℝ) * E ^ (Real.log q / c) := by
    rw [← Real.rpow_natCast]
    calc
      (q : ℝ) ^ (r : ℝ) ≤ (q : ℝ) ^ (1 + Real.log E / c) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hr
      _ = (q : ℝ) * E ^ (Real.log q / c) := by
        rw [Real.rpow_add hq0, Real.rpow_one, Real.rpow_def_of_pos hq0,
          Real.rpow_def_of_pos (by linarith : (0 : ℝ) < E)]
        ring_nf
  push_cast
  exact mul_le_mul (pow_le_pow_left₀ hr0 hr 2) hpow (by positivity) (by positivity)

/-- **Soft-truncation MPO on the source's scale range.** For every positive order `m` and scale
with `m < (ln 2 / 2) t`, the actual soft-truncated Hamiltonian, with its exterior and scalar term,
has actual operator tensors within any prescribed accuracy `ξ`. The cluster order is the explicit
logarithmic ceiling with base `b = 2 (√2 - 1)`, and for `ξ ≤ t 2^{m+1}` the bond dimension is at
most `1 + N q² + (m + 1) (1 + log E / c)² q E^{log q / c}` with
`E = 2 max{1, N²} t 2^{m+1} / ξ` and `c = -log b`. All tensors are constructed from the original
nearest-neighbour interactions. ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx-eff`, lines 1178–1185 and 1262–1268. -/
theorem exists_softTruncatedHamiltonian_mpo_of_lt_log_two {N q m : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Finset (Fin N)) (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i ∈ I, h i)
    (hscale : (m : ℝ) < Real.log 2 / 2 * t) (hxi : 0 < xi) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.sqrt 2 - 1)
    let c := -Real.log b
    let E := 2 * max 1 ((N : ℝ) ^ 2) * W / xi
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / c⌉₊
    let D := (1 + N * q ^ 2) + (r ^ 2 * q ^ r) * (m + 1)
    (∃ A : Fin (N + 1) → MPOTensor q D,
      ‖((∑ i, h i) - (∑ i ∈ I, h i) + (eps : ℂ) • 1 +
          cfc (Real.softTruncation t m)
            ((∑ i ∈ I, h i) - (eps : ℂ) • 1)) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi) ∧
    (xi ≤ W → (D : ℝ) ≤ 1 + N * q ^ 2 +
      (m + 1) * ((1 + Real.log E / c) ^ 2 * ((q : ℝ) * E ^ (Real.log q / c)))) := by
  intro W b c E r D
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ht : 0 < t := by
    have hl : 0 < Real.log 2 / 2 := by positivity
    by_contra hnt
    push_neg at hnt
    nlinarith
  have hb := softHeat_sourceRange_base_bounds
  refine ⟨exists_softTruncatedHamiltonian_mpo_of_accuracy_of_base hq h hs hh hnorm I eps t xi hlo
    b ht hxi hb.1 hb.2 (softHeat_base_le_of_lt_log_two ht hscale), fun hxiW ↦ ?_⟩
  have hbond := clusterBond_le_rpow (N := N) hq hb.1 hb.2 hxi hxiW
  change ((r ^ 2 * q ^ r : ℕ) : ℝ) ≤ _ at hbond
  dsimp only [D]
  push_cast at hbond ⊢
  nlinarith [hbond]

end TNLean.MPS.AreaLaw
