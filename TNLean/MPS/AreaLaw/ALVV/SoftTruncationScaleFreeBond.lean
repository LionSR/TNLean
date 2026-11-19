/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SoftTruncationMPOSourceRange

/-!
# A soft-truncation MPO whose bond does not grow with the scale

ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268, allows every order `m ≥ 1`
and scale with `m < (ln 2 / 2) t`, and bounds the bond by `poly(t′ 2^{t′} n / ξ)` with no
dependence on the scale `t`. The heat coefficients of the soft series have absolute sum
`t 2^{m+1}`, so the required cluster precision grows with `t`. The heat times `a / t`,
`0 ≤ a ≤ m`, shrink at the same rate: every heat-time base is at most `2 √2 m / t`. With the
base `b = min {2 (√2 - 1), 2 √2 m / t}` the cluster exponent `-log b` grows like `log t`, and
the two growths cancel. The resulting bond is bounded by an explicit expression in `m`, `N`,
`q` and `ξ` alone,
`1 + N q² + (m + 1) (2 + log E₀ / c₀)² q² E₀^{log q / c₀}`, where
`E₀ = 2 max {1, N²} 2^{m+1} 2 √2 m / ξ` and `c₀ = -log (2 (√2 - 1))`. For fixed local
dimension this is polynomial in `m 2^m N / ξ`, the quantity of the printed bound.
The bound is stated for `ξ ≤ 2^{m+1}`; for every `ξ > 0`, as the source allows, the same bound
holds at `min {ξ, 2^{m+1}}` (`exists_softTruncatedHamiltonian_mpo_scaleFree_of_pos`).

**Local fix (cluster estimate):** the proof uses the corrected interaction-label cluster
estimate in place of the false printed one; no computational running time is asserted.
See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

/-- On the source's scale range every heat-time base of the soft series is at most
`2 √2 m / t`. Numerical auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`,
lines 1262–1268. -/
theorem softHeat_base_le_sqrt_two_mul_div {m t : ℝ} (hm : 0 ≤ m) (ht : 0 < t)
    (hscale : m < Real.log 2 / 2 * t) :
    2 * (Real.exp (m / t) - 1) ≤ 2 * Real.sqrt 2 * (m / t) := by
  set x := m / t with hxdef
  have hx0 : 0 ≤ x := div_nonneg hm ht.le
  have hx : x ≤ Real.log 2 / 2 := ((div_lt_iff₀ ht).mpr hscale).le
  have he : Real.exp x ≤ Real.sqrt 2 := by
    have h := Real.exp_le_exp.mpr hx
    rwa [exp_log_two_div_two] at h
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos := Real.exp_pos x
  have hmain : Real.exp x - 1 ≤ x * Real.exp x := by nlinarith
  nlinarith

/-- The scale-adapted cluster base `min {2 (√2 - 1), 2 √2 m / t}` lies strictly between zero
and one and dominates every heat-time base on the source's scale range. Numerical auxiliary to
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem softHeat_scaleFreeBase_bounds {m t : ℝ} (hm : 0 < m) (ht : 0 < t)
    (hscale : m < Real.log 2 / 2 * t) :
    let b := min (2 * (Real.sqrt 2 - 1)) (2 * Real.sqrt 2 * (m / t))
    0 < b ∧ b < 1 ∧ 2 * (Real.exp (m / t) - 1) ≤ b := by
  intro b
  have hb := softHeat_sourceRange_base_bounds
  refine ⟨lt_min hb.1 (by positivity), (min_le_left _ _).trans_lt hb.2, le_min
    (softHeat_base_le_of_lt_log_two ht hscale)
    (softHeat_base_le_sqrt_two_mul_div hm.le ht hscale)⟩

/-- The cluster exponent `-log b` of the scale-adapted base absorbs the growth of `log t`: the
logarithmic cluster order is at most `2 + log E₀ / c₀`, with
`E₀ = 2 max {1, N²} 2^{m+1} 2 √2 m / ξ` and `c₀ = -log (2 (√2 - 1))`, independently of the
scale. Numerical auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`,
lines 1262–1268. -/
theorem softClusterOrder_le_scaleFree {N m : ℕ} {t xi : ℝ} (hm : 0 < m)
    (hscale : (m : ℝ) < Real.log 2 / 2 * t) (hxi : 0 < xi) (hxi2 : xi ≤ (2 : ℝ) ^ (m + 1)) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := min (2 * (Real.sqrt 2 - 1)) (2 * Real.sqrt 2 * ((m : ℝ) / t))
    let c0 := -Real.log (2 * (Real.sqrt 2 - 1))
    let E0 := 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) * (2 * Real.sqrt 2 * m) / xi
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    0 < c0 ∧ 1 ≤ E0 ∧ (r : ℝ) ≤ 2 + Real.log E0 / c0 := by
  intro W b c0 E0 r
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl2 : 0 < Real.log 2 / 2 := by positivity
  have ht : 0 < t := pos_of_mul_pos_right ((by linarith : (0 : ℝ) < m).trans hscale) hl2.le
  obtain ⟨hb0, hb1, -⟩ := softHeat_scaleFreeBase_bounds (by linarith) ht hscale
  have hB := softHeat_sourceRange_base_bounds
  have hc0 : 0 < c0 := neg_pos.mpr (Real.log_neg hB.1 hB.2)
  have hc : 0 < -Real.log b := neg_pos.mpr (Real.log_neg hb0 hb1)
  have hs2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  -- The scale is at least one, so the accuracy does not exceed the coefficient budget.
  have ht1 : 1 ≤ t := by
    have : (m : ℝ) < t / 2 := by nlinarith
    linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hxiW : xi ≤ W := by
    dsimp only [W]
    nlinarith
  obtain ⟨-, hr⟩ := clusterOrder_le_one_add_log (N := N) hb0 hb1 hxi hxiW
  change (r : ℝ) ≤ 1 + Real.log (2 * max 1 ((N : ℝ) ^ 2) * W / xi) / (-Real.log b) at hr
  have hM : 1 ≤ max 1 ((N : ℝ) ^ 2) := le_max_left _ _
  set s := t / (2 * Real.sqrt 2 * m) with hsdef
  have hk : 0 < 2 * Real.sqrt 2 * (m : ℝ) := by positivity
  have hs0 : 0 < s := div_pos ht hk
  -- `E = E₀ s`.
  have hE : 2 * max 1 ((N : ℝ) ^ 2) * W / xi = E0 * s := by
    dsimp only [W, E0]
    rw [hsdef]
    field_simp
  have hE0 : 1 ≤ E0 := by
    dsimp only [E0]
    rw [le_div_iff₀ hxi]
    have h2 : (2 : ℝ) ≤ 2 * Real.sqrt 2 * m := by nlinarith
    have h3 : (2 : ℝ) ^ (m + 1) ≤ 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) := by
      nlinarith
    have h4 : 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) ≤
        2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) * (2 * Real.sqrt 2 * m) := by
      have : 0 ≤ 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) := by positivity
      nlinarith
    linarith
  refine ⟨hc0, hE0, ?_⟩
  -- `-log b` dominates both `c₀` and `log s`.
  have hcc0 : c0 ≤ -Real.log b := by
    dsimp only [c0]
    exact neg_le_neg (Real.log_le_log hb0 (min_le_left _ _))
  have hbs : b ≤ s⁻¹ := by
    refine (min_le_right _ _).trans_eq ?_
    rw [hsdef, inv_div]
    ring
  have hcs : Real.log s ≤ -Real.log b := by
    have h := Real.log_le_log hb0 hbs
    rw [Real.log_inv] at h
    linarith
  have hlogE : Real.log (E0 * s) = Real.log E0 + Real.log s :=
    Real.log_mul (by positivity) hs0.ne'
  have hL0 : 0 ≤ Real.log E0 := Real.log_nonneg hE0
  have hpart1 : Real.log E0 / (-Real.log b) ≤ Real.log E0 / c0 :=
    div_le_div_of_nonneg_left hL0 hc0 hcc0
  have hpart2 : Real.log s / (-Real.log b) ≤ 1 := (div_le_one hc).mpr hcs
  rw [hE, hlogE, add_div] at hr
  linarith

/-- The cluster bond `r² q^r` at the scale-adapted base is bounded independently of the scale
by `(2 + log E₀ / c₀)² q² E₀^{log q / c₀}`. Numerical auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem softClusterBond_le_scaleFree {N q m : ℕ} {t xi : ℝ} (hq : 1 ≤ q) (hm : 0 < m)
    (hscale : (m : ℝ) < Real.log 2 / 2 * t) (hxi : 0 < xi) (hxi2 : xi ≤ (2 : ℝ) ^ (m + 1)) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := min (2 * (Real.sqrt 2 - 1)) (2 * Real.sqrt 2 * ((m : ℝ) / t))
    let c0 := -Real.log (2 * (Real.sqrt 2 - 1))
    let E0 := 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) * (2 * Real.sqrt 2 * m) / xi
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ((r ^ 2 * q ^ r : ℕ) : ℝ) ≤
      (2 + Real.log E0 / c0) ^ 2 * ((q : ℝ) ^ 2 * E0 ^ (Real.log q / c0)) := by
  intro W b c0 E0 r
  obtain ⟨hc0, hE0, hr⟩ := softClusterOrder_le_scaleFree (N := N) hm hscale hxi hxi2
  change (r : ℝ) ≤ 2 + Real.log E0 / c0 at hr
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpow : (q : ℝ) ^ r ≤ (q : ℝ) ^ 2 * E0 ^ (Real.log q / c0) := by
    rw [← Real.rpow_natCast]
    calc
      (q : ℝ) ^ (r : ℝ) ≤ (q : ℝ) ^ (2 + Real.log E0 / c0) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hr
      _ = (q : ℝ) ^ 2 * E0 ^ (Real.log q / c0) := by
        rw [Real.rpow_add hq0, Real.rpow_two, Real.rpow_def_of_pos hq0,
          Real.rpow_def_of_pos (by linarith : (0 : ℝ) < E0)]
        ring_nf
  push_cast
  exact mul_le_mul (pow_le_pow_left₀ hr0 hr 2) hpow (by positivity) (by positivity)

/-- **Soft-truncation MPO with a bond independent of the scale.** For every positive order
`m` and scale with `m < (ln 2 / 2) t`, the actual soft-truncated Hamiltonian, with its exterior
and scalar term, has actual operator tensors within any prescribed accuracy `ξ`. The cluster
order is the logarithmic ceiling at the base `b = min {2 (√2 - 1), 2 √2 m / t}`, and for
`ξ ≤ 2^{m+1}` the bond dimension is at most
`1 + N q² + (m + 1) (2 + log E₀ / c₀)² q² E₀^{log q / c₀}` with
`E₀ = 2 max {1, N²} 2^{m+1} 2 √2 m / ξ` and `c₀ = -log (2 (√2 - 1))`, which does not depend
on `t`. All tensors are constructed from the original nearest-neighbour interactions.
ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx-eff`, lines 1178–1185 and
1262–1268. -/
theorem exists_softTruncatedHamiltonian_mpo_scaleFree {N q m : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Finset (Fin N)) (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i ∈ I, h i)
    (hscale : (m : ℝ) < Real.log 2 / 2 * t) (hxi : 0 < xi) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := min (2 * (Real.sqrt 2 - 1)) (2 * Real.sqrt 2 * ((m : ℝ) / t))
    let c0 := -Real.log (2 * (Real.sqrt 2 - 1))
    let E0 := 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) * (2 * Real.sqrt 2 * m) / xi
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    let D := (1 + N * q ^ 2) + (r ^ 2 * q ^ r) * (m + 1)
    (∃ A : Fin (N + 1) → MPOTensor q D,
      ‖((∑ i, h i) - (∑ i ∈ I, h i) + (eps : ℂ) • 1 +
          cfc (Real.softTruncation t m)
            ((∑ i ∈ I, h i) - (eps : ℂ) • 1)) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi) ∧
    (xi ≤ (2 : ℝ) ^ (m + 1) → (D : ℝ) ≤ 1 + N * q ^ 2 +
      (m + 1) * ((2 + Real.log E0 / c0) ^ 2 * ((q : ℝ) ^ 2 * E0 ^ (Real.log q / c0)))) := by
  intro W b c0 E0 r D
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ht : 0 < t := by
    have hl : 0 < Real.log 2 / 2 := by positivity
    exact pos_of_mul_pos_right (hmR.trans hscale) hl.le
  obtain ⟨hb0, hb1, hbase⟩ := softHeat_scaleFreeBase_bounds hmR ht hscale
  refine ⟨TNLean.MPS.AreaLaw.exists_softTruncatedHamiltonian_mpo_of_accuracy_of_base hq h hs
    hh hnorm I eps t xi hlo b ht hxi hb0 hb1 hbase, fun hxi2 ↦ ?_⟩
  have hbond := softClusterBond_le_scaleFree (N := N) (t := t) hq hm hscale hxi hxi2
  change ((r ^ 2 * q ^ r : ℕ) : ℝ) ≤ _ at hbond
  dsimp only [D]
  push_cast at hbond ⊢
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hbond hm1
  dsimp only [E0, c0] at this ⊢
  linarith

/-- **Lemma 5.4 for every accuracy, with a bond independent of the scale.** For every positive
order `m`, scale with `m < (ln 2 / 2) t` and accuracy `ξ > 0`, the actual soft-truncated
Hamiltonian has operator tensors within `ξ` whose bond dimension is at most
`1 + N q² + (m + 1) (2 + log E₀ / c₀)² q² E₀^{log q / c₀}`, where `ξ' = min {ξ, 2^{m+1}}`,
`E₀ = 2 max {1, N²} 2^{m+1} 2 √2 m / ξ'` and `c₀ = -log (2 (√2 - 1))`; the bound does not
depend on `t`. ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268, under the
local fix of this module. -/
theorem exists_softTruncatedHamiltonian_mpo_scaleFree_of_pos {N q m : ℕ}
    (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Finset (Fin N)) (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i ∈ I, h i)
    (hscale : (m : ℝ) < Real.log 2 / 2 * t) (hxi : 0 < xi) :
    let xi' := min xi ((2 : ℝ) ^ (m + 1))
    let c0 := -Real.log (2 * (Real.sqrt 2 - 1))
    let E0 := 2 * max 1 ((N : ℝ) ^ 2) * (2 : ℝ) ^ (m + 1) * (2 * Real.sqrt 2 * m) / xi'
    ∃ (D : ℕ) (A : Fin (N + 1) → MPOTensor q D),
      ‖((∑ i, h i) - (∑ i ∈ I, h i) + (eps : ℂ) • 1 +
          cfc (Real.softTruncation t m)
            ((∑ i ∈ I, h i) - (eps : ℂ) • 1)) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi ∧
      (D : ℝ) ≤ 1 + N * q ^ 2 +
        (m + 1) * ((2 + Real.log E0 / c0) ^ 2 * ((q : ℝ) ^ 2 * E0 ^ (Real.log q / c0))) := by
  intro xi' c0 E0
  have hxi' : 0 < xi' := lt_min hxi (by positivity)
  obtain ⟨⟨A, hA⟩, hD⟩ := exists_softTruncatedHamiltonian_mpo_scaleFree hq hm h hs hh hnorm I
    eps t xi' hlo hscale hxi'
  exact ⟨_, A, hA.trans (min_le_left _ _), hD (min_le_right _ _)⟩

end TNLean.MPS.AreaLaw.ALVV
