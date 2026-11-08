/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.OptimizedRankLog

/-!
# Cube-root accuracy parameters for frustration-free clipping

For a requested squared error `ρ`, put `z = log(128/ρ)` and `r = (z²/g)^{1/3}`.
The window is enlarged from an initial width `s₀ ≥ 1/g` by twice `m = ⌈6r⌉`.
At degree `s²` and the fixed frustration-free cutoff `1024/g`, the Chebyshev
shrinking factor is at most `ρ/64`. The logarithm of the common rank budget is
at most a universal multiple of `u³/g + r(u + log(z+1))`, where
`u = 1 + log q + log(1/g)`.

Source: AKLV, arXiv:1301.1162v1, Section 5, lines 862–870. The source takes
`ℓ = s²` and `s` of order `ε^{-1/3} log^{2/3} n` (line 868). The exponent of the
gap at line 867 is `+1/2`, as at line 835.

**Local fix (rate):** The gap exponent at line 867 is read as `+1/2`. The
logarithmic rank cost retains the factor `u + log(z+1)` and the additive term
`u³/g`: Lemma `l:agsp` (line 590) gives the rank `(dℓ)^{O(ℓ/s)}`, whose logarithm
at `ℓ = s²` is of order `s(log d + log s)`, while line 868 prints `exp(s log d)`.
The printed `exp(O(ε^{-1/3} log^{2/3} n))` is not asserted. See
`docs/paper-gaps/aklv13_frustration_free_mps_rate.tex`.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- The cube-root window increment `m = ⌈6 (z²/g)^{1/3}⌉` with `z = log(128/ρ)`.
AKLV, arXiv:1301.1162v1, line 868, where `s` is of order `ε^{-1/3} log^{2/3} n`. -/
noncomputable def aklvFrustrationFreeIncrement (g rho : ℝ) : ℕ :=
  ⌈6 * (aklvAccuracyLog rho ^ 2 / g) ^ ((1 : ℝ) / 3)⌉₊

/-- The common rank budget at initial width `s₀` and enlarged width `s = s₀ + 2m`:
the product of the two filter ranks at degrees `s₀²` and `s²`, or the exact
boundary rank `q^{s - ⌊s/2⌋}`. AKLV, arXiv:1301.1162v1, lines 862–868. -/
noncomputable def aklvFrustrationFreeRankBound (q s0 : ℕ) (g rho : ℝ) : ℕ :=
  let s := s0 + 2 * aklvFrustrationFreeIncrement g rho
  max ((q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) * (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)))
    (q ^ (s - s / 2))

/-- The cube-root scale `r = (z²/g)^{1/3}` is at least one, satisfies `r³ = z²/g`
and `r ≤ z/g`, and the increment lies between `6r` and `7r`. -/
theorem aklvFrustrationFreeIncrement_bounds {g rho : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    let z := aklvAccuracyLog rho
    let r := (z ^ 2 / g) ^ ((1 : ℝ) / 3)
    1 ≤ r ∧ r ^ 3 = z ^ 2 / g ∧ 6 * r ≤ (aklvFrustrationFreeIncrement g rho : ℝ) ∧
      (aklvFrustrationFreeIncrement g rho : ℝ) ≤ 7 * r ∧ r ≤ z / g := by
  intro z r
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have harg : 0 ≤ z ^ 2 / g := by positivity
  have hr3 : r ^ 3 = z ^ 2 / g := by
    have h := rpow_inv_natCast_pow harg (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [r, Nat.cast_ofNat, one_div] using h
  have hr1 : 1 ≤ r :=
    one_le_rpow ((one_le_div hg).mpr (hg1.trans (one_le_pow₀ hz))) (by norm_num)
  have hm : 6 * r ≤ (aklvFrustrationFreeIncrement g rho : ℝ) := Nat.le_ceil _
  have hm' : (aklvFrustrationFreeIncrement g rho : ℝ) < 6 * r + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  refine ⟨hr1, hr3, hm, by linarith, ?_⟩
  have hzg : 0 ≤ z / g := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hzg
  rw [hr3, div_pow, div_le_div_iff₀ hg (by positivity)]
  have hg3 : g ^ 3 ≤ g := pow_le_of_le_one hg.le hg1 (by norm_num)
  have hz2 : z ^ 2 ≤ z ^ 3 := pow_le_pow_right₀ hz (by norm_num)
  calc
    z ^ 2 * g ^ 3 ≤ z ^ 2 * g := mul_le_mul_of_nonneg_left hg3 (by positivity)
    _ ≤ z ^ 3 * g := mul_le_mul_of_nonneg_right hz2 hg.le

/-- At degree `s²`, the frustration-free cutoff `1024/g` and half-gap `g/2`, the
Chebyshev shrinking factor is at most `ρ/64` once `s ≥ 1/g` and `g s³ ≥ 1728 z²`.
AKLV, arXiv:1301.1162v1, lines 864–869, with the gap exponent `+1/2` of line 835. -/
theorem aklvFrustrationFree_shrink_le {g rho : ℝ} (hg : 0 < g)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) {s : ℕ} (hgap : 1 / g ≤ (s : ℝ))
    (hscale : 1728 * aklvAccuracyLog rho ^ 2 ≤ g * (s : ℝ) ^ 3) :
    2 * exp (-2 * ((s ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * (1024 / g) + s))) ≤
      rho / 64 := by
  let z := aklvAccuracyLog rho
  let w := (g / 2) / (2 * (1024 / g) + (s : ℝ))
  obtain ⟨hz, hexp⟩ := aklvAccuracyLog_bounds hrho hrho1
  change 1 ≤ z at hz
  change exp (-z) = rho / 128 at hexp
  have hs : 0 < (s : ℝ) := (by positivity : (0 : ℝ) < 1 / g).trans_le hgap
  have hden : 0 < 2 * (1024 / g) + (s : ℝ) := by positivity
  have hw : 0 ≤ w := by positivity
  have hcut : 2 * (1024 / g) + (s : ℝ) ≤ 2049 * s := by
    have : 2 * (1024 / g) = 2048 * (1 / g) := by ring
    linarith
  have hsquare : z ^ 2 ≤ (2 * (s : ℝ) ^ 2) ^ 2 * w := by
    dsimp only [w]
    rw [mul_div_assoc', le_div_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hcut (sq_nonneg z)
    have hz3 : 1728 * z ^ 2 * (s : ℝ) ≤ g * (s : ℝ) ^ 3 * s :=
      mul_le_mul_of_nonneg_right hscale hs.le
    linarith only [hmul, hz3, mul_nonneg hg.le (pow_nonneg hs.le 4)]
  have hX : z ≤ 2 * ((s ^ 2 : ℕ) : ℝ) * sqrt w := by
    push_cast
    have hsq : (2 * (s : ℝ) ^ 2 * sqrt w) ^ 2 = (2 * (s : ℝ) ^ 2) ^ 2 * w := by
      rw [mul_pow, sq_sqrt hw]
    exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
      (by rw [hsq]; exact hsquare)
  calc
    2 * exp (-2 * ((s ^ 2 : ℕ) : ℝ) * sqrt w) ≤ 2 * exp (-z) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by norm_num)
      linarith
    _ = rho / 64 := by rw [hexp]; ring

/-- The common rank budget has logarithm at most a universal multiple of
`u³/g + r(u + log(z+1))`, given the initial width and initial rank bounds of
the frustration-free parameter choice. If `m ≤ s₀` the second filter costs at
most `10⁴ log D₀`; otherwise its cost is linear in `m ≤ 7z/g`.
AKLV, arXiv:1301.1162v1, lines 864–870, with the rate of the module's local
fix. -/
theorem aklvFrustrationFreeRankBound_log_le {q : ℕ} (hq : 2 ≤ q) {g rho : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    {s0 : ℕ} (hs0 : 1 ≤ s0) {R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W) :
    let u := 1 + log (q : ℝ) + log (1 / g)
    let z := aklvAccuracyLog rho
    let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
    log (D0 : ℝ) ≤ R / g * u ^ 3 → (s0 : ℝ) ≤ W / g * u ^ 2 →
    log (aklvFrustrationFreeRankBound q s0 g rho : ℝ) ≤
      (10001 * R + W) * (u ^ 3 / g) +
        8400000 * ((z ^ 2 / g) ^ ((1 : ℝ) / 3) * (u + log (z + 1))) := by
  intro u z D0 hlogD0 hs0W
  obtain ⟨hr1, _hr3, hm6, hm7, hrz⟩ := aklvFrustrationFreeIncrement_bounds hg hg1 hrho hrho1
  let r := (z ^ 2 / g) ^ ((1 : ℝ) / 3)
  change 1 ≤ r at hr1
  change r ≤ z / g at hrz
  let m := aklvFrustrationFreeIncrement g rho
  change 6 * r ≤ (m : ℝ) at hm6
  change (m : ℝ) ≤ 7 * r at hm7
  let s := s0 + 2 * m
  let D1 : ℕ := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
  let V := u + log (z + 1)
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hlogz : 0 ≤ log (z + 1) := log_nonneg (by linarith)
  have hV : 0 ≤ V := by dsimp only [V]; linarith
  have hrV : 0 ≤ r * V := by positivity
  have hm1 : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hspos : 0 < s := by dsimp only [s]; omega
  have hD0 : 0 ≤ log (D0 : ℝ) := log_natCast_nonneg D0
  have hD0R : 0 ≤ R / g * u ^ 3 := hD0.trans hlogD0
  have hform : (q * (s ^ 2 + 1)) ^ (32 * (s ^ 2 / s + Nat.sqrt (s ^ 2) + 1)) = D1 := by
    have hdiv : s ^ 2 / s = s := by rw [pow_two, Nat.mul_div_cancel _ hspos]
    rw [hdiv, Nat.sqrt_eq', ← two_mul]
  have h66 (n : ℕ) (hn : s ≤ 3 * n) : s ^ 2 ≤ 66 * n ^ 2 :=
    calc
      s ^ 2 ≤ (3 * n) ^ 2 := Nat.pow_le_pow_left hn 2
      _ = 9 * n ^ 2 := by ring
      _ ≤ 66 * n ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
  have hfilter : log (D1 : ℝ) ≤ 10000 * log (D0 : ℝ) + 8400000 * (r * V) := by
    rcases le_total m s0 with hms | hms
    · have hell : s ^ 2 ≤ 66 * s0 ^ 2 := h66 s0 (by dsimp only [s]; omega)
      have hcost := aklv_log_rank_le_initial_cost hq hs0 (Nat.le_add_right s0 (2 * m)) hell
      rw [hform] at hcost
      linarith only [hcost, hrV]
    · have hell : s ^ 2 ≤ 66 * m ^ 2 := h66 m (by dsimp only [s]; omega)
      have hz' : 1 ≤ 7 * z / g := by
        rw [le_div_iff₀ hg]
        linarith
      have hmz : (m : ℝ) ≤ 7 * z / g + 1 := by
        have h7 : 7 * r ≤ 7 * z / g := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hrz (by norm_num)
        linarith
      have hcost := aklv_log_rank_le_accuracy_cost hq hm1
        (show m ≤ s by dsimp only [s]; omega) hell hz' hmz
      rw [hform] at hcost
      have hz1 : 0 < z + 1 := by linarith
      have hzg : 7 * z / g + 1 ≤ 7 * (z + 1) * (1 / g) := by
        rw [show 7 * (z + 1) * (1 / g) = 7 * z / g + 7 / g by ring]
        have : 1 ≤ 7 / g := by rw [le_div_iff₀ hg]; linarith
        linarith
      have hlogz' : log (7 * z / g + 1) ≤ log 7 + log (z + 1) + log (1 / g) := by
        have h := log_le_log (by positivity) hzg
        rwa [log_mul (by positivity) (by positivity),
          log_mul (by norm_num) (ne_of_gt hz1)] at h
      have hlog7 : log (7 : ℝ) ≤ 2 := by
        have h2 := log_two_lt_d9
        have h78 : log (7 / 8 : ℝ) ≤ 7 / 8 - 1 := log_le_sub_one_of_pos (by norm_num)
        have hid : log (7 : ℝ) = log (7 / 8) + 3 * log 2 := by
          rw [show (7 : ℝ) = 7 / 8 * 2 ^ 3 by norm_num, log_mul (by norm_num) (by norm_num),
            log_pow]
          norm_num
        linarith
      have hbase : 1 + log (q : ℝ) + log (7 * z / g + 1) ≤ 3 * V := by
        dsimp only [V, u]
        linarith
      have hlog' : 0 ≤ log (7 * z / g + 1) := log_nonneg (by linarith)
      have hprod : (m : ℝ) * (1 + log (q : ℝ) + log (7 * z / g + 1)) ≤ (7 * r) * (3 * V) :=
        mul_le_mul hm7 hbase (by linarith) (by linarith)
      linarith only [hcost, hprod, hD0]
  have hboundary : ((s - s / 2 : ℕ) : ℝ) * log (q : ℝ) ≤
      W * (u ^ 3 / g) + 8400000 * (r * V) := by
    have hS : ((s - s / 2 : ℕ) : ℝ) ≤ (s0 : ℝ) + 2 * (m : ℝ) := by
      have h : s - s / 2 ≤ s0 + 2 * m := Nat.sub_le _ _
      exact_mod_cast h
    have hlogqu : log (q : ℝ) ≤ u := by dsimp only [u]; linarith
    have hfirst : (s0 : ℝ) * log (q : ℝ) ≤ W * (u ^ 3 / g) := by
      calc
        (s0 : ℝ) * log (q : ℝ) ≤ (W / g * u ^ 2) * u :=
          mul_le_mul hs0W hlogqu hlogq (by positivity)
        _ = W * (u ^ 3 / g) := by ring
    have hsecond : 2 * (m : ℝ) * log (q : ℝ) ≤ 14 * (r * V) := by
      have huV : log (q : ℝ) ≤ V := by dsimp only [V]; linarith
      have h := mul_le_mul (show 2 * (m : ℝ) ≤ 14 * r by linarith) huV hlogq (by positivity)
      linarith
    linarith only [mul_le_mul_of_nonneg_right hS hlogq, hfirst, hsecond, hrV]
  have hD1 : 0 < (D1 : ℝ) := by dsimp only [D1]; positivity
  have hD0pos : 0 < (D0 : ℝ) := by dsimp only [D0]; positivity
  have hprodlog : log ((D0 * D1 : ℕ) : ℝ) ≤ (10001 * R + W) * (u ^ 3 / g) + 8400000 * (r * V) := by
    rw [Nat.cast_mul, log_mul (ne_of_gt hD0pos) (ne_of_gt hD1)]
    have hR' : R / g * u ^ 3 = R * (u ^ 3 / g) := by ring
    have hWu : 0 ≤ W * (u ^ 3 / g) := by positivity
    linarith only [hlogD0, hfilter, hR', hWu]
  have hbdlog : log ((q ^ (s - s / 2) : ℕ) : ℝ) ≤
      (10001 * R + W) * (u ^ 3 / g) + 8400000 * (r * V) := by
    rw [Nat.cast_pow, log_pow]
    have hRu : 0 ≤ R * (u ^ 3 / g) := by positivity
    linarith only [hboundary, hRu]
  unfold aklvFrustrationFreeRankBound
  change log ((max (D0 * D1) (q ^ (s - s / 2)) : ℕ) : ℝ) ≤ _
  rcases le_total (D0 * D1) (q ^ (s - s / 2)) with hle | hle
  · rw [max_eq_right hle]
    exact hbdlog
  · rw [max_eq_left hle]
    exact hprodlog

end TNLean.MPS.AreaLaw
