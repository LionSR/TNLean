/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The inverse-gap logarithm is forced by the AKLV certificates

The entropy bound of Arad, Kitaev, Landau and Vazirani passes through one
favorable pair: a polynomial filter of degree `ℓ` whose operator Schmidt rank
`D` and squared perpendicular shrinking factor `Δ` satisfy `D Δ ≤ 1/2`. The
rank lemma bounds `D` by `(q(ℓ + 1))^(c(⌊ℓ/s⌋ + ⌊√ℓ⌋ + 1))` and the Chebyshev
estimate bounds `Δ` by `4 exp(-4ℓ√(γ/w))`, where `s` is the window width,
`w ≥ s` is the spectral ceiling of the clipped Hamiltonian and `γ ≤ g` is the
gap used in the Chebyshev estimate.

This file proves that whenever these two certificates multiply to at most one,
the rank certificate satisfies
`log D > c³ (log q + 2 log(1/g))³ / (16 g)`. No choice of `ℓ`, `s`, clipping
height or gap parameter avoids it. With `c ≥ 4`, the certificate route therefore
cannot give the printed rate `O(log³ q / g)`: at fixed `q`, the forced
`log(1/g)³ / g` is not a bounded multiple of `log³ q / g`.
`aklv_certificate_not_uniform_log_cube` states this. The integrated upper bound
`C (1 + log q + log(1/g))³ / g` is optimal for the route up to the universal
constant. The statement concerns the two upper-bound certificates only. It
gives no lower bound for the actual operator Schmidt rank, and it does not
refute the printed entropy theorem.

Source: AKLV, arXiv:1301.1162v1, `1dfrustrated34.tex`, Lemma 4.2 (line 590),
proof of Theorem `t:ent` (lines 827–846), Lemma `l:5` (lines 1003–1052).

**Local fix (rate):** The printed `O(log³ d / ε)` drops the factor
`log(s² + s)` at lines 840–843; this file shows that the factor cannot be
removed within the source's certificates. Recorded in
`docs/paper-gaps/aklv13_entropy_inverse_gap_logarithm.tex`.
-/

open Real

namespace TNLean.MPS.AreaLaw

/-- The real-variable core of `aklv_certificate_log_rank_gt`. Here `N` is the
exponent count, `Lg` the logarithm of the rank base, `X` the Chebyshev exponent
and `M = c N Lg` the logarithm of the rank certificate. -/
private lemma aklv_certificate_core {c N Lg ell s g X : ℝ}
    (hc : 4 ≤ c) (hL : 1 ≤ Lg) (hell : 1 ≤ ell) (hs : 0 < s) (hg : 0 < g) (hN : 0 < N)
    (hdiv : ell < s * N) (hsq : ell < N ^ 2) (hM : c * N * Lg < X)
    (hX2 : X ^ 2 ≤ 16 * ell ^ 2 * (g / s)) :
    c ^ 3 * Lg ^ 3 / (16 * g) < c * N * Lg ∧ 1 / g ^ 2 ≤ ell + 1 := by
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < Lg := by linarith
  have hM0 : 0 < c * N * Lg := by positivity
  have hell0 : 0 < ell := by linarith
  have hsq' : (c * N * Lg) ^ 2 < X ^ 2 := by nlinarith
  -- `(c N Lg)² s < 16 ℓ² g`.
  have hA0 : (c * N * Lg) ^ 2 * s < 16 * ell ^ 2 * g := by
    have h' : 16 * ell ^ 2 * (g / s) * s = 16 * ell ^ 2 * g := by field_simp
    have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hsq' hX2) hs
    linarith
  -- `c² N Lg² < 16 g ℓ`.
  have hA : c ^ 2 * N * Lg ^ 2 < 16 * g * ell := by
    have hl2 : ell ^ 2 < ell * (s * N) := by nlinarith
    have h2 : (c ^ 2 * N * Lg ^ 2) * (s * N) < (16 * g * ell) * (s * N) := by
      have : 16 * ell ^ 2 * g < 16 * g * (ell * (s * N)) := by nlinarith
      nlinarith
    exact lt_of_mul_lt_mul_right h2 (by positivity)
  -- `c² Lg² < 16 g N`.
  have hB : c ^ 2 * Lg ^ 2 < 16 * g * N := by
    have h1 : (c ^ 2 * Lg ^ 2) * N < (16 * g * N) * N := by
      have : 16 * g * ell < 16 * g * N ^ 2 := by nlinarith
      nlinarith
    exact lt_of_mul_lt_mul_right h1 hN.le
  refine ⟨?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    have hcL : 0 < c * Lg := by positivity
    have := mul_lt_mul_of_pos_left hB hcL
    nlinarith
  · have h4 : 4 ≤ c * Lg := by nlinarith
    have hc4 : 256 ≤ (c * Lg) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) h4 4
      norm_num at this
      exact this
    have hlow : (c * Lg) ^ 4 < 256 * g ^ 2 * ell := by
      have h1 := mul_lt_mul_of_pos_left hB (by positivity : 0 < c ^ 2 * Lg ^ 2)
      have h2 := mul_lt_mul_of_pos_left hA (by positivity : 0 < 16 * g)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- A favorable pair of AKLV certificates forces a cubic inverse-gap
logarithm in the logarithm of the rank certificate. Here the rank certificate
is `(q(ℓ + 1))^(c(⌊ℓ/s⌋ + ⌊√ℓ⌋ + 1))`, as in Lemma 4.2 of AKLV,
arXiv:1301.1162v1 (line 590, with the corrected count of
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf),
and the squared shrinking certificate is `4 exp(-4ℓ√(γ/w))`, as in Lemma 4.1
(lines 530–583) at gap `γ ≤ g` and ceiling `w ≥ s`. The proof of Theorem `t:ent`
(lines 827–846) needs such a favorable pair. -/
theorem aklv_certificate_log_rank_gt {q ell s c : ℕ} {g γ w : ℝ}
    (hq : 2 ≤ q) (hs : 0 < s) (hc : 4 ≤ c) (hg : 0 < g) (hγ : 0 ≤ γ)
    (hγg : γ ≤ g) (hsw : (s : ℝ) ≤ w)
    (hfav : (((q * (ell + 1)) ^ (c * (ell / s + Nat.sqrt ell + 1)) : ℕ) : ℝ) *
      (4 * exp (-(4 * (ell : ℝ) * sqrt (γ / w)))) ≤ 1) :
    (c : ℝ) ^ 3 * (log q + 2 * log (1 / g)) ^ 3 / (16 * g) <
      log (((q * (ell + 1)) ^ (c * (ell / s + Nat.sqrt ell + 1)) : ℕ) : ℝ) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ell / s + Nat.sqrt ell + 1 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * (ell : ℝ) * sqrt (γ / w) := ⟨_, rfl⟩
  rw [← hN] at hfav ⊢
  rw [← hX] at hfav
  have hq1 : 1 ≤ q := by omega
  have hBpos : 0 < q * (ell + 1) := Nat.mul_pos (by omega) (Nat.succ_pos _)
  have hDpos : (0 : ℝ) < (((q * (ell + 1)) ^ (c * N) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos hBpos
  have hlogD : log ((((q * (ell + 1)) ^ (c * N) : ℕ) : ℝ)) =
      (c : ℝ) * N * log ((q : ℝ) * ((ell : ℝ) + 1)) := by
    rw [Nat.cast_pow, log_pow]; push_cast; ring
  -- The favorable product gives `log D < X`.
  have hDlt : (((q * (ell + 1)) ^ (c * N) : ℕ) : ℝ) < exp X := by
    have hexp : exp (-X) * exp X = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos (-X), exp_pos X]
  have hMlt := (log_lt_iff_lt_exp hDpos).mpr hDlt
  rw [hlogD] at hMlt
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hdiv : (ell : ℝ) < s * N := by
    have h := Nat.lt_mul_div_succ ell hs
    have h' : ell < s * N :=
      lt_of_lt_of_le h (Nat.mul_le_mul_left s
        (by rw [hN]; exact Nat.add_le_add_right (Nat.le_add_right _ _) 1))
    exact_mod_cast h'
  have hsqrt : (ell : ℝ) < (N : ℝ) ^ 2 := by
    have h := Nat.lt_succ_sqrt' ell
    have h' : ell < N ^ 2 :=
      lt_of_lt_of_le h (Nat.pow_le_pow_left
        (by rw [hN]; exact Nat.add_le_add_right (Nat.le_add_left _ _) 1) 2)
    exact_mod_cast h'
  have hX2 : X ^ 2 ≤ 16 * (ell : ℝ) ^ 2 * (g / s) := by
    have hq0 : 0 ≤ γ / w := div_nonneg hγ (hsR.le.trans hsw)
    have hratio : γ / w ≤ g / s := div_le_div₀ hg.le hγg hsR hsw
    rw [hX, mul_pow, mul_pow, sq_sqrt hq0]
    have : (0 : ℝ) ≤ 4 ^ 2 * (ell : ℝ) ^ 2 := by positivity
    nlinarith
  -- The degree is positive, so the rank base is at least four.
  have hell : 1 ≤ ell := by
    rcases Nat.eq_zero_or_pos ell with h0 | h
    · exfalso
      have hX0 : X = 0 := by simp [hX, h0]
      have hlogB : 0 ≤ log ((q : ℝ) * ((ell : ℝ) + 1)) :=
        log_nonneg (by
          have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
          nlinarith [(Nat.cast_nonneg ell : (0 : ℝ) ≤ ell)])
      have : 0 ≤ (c : ℝ) * N * log ((q : ℝ) * ((ell : ℝ) + 1)) := by positivity
      linarith
    · exact h
  have hL : 1 ≤ log ((q : ℝ) * ((ell : ℝ) + 1)) := by
    have hB4 : (4 : ℝ) ≤ (q : ℝ) * ((ell : ℝ) + 1) := by
      have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
      nlinarith
    have h4 : (1 : ℝ) ≤ log 4 := by
      rw [le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    exact h4.trans (log_le_log (by norm_num) hB4)
  have hcR : (4 : ℝ) ≤ c := by exact_mod_cast hc
  obtain ⟨hMain, hellg⟩ :=
    aklv_certificate_core hcR hL (by exact_mod_cast hell) hsR hg hNpos hdiv hsqrt hMlt hX2
  have hLb : log q + 2 * log (1 / g) ≤ log ((q : ℝ) * ((ell : ℝ) + 1)) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    rw [log_mul hq0.ne' (by positivity)]
    have hlog : 2 * log (1 / g) ≤ log ((ell : ℝ) + 1) := by
      have := log_le_log (by positivity) hellg
      rwa [one_div, ← inv_pow, log_pow, ← one_div] at this
    linarith
  have hcube := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).monotone hLb
  rw [hlogD]
  calc
    (c : ℝ) ^ 3 * (log q + 2 * log (1 / g)) ^ 3 / (16 * g) ≤
        (c : ℝ) ^ 3 * log ((q : ℝ) * ((ell : ℝ) + 1)) ^ 3 / (16 * g) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (by positivity)) (by positivity)
    _ < _ := hMain

/-- The certificate route cannot give the printed rate. For every local
dimension `q ≥ 2` and every constant `C`, there is a gap `0 < g ≤ 1` such that every
favorable pair of AKLV certificates at that gap has rank certificate with
`log D > C log³ q / g`. AKLV, arXiv:1301.1162v1, proof of Theorem `t:ent`,
lines 827–846, where the factor `log(s² + s)` is dropped. -/
theorem aklv_certificate_not_uniform_log_cube {q : ℕ} (hq : 2 ≤ q) (C : ℝ) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
      ∀ {ell s c : ℕ} {γ w : ℝ}, 0 < s → 4 ≤ c → 0 ≤ γ → γ ≤ g → (s : ℝ) ≤ w →
        (((q * (ell + 1)) ^ (c * (ell / s + Nat.sqrt ell + 1)) : ℕ) : ℝ) *
          (4 * exp (-(4 * (ell : ℝ) * sqrt (γ / w)))) ≤ 1 →
        C * log q ^ 3 / g <
          log (((q * (ell + 1)) ^ (c * (ell / s + Nat.sqrt ell + 1)) : ℕ) : ℝ) := by
  set x : ℝ := |C| * log q ^ 3 + 1 with hxdef
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith [abs_nonneg C, pow_nonneg hlogq 3]
  refine ⟨exp (-x), exp_pos _, exp_le_one_iff.mpr (by linarith), ?_⟩
  intro ell s c γ w hs hc hγ hγg hsw hfav
  have hlower := aklv_certificate_log_rank_gt hq hs hc (exp_pos _) hγ hγg hsw hfav
  refine lt_of_le_of_lt ?_ hlower
  have hlog : log (1 / exp (-x)) = x := by rw [one_div, ← exp_neg, neg_neg, log_exp]
  rw [hlog]
  have hb : 2 * x ≤ log q + 2 * x := by linarith
  have hcube : (2 * x) ^ 3 ≤ (log q + 2 * x) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hb 3
  have hcR : (64 : ℝ) ≤ (c : ℝ) ^ 3 := by
    have h4 : (4 : ℝ) ≤ c := by exact_mod_cast hc
    have := pow_le_pow_left₀ (by norm_num) h4 3
    norm_num at this
    exact this
  have hCx : C * log q ^ 3 ≤ x := by
    rw [hxdef]; nlinarith [le_abs_self C, pow_nonneg hlogq 3]
  have hx3 : x ≤ 4 * (2 * x) ^ 3 := by
    have hxx : 0 ≤ (x - 1) * (x * (x + 1)) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hg : 0 < exp (-x) := exp_pos _
  rw [div_le_div_iff₀ hg (by positivity)]
  have hstep : C * log q ^ 3 * 16 ≤ (c : ℝ) ^ 3 * (log q + 2 * x) ^ 3 := by
    have h0 : 0 ≤ (log q + 2 * x) ^ 3 := by positivity
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hstep hg.le]

end TNLean.MPS.AreaLaw
