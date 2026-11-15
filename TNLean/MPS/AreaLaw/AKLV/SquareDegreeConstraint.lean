/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A necessary window size for the square-degree AKLV estimates

For degree $s^2$, spectral ceiling $R \ge s$, and gap $\gamma \ge 0$, the
numerical rank and squared shrinking estimates used in the AKLV construction
can have product at most one only if $1024(\log s)^2 \le \gamma s$.
For the frustration-free clipped gap $g/2$, this gives
$2048(\log s)^2 \le gs$.

These are necessary conditions on the numerical upper bounds, not lower bounds
on an operator Schmidt rank or an entropy. They quantify the unresolved
parameter inference in AKLV, arXiv:1301.1162v1, proof of `t:ent`,
the source file 1dfrustrated34.tex, lines 827–846.
They neither construct a sharper filter nor establish the printed entropy rate.
-/

namespace Real

/-- A favorable product of the square-degree numerical estimates forces a
logarithmic lower bound on the window size. The gap $\gamma$ is the gap used
in the shrinking estimate. This is an auxiliary analysis of the parameter
inference in AKLV, arXiv:1301.1162v1, proof of `t:ent`, lines 827–846. -/
theorem aklv_square_degree_log_sq_le {q s : ℕ} {gamma R : ℝ}
    (hq : 1 ≤ q) (hs : 1 ≤ s) (hgamma : 0 ≤ gamma) (hR : (s : ℝ) ≤ R)
    (htrade : (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) *
      (4 * exp (-(4 * (s : ℝ) ^ 2 * sqrt (gamma / R)))) ≤ 1) :
    1024 * log (s : ℝ) ^ 2 ≤ gamma * s := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hRpos : 0 < R := hspos.trans_le hR
  have hlogs : 0 ≤ log (s : ℝ) := log_nonneg hs1
  let b : ℕ := q * (s ^ 2 + 1)
  let D : ℕ := b ^ (32 * (2 * s + 1))
  have hb : s ^ 2 ≤ b := by
    calc
      s ^ 2 ≤ s ^ 2 + 1 := Nat.le_succ _
      _ = 1 * (s ^ 2 + 1) := (one_mul _).symm
      _ ≤ b := Nat.mul_le_mul_right _ hq
  have hbR : (s : ℝ) ^ 2 ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := (sq_pos_of_pos hspos).trans_le hbR
  have hDpos : (0 : ℝ) < D := by
    dsimp only [D]
    rw [Nat.cast_pow]
    positivity
  have hbase : 2 * log (s : ℝ) ≤ log (b : ℝ) := by
    calc
      2 * log (s : ℝ) = log ((s : ℝ) ^ 2) := by rw [log_pow]; norm_num
      _ ≤ log (b : ℝ) := log_le_log (sq_pos_of_pos hspos) hbR
  have hlogD : 128 * (s : ℝ) * log (s : ℝ) ≤ log (D : ℝ) := by
    calc
      128 * (s : ℝ) * log (s : ℝ) = (64 * (s : ℝ)) * (2 * log (s : ℝ)) := by ring
      _ ≤ ((32 * (2 * s + 1) : ℕ) : ℝ) * log (b : ℝ) := by
        apply mul_le_mul _ hbase (by positivity) (by positivity)
        push_cast
        linarith
      _ = log (D : ℝ) := by dsimp only [D]; rw [Nat.cast_pow, log_pow]
  change (D : ℝ) * (4 * exp (-(4 * (s : ℝ) ^ 2 * sqrt (gamma / R)))) ≤ 1 at htrade
  have hlog := log_le_log
    (mul_pos hDpos (by positivity : 0 < 4 * exp (-(4 * (s : ℝ) ^ 2 * sqrt (gamma / R)))))
    htrade
  rw [log_one, log_mul hDpos.ne' (by positivity),
    log_mul (by norm_num : (4 : ℝ) ≠ 0) (exp_pos _).ne', log_exp] at hlog
  have hscale : 32 * log (s : ℝ) ≤ (s : ℝ) * sqrt (gamma / R) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 4 * (s : ℝ) by positivity)).mp
    nlinarith only [hlog, hlogD, log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 32 * log (s : ℝ))
    (by positivity : 0 ≤ (s : ℝ) * sqrt (gamma / R))).mpr hscale
  simp only [mul_pow, sq_sqrt (div_nonneg hgamma hRpos.le)] at hsq
  have hratio : (s : ℝ) ^ 2 * (gamma / R) ≤ gamma * s := by
    rw [← mul_div_assoc, div_le_iff₀ hRpos]
    nlinarith only [mul_le_mul_of_nonneg_left hR (mul_nonneg hgamma hspos.le)]
  nlinarith only [hsq, hratio]

/-- At the preserved half-gap, the current square-degree bounds require
$gs \ge 2048(\log s)^2$. This concerns the numerical estimates used for
frustration-free clipping in AKLV, arXiv:1301.1162v1, lines 810–846. -/
theorem aklv_frustrationFree_square_degree_log_sq_le {q s : ℕ} {g R : ℝ}
    (hq : 1 ≤ q) (hs : 1 ≤ s) (hg : 0 ≤ g) (hR : (s : ℝ) ≤ R)
    (htrade : (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) *
      (4 * exp (-(4 * (s : ℝ) ^ 2 * sqrt ((g / 2) / R)))) ≤ 1) :
    2048 * log (s : ℝ) ^ 2 ≤ g * s := by
  have h := aklv_square_degree_log_sq_le hq hs (div_nonneg hg (by norm_num)) hR htrade
  linarith

end Real
