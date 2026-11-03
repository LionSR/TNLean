/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.InterleavedFilterParameters
import QICLean.Analysis.ViableNodeSamplingParameters

/-!
# Sampling and independent truncation at the same physical count

The sampling size, small target accuracy and clipping threshold are
chosen at the actual polynomial-family count. The failure target is fixed
before the family. These scalar estimates support ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
and the parameter selection, lines 1797–1805.
-/

namespace Real

/-- The actual sampling ceiling has a logarithmic bound at a size scale
fixed before every parent space. The scale corresponds to the fixed
failure target `(L+1)^(-2)`. Supporting ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558, and lines 1797–1805. -/
theorem interleaved_sample_size_bounds (r L D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) :
    let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
    let A := log (D : ℝ) + w
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    1 ≤ w ∧ 1 ≤ s ∧ (s : ℝ) ≤ 4097 * (r : ℝ) * A ∧ log (s : ℝ) ≤ 13 * A := by
  intro w A s
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hlogr : 0 ≤ log (r : ℝ) := log_nonneg hrR
  have hlogD : 0 ≤ log (D : ℝ) := log_nonneg hDR
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hlogL : 0 ≤ log ((L : ℝ) + 1) := log_nonneg (by linarith only [hL])
  have hw : 1 ≤ w := by dsimp only [w]; linarith
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  have hlogrA : log (r : ℝ) ≤ A - 1 := by dsimp only [A, w]; linarith
  obtain ⟨hs, _hlower, hupper, hlog⟩ := viable_node_sample_size_log_bound hr hA hlogrA
  exact ⟨hw, hs, hupper, hlog⟩

/-- The uniform actual sample-overlap lower bound gives a valid tiny
clipping accuracy and the required quadratic reference budget at the
same count. Supporting ALVV, arXiv:1602.08828v2, Lemma `l:rs`,
lines 530–558, and the interleaved analysis, lines 1797–1805. -/
theorem interleaved_overlap_accuracy_bounds (D s : ℕ) (hD : 2 ≤ D) (hs : 1 ≤ s) :
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    0 < a ∧ a ≤ 1 / 100 ∧ 0 < tau ∧ tau ≤ 1 ∧
      200 * tau ≤ 1 ∧ 4 * tau ≤ a ^ 2 / 16384 := by
  intro a tau
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hD0 : (0 : ℝ) < D := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hDpow : (4096 : ℝ) ≤ (D : ℝ) ^ 12 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hDR 12
    norm_num at h ⊢
    exact h
  have hsPow : (1 : ℝ) ≤ (s : ℝ) ^ 5 := one_le_pow₀ hsR
  have hprod : (4096 : ℝ) ≤ (D : ℝ) ^ 12 * (s : ℝ) ^ 5 := by
    simpa only [mul_one] using mul_le_mul hDpow hsPow (by norm_num) (by positivity)
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a ≤ 1 / 100 := by
    dsimp only [a]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)).mpr
    nlinarith only [hprod]
  have haSq : a ^ 2 ≤ 1 := by nlinarith
  have htau : 0 < tau := by dsimp only [tau]; positivity
  refine ⟨ha, ha1, htau, ?_, ?_, ?_⟩
  · dsimp only [tau]
    linarith only [haSq]
  · dsimp only [tau]
    linarith only [haSq]
  · dsimp only [tau]
    nlinarith [sq_nonneg a]

/-- The logarithmic cost of the actual tiny alignment accuracy is bounded
at the same count and sampling size. Supporting ALVV,
arXiv:1602.08828v2, interleaved parameter selection, lines 1797–1805. -/
theorem interleaved_accuracy_log_bounds (D s : ℕ) (hD : 2 ≤ D) (hs : 1 ≤ s) :
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    24 * log (D : ℝ) ≤ log (1 / tau) ∧
      log (1 / tau) ≤ 28 + 24 * log (D : ℝ) + 10 * log (s : ℝ) := by
  intro a tau
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hlogs : 0 ≤ log (s : ℝ) := log_nonneg (by exact_mod_cast hs)
  obtain ⟨ha, _ha1, _htau, _htau1, _hepsilon, _hreference⟩ :=
    interleaved_overlap_accuracy_bounds D s hD hs
  change 0 < a at ha
  have hlog2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hlog2up : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hratio0 : 0 ≤ log (32 / 3 : ℝ) := log_nonneg (by norm_num)
  have hratioup : log (32 / 3 : ℝ) ≤ 4 := by
    calc
      log (32 / 3 : ℝ) ≤ log ((2 : ℝ) ^ 4) := log_le_log (by norm_num) (by norm_num)
      _ = 4 * log 2 := log_pow 2 4
      _ ≤ _ := by linarith only [hlog2up]
  have haInv : 1 / a = (32 / 3 : ℝ) * (D : ℝ) ^ 12 * (s : ℝ) ^ 5 := by
    dsimp only [a]
    rw [one_div_div]
    ring
  have hloga : log (1 / a) = log (32 / 3 : ℝ) +
      12 * log (D : ℝ) + 5 * log (s : ℝ) := by
    rw [haInv,
      log_mul (by positivity : (32 / 3 : ℝ) * (D : ℝ) ^ 12 ≠ 0) (pow_ne_zero 5 hs0.ne'),
      log_mul (by norm_num : (32 / 3 : ℝ) ≠ 0) (pow_ne_zero 12 hD0.ne'),
      log_pow, log_pow]
    norm_num
  have htauInv : 1 / tau = 1048576 / a ^ 2 := by
    dsimp only [tau]
    rw [one_div_div]
  have hlogNum : log (1048576 : ℝ) = 20 * log 2 := by
    calc
      log (1048576 : ℝ) = log ((2 : ℝ) ^ 20) := by norm_num
      _ = 20 * log 2 := log_pow 2 20
  have hlogtau : log (1 / tau) = 20 * log 2 + 2 * log (1 / a) := by
    rw [htauInv, log_div (by norm_num : (1048576 : ℝ) ≠ 0) (pow_ne_zero 2 ha.ne'),
      log_pow, hlogNum, one_div, log_inv]
    ring
  rw [hlogtau, hloga]
  constructor <;> linarith only [hlog2, hlog2up, hratio0, hratioup, hlogs]

end Real
