/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The number of rounds and the error of a sampled merge

ALVV, arXiv:1602.08828v2, the merge of lines 1662–1677 and Theorem `t:alg1`, lines 1777–1818,
apply `k` rounds of an improving family of at most `D²` operators after sampling `s` vectors of
the merged space. This file records the arithmetic shared by the merge trees of the
degenerate-gap case and of the frustration-free unique-ground-state case: the least integer `k`
with `D^{2k} ≥ s`, the overlap of the sample, and the error of the filtered sample.

**Local fix (rounding of the number of rounds):** the source, line 1797, takes
`k = ⌈log_D s⌉ / 2`, which is not an integer when `⌈log_D s⌉` is odd. The least integer `k` with
`D^{2k} ≥ s` gives `s ≤ D^{2k} ≤ D² s`, one factor of `D` above the source's `D^{2k} ≤ D s` in
that case. See `docs/paper-gaps/alvv16_unique_ground_state_tree.tex`.
-/

namespace TNLean.MPS.AreaLaw.ALVV

/-- The least number of rounds `k` with `D^{2k} ≥ s`, namely `k = ⌈⌈log_D s⌉ / 2⌉`, satisfies
`1 ≤ k` and `s ≤ D^{2k} ≤ D² s`. The source takes `k = ⌈log_D s⌉ / 2`, which need not be an
integer, and then has `D^{2k} ≤ D s`; rounding up costs one factor of `D`. Auxiliary to ALVV,
arXiv:1602.08828v2, the merge, lines 1662–1677, and Theorem `t:alg1`, lines 1777–1817. -/
theorem merge_rounds_bounds {D s : ℕ} (hD : 2 ≤ D) (hs : 2 ≤ s) :
    let k := (Nat.clog D s + 1) / 2
    1 ≤ k ∧ s ≤ D ^ (2 * k) ∧ D ^ (2 * k) ≤ D ^ 2 * s := by
  intro k
  have hD1 : 1 < D := hD
  have hc : 0 < Nat.clog D s := Nat.clog_pos hD1 hs
  have hup : s ≤ D ^ Nat.clog D s := Nat.le_pow_clog hD1 s
  have hlow : D ^ (Nat.clog D s - 1) < s := by
    simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self hD1 hs
  have hk1 : Nat.clog D s ≤ 2 * k := by omega
  have hk2 : 2 * k ≤ 2 + (Nat.clog D s - 1) := by omega
  refine ⟨by omega, hup.trans (Nat.pow_le_pow_right (by omega) hk1), ?_⟩
  calc D ^ (2 * k) ≤ D ^ (2 + (Nat.clog D s - 1)) := Nat.pow_le_pow_right (by omega) hk2
    _ = D ^ 2 * D ^ (Nat.clog D s - 1) := pow_add D 2 _
    _ ≤ D ^ 2 * s := Nat.mul_le_mul_left _ hlow.le

/-- When `⌈log_D s⌉` is odd and `s` is not a power of `D`, no integer number of rounds `j`
attains the source's bound `D^{2j} ≤ D s` together with the condition `s ≤ D^{2j}` of the merge
error estimate: the first forces `D^{2j} < s`. This is why the printed node bound `D s²` of
ALVV, arXiv:1602.08828v2, Theorem `t:alg1`, line 1797, is replaced by `D² s²` in that case. -/
theorem merge_rounds_lt_of_odd {D s j : ℕ} (hD : 2 ≤ D) (hs : 2 ≤ s)
    (hodd : Odd (Nat.clog D s)) (hpow : s ≠ D ^ Nat.clog D s) (hj : D ^ (2 * j) ≤ D * s) :
    D ^ (2 * j) < s := by
  have hD1 : 1 < D := hD
  set c := Nat.clog D s
  have hup : s < D ^ c := lt_of_le_of_ne (Nat.le_pow_clog hD1 s) hpow
  have hlow : D ^ (c - 1) < s := by
    simpa only [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self hD1 hs
  have hc : 0 < c := Nat.clog_pos hD1 hs
  have hlt : D ^ (2 * j) < D ^ (c + 1) :=
    hj.trans_lt (by
      rw [pow_succ, mul_comm (D ^ c)]
      exact Nat.mul_lt_mul_of_pos_left hup (by omega))
  have h2j : 2 * j < c + 1 := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  obtain ⟨t, ht⟩ := hodd
  have h2j' : 2 * j ≤ c - 1 := by omega
  exact (Nat.pow_le_pow_right (by omega) h2j').trans_lt hlow

/-- The sample overlap of a merged space of dimension `Q ≤ M s` is at least `3 / (32 M)`.
Auxiliary to ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. -/
theorem merge_sample_overlap_lower {s Q M : ℕ} (hQ0 : 0 < Q) (hM : 1 ≤ M) (hQ : Q ≤ M * s) :
    (3 : ℝ) / (32 * M) ≤ (1 - (1 / 4 : ℝ)) * (min s Q : ℕ) / (8 * Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rcases le_total Q s with hQs | hsQ
  · rw [min_eq_right hQs]
    rw [show (1 - (1 / 4 : ℝ)) * (Q : ℝ) / (8 * Q) = 3 / 32 by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [min_eq_left hsQ]
    have hQR' : (Q : ℝ) ≤ M * s := by exact_mod_cast hQ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- With `k` rounds such that `s ≤ D^{2k}`, a merged space of dimension at most `(D^{2k} s)²`,
and a family whose `k`-fold products improve by `Δ^k` with `D¹² Δ ≤ 10⁻⁵`, the error after
sampling and filtering is at most `(1024/9) · 10⁻⁵`. Auxiliary to ALVV, arXiv:1602.08828v2,
Lemmas `l:rs` and `l:er`, lines 530–558 and 597–622, and Theorem `t:alg1`, lines 1777–1817. -/
theorem merge_power_error_le {D s k Q : ℕ} (hD : 2 ≤ D) (hk : 1 ≤ k) (hsk : s ≤ D ^ (2 * k))
    (hQ0 : 0 < Q) (hQ : Q ≤ (D ^ (2 * k) * s) ^ 2) {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hbase : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000) :
    let c := (1 - (1 / 4 : ℝ)) * (min s Q : ℕ) / (8 * Q)
    0 < c ∧ Delta ^ k / c ^ 2 ≤ (1024 / 9 : ℝ) * (1 / 100000) := by
  intro c
  have hD1 : 1 ≤ D := by omega
  have hP1 : 1 ≤ D ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
  have hs0 : 0 < s := by
    by_contra h0
    have : s = 0 := by omega
    subst this
    simp at hQ
    omega
  let M := D ^ (4 * k) * s
  have hM : 1 ≤ M := Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) hs0
  have hQM : Q ≤ M * s := by
    refine hQ.trans (le_of_eq ?_)
    simp only [M]
    ring
  have hlow := merge_sample_overlap_lower hQ0 hM hQM
  have hlow0 : (0 : ℝ) < 3 / (32 * M) := by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨hlow0.trans_le hlow, ?_⟩
  have hMR : ((M : ℕ) : ℝ) = (D : ℝ) ^ (4 * k) * s := by simp only [M]; push_cast; ring
  have hsR : (s : ℝ) ≤ (D : ℝ) ^ (2 * k) := by exact_mod_cast hsk
  have hs0R : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hDR : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hpowk : Delta ^ k * (D : ℝ) ^ (12 * k) ≤ (1 / 100000 : ℝ) := by
    rw [pow_mul, ← mul_pow, mul_comm]
    calc ((D : ℝ) ^ 12 * Delta) ^ k ≤ (1 / 100000 : ℝ) ^ k :=
          pow_le_pow_left₀ (by positivity) hbase k
      _ ≤ 1 / 100000 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hM2 : ((M : ℕ) : ℝ) ^ 2 ≤ (D : ℝ) ^ (12 * k) := by
    rw [hMR]
    have h2 : (s : ℝ) ^ 2 ≤ ((D : ℝ) ^ (2 * k)) ^ 2 := pow_le_pow_left₀ hs0R hsR 2
    calc ((D : ℝ) ^ (4 * k) * s) ^ 2 = ((D : ℝ) ^ (4 * k)) ^ 2 * (s : ℝ) ^ 2 := by ring
      _ ≤ ((D : ℝ) ^ (4 * k)) ^ 2 * ((D : ℝ) ^ (2 * k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (D : ℝ) ^ (12 * k) := by rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  calc Delta ^ k / c ^ 2 ≤ Delta ^ k / (3 / (32 * M)) ^ 2 :=
        div_le_div_of_nonneg_left (pow_nonneg hDelta k) (by positivity)
          (pow_le_pow_left₀ hlow0.le hlow 2)
    _ = (1024 / 9 : ℝ) * (Delta ^ k * ((M : ℕ) : ℝ) ^ 2) := by
        have : (0 : ℝ) < M := by exact_mod_cast hM
        field_simp
        ring
    _ ≤ (1024 / 9 : ℝ) * (Delta ^ k * (D : ℝ) ^ (12 * k)) := by
        gcongr
    _ ≤ (1024 / 9 : ℝ) * (1 / 100000) := by gcongr

end TNLean.MPS.AreaLaw.ALVV
