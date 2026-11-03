/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyFilterParameters

/-!
# An explicit low-energy count at the source scale

The cap on the effective spectral width is absorbed into a constant
controlled by the fixed density bandwidth. The resulting count retains
its logarithmic correction and does not identify the capped width with
the uncapped one. These are scalar estimates supporting ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
-/

namespace Real

/-- The source bandwidth condition controls the inverse capped width and
identifies its logarithm exactly. Auxiliary to ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, line 1027. -/
theorem low_energy_cap_bound (etaLD w : ℝ) (hw : 0 < w)
    (hband : 6 * w ≤ etaLD) :
    1 / min w 1 ≤ max 1 (etaLD / 6) / w ∧
      log (1 / min w 1) = max (log (1 / w)) 0 := by
  by_cases hw1 : w ≤ 1
  · rw [min_eq_left hw1]
    refine ⟨div_le_div_of_nonneg_right (le_max_left _ _) hw.le, ?_⟩
    exact (max_eq_left (log_nonneg ((one_le_div hw).mpr hw1))).symm
  · rw [min_eq_right (le_of_not_ge hw1)]
    have hlog : log (1 / w) ≤ 0 :=
      log_nonpos (by positivity) ((div_le_one hw).mpr (le_of_not_ge hw1))
    refine ⟨?_, by simp only [div_one, log_one, max_eq_right hlog]⟩
    simpa only [div_one] using (one_le_div hw).mpr
      ((show w ≤ etaLD / 6 by linarith only [hband]).trans (le_max_right _ _))

/-- The capped logarithmic count gives an explicit bound in `log L / mu`.
Its bandwidth-dependent constant is visible, and the logarithmic correction
is retained. The count is an input to this scalar auxiliary and is constructed
in the physical family theorem. ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem low_energy_count_le_source_scale (L q : ℕ) (mu etaLD K D : ℝ)
    (hL : 2 ≤ L) (hq : 1 ≤ q) (hmu : 0 < mu) (hK : 0 ≤ K)
    (hband : 6 * (mu / (3 * log (L : ℝ))) ≤ etaLD)
    (hcount : let g := min (mu / (3 * log (L : ℝ))) 1
      log D ≤ K / g * (1 + log (q : ℝ) + log (1 / g)) ^ 3) :
    log D ≤ 3 * K * max 1 (etaLD / 6) * (log (L : ℝ) / mu) *
      (1 + log (q : ℝ) + max (log (3 * log (L : ℝ) / mu)) 0) ^ 3 := by
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  let w := mu / (3 * log (L : ℝ))
  have hw : 0 < w := by dsimp only [w]; positivity
  obtain ⟨hinv, hlog⟩ := low_energy_cap_bound etaLD w hw hband
  have hwInv : 1 / w = 3 * log (L : ℝ) / mu := by
    dsimp only [w]
    field_simp
  have hu : 0 ≤ 1 + log (q : ℝ) + log (1 / min w 1) := by
    have hqlog : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast hq)
    have hglog : 0 ≤ log (1 / min w 1) :=
      log_nonneg ((one_le_div (lt_min hw zero_lt_one)).mpr (min_le_right _ _))
    linarith only [hqlog, hglog]
  change log D ≤ K / min w 1 * (1 + log (q : ℝ) + log (1 / min w 1)) ^ 3 at hcount
  calc
    log D ≤ K * (1 / min w 1) * (1 + log (q : ℝ) + log (1 / min w 1)) ^ 3 := by
      simpa only [div_eq_mul_inv, one_mul] using hcount
    _ ≤ K * (max 1 (etaLD / 6) / w) *
        (1 + log (q : ℝ) + log (1 / min w 1)) ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hK)
        (pow_nonneg hu 3)
    _ = _ := by
      rw [hlog, hwInv]
      simp only [div_eq_mul_inv, one_mul] at hwInv ⊢
      rw [hwInv]
      ring

end Real
