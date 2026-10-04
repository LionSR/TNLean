/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBS
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric localization of the PVBS boundary particle

The exact amplitudes give exponential decay from the left boundary for `‖q‖ < 1`.
For `1 < ‖q‖`, amplitudes relative to the rightmost particle decay exponentially
with distance from the right boundary. These are the two boundary regimes of
Bachmann and Nachtergaele, arXiv:1112.4097, Section II, equation (8).
-/

open Filter Topology

namespace MPSTensor

/-- Absolute one-particle amplitudes are geometric in their distance from the left edge. -/
theorem norm_pvbsEdge_excitedAt (q : ℂ) (N : ℕ) (k : Fin N) :
    ‖pvbsEdge q N (excitedAt N k)‖ = ‖q‖ ^ k.val := by
  rw [pvbsEdge_excitedAt, norm_pow]

/-- In the left-boundary regime, the amplitude at distance `k` tends to zero. -/
theorem pvbsEdge_left_decay (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun k : ℕ => pvbsEdge q (k + 1) (excitedAt (k + 1) (Fin.last k)))
      atTop (𝓝 0) := by
  simpa only [pvbsEdge_excitedAt, Fin.val_last] using
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq

/-- Relative to the last-site amplitude, a particle `k` sites from the right edge
has amplitude `q⁻ᵏ`, independently of the number of sites to its left. -/
theorem pvbsEdge_right_relative (q : ℂ) (hq : q ≠ 0) (n k : ℕ) :
    pvbsEdge q (n + k + 1) (excitedAt (n + k + 1) ⟨n, by omega⟩) /
      pvbsEdge q (n + k + 1) (excitedAt (n + k + 1) (Fin.last (n + k))) =
        (q⁻¹) ^ k := by
  simp only [pvbsEdge_excitedAt, Fin.val_last, pow_add, inv_pow]
  field_simp

/-- In the right-boundary regime, the relative amplitude decays with distance
from the right edge. -/
theorem pvbsEdge_right_decay (q : ℂ) (hq : 1 < ‖q‖) (n : ℕ) :
    Tendsto (fun k : ℕ =>
      pvbsEdge q (n + k + 1) (excitedAt (n + k + 1) ⟨n, by omega⟩) /
        pvbsEdge q (n + k + 1) (excitedAt (n + k + 1) (Fin.last (n + k))))
      atTop (𝓝 0) := by
  have hq0 : q ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hq)
  simp only [pvbsEdge_right_relative q hq0]
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ hq

end MPSTensor
