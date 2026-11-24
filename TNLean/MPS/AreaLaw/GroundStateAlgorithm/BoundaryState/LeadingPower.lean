/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BoundaryState.LeadingResidual
import QICLean.Spectral.Filter.DensityPowerIteration

/-!
# Iteration counts at the LVV residual tolerance

The residual tolerance in the LVV leading-vector procedure depends on the
chain length and the spectral gap. Substituting it into the coordinate-start
power method gives bounds on both the number of iterations per start and the
total number of matrix-vector products.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
lines 477–478 and 493–505.
-/

namespace TNLean.MPS.AreaLaw

/-- At the LVV residual tolerance, the elementary power-iteration count is bounded by an
explicit polynomial in the compressed dimension, the chain length, and the inverse gap.
This is the counting part of the leading-vector runtime estimate in LVV13,
`algo53.tex`, lines 477--478 and 493--505. -/
theorem lvvPower_iterationCount_lt (n L : ℕ) (hL : 0 < L)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    let η := 11 * Δ / (778752 * L)
    let t := ⌈(n : ℝ) / η ^ 2⌉₊
    (t : ℝ) < (n : ℝ) * (778752 * L : ℝ) ^ 2 / (11 * Δ) ^ 2 + 1 := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hη : 0 < 11 * Δ / (778752 * L) := by positivity
  have harg : 0 ≤ (n : ℝ) / (11 * Δ / (778752 * L)) ^ 2 := by positivity
  calc
    (⌈(n : ℝ) / (11 * Δ / (778752 * L)) ^ 2⌉₊ : ℝ)
        < (n : ℝ) / (11 * Δ / (778752 * L)) ^ 2 + 1 :=
          Nat.ceil_lt_add_one harg
    _ = (n : ℝ) * (778752 * L : ℝ) ^ 2 / (11 * Δ) ^ 2 + 1 := by
      field_simp

/-- Trying all `n` deterministic coordinate starts uses fewer than `n` times the explicit
single-start iteration budget.  Thus the number of dense matrix-vector applications in
the LVV leading-vector stage is polynomial once a compressed density is given. -/
theorem lvvPower_totalIterationCount_lt (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    let η := 11 * Δ / (778752 * L)
    let t := ⌈(n : ℝ) / η ^ 2⌉₊
    ((n * t : ℕ) : ℝ) <
      (n : ℝ) * ((n : ℝ) * (778752 * L : ℝ) ^ 2 / (11 * Δ) ^ 2 + 1) := by
  have ht := lvvPower_iterationCount_lt n L hL hΔ
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  simpa only [Nat.cast_mul] using mul_lt_mul_of_pos_left ht hnreal

end TNLean.MPS.AreaLaw
