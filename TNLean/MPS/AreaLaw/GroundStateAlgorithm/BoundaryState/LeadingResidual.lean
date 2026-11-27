/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BoundaryState.ViableLeadingBounds
import QICLean.Spectral.Gap.CodimensionOneGap
import QICLean.Spectral.Filter.DensityPowerIteration

/-!
# Residual certification for the LVV leading vector

The trace-one constraint separates a density matrix eigenvalue above one half from the
rest of the spectrum.  The residual certificate of the leading eigenvector,
`Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_residual_le`, is applied here at the
LVV vector tolerance.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`,
lines 493--505.

It also contains the following results.

* `TNLean.MPS.AreaLaw.lvvPower_iterationCount_lt`,
  `TNLean.MPS.AreaLaw.lvvPower_totalIterationCount_lt`: iteration counts at the LVV residual
  tolerance.
-/

section LeadingResidual

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- At the LVV vector tolerance `Δ / (16224 L)`, the sufficient residual tolerance
`11 / 24` times the vector tolerance is `11 Δ / (389376 L)`. -/
theorem residual_precision_of_lvv_vector_tolerance
    {L : ℕ} (hL : 0 < L) {Δ r : ℝ}
    (hr : r ≤ 11 * Δ / (389376 * L)) :
    r ≤ (11 / 24) * (Δ / (16224 * L)) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have heq :
      (11 : ℝ) * Δ / (389376 * L) = (11 / 24) * (Δ / (16224 * L)) := by
    field_simp [hL0]
    ring
  rwa [← heq]

/-- The explicit LVV spectral tolerance: for a positive chain length, a residual at
most `11 Δ / (389376 L)` produces an exact unit leading eigenvector within
`Δ / (16224 L)` of the numerical unit vector. -/
theorem Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_lvv_residual
    {n : Type*} [Fintype n] [DecidableEq n]
    {L : ℕ} (hL : 0 < L) {Δ : ℝ} (hΔ : 0 < Δ)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ)
    (hres : ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ 11 * Δ / (389376 * L)) :
    ∃ v : EuclideanSpace ℂ n,
      ‖v‖ = 1 ∧
      σ *ᵥ WithLp.ofLp v = (μ : ℂ) • WithLp.ofLp v ∧
      ‖z - v‖ ≤ Δ / (16224 * L) ∧
      ∃ θ : ℝ, v = Complex.exp (θ * Complex.I) • u := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hζ : 0 ≤ Δ / (16224 * L) :=
    (div_pos hΔ (mul_pos (by norm_num) hLreal)).le
  apply Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_residual_le
    hσ htr hu hz huσ hμ hζ
  exact residual_precision_of_lvv_vector_tolerance hL hres

end TNLean.MPS.AreaLaw

end LeadingResidual

section LeadingPower

/-!
## Iteration counts at the LVV residual tolerance

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

end LeadingPower
