/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GappedGroundState
import TNLean.PEPS.AreaLaw.Amplification.EntropyComparison

/-!
# Marginal trace norm from the original full-system gap

The marginals of a unit vector with small excess energy are close to those of
the original unit ground vector. The bound uses the original full-system gap
and the full trace norm of the difference of the reduced density matrices.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 320–365,
`eq:patch-energy-bound`, `eq:patch-kappa-choice`, and
`eq:patch-marginal-closeness`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped InnerProductSpace Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- A unit vector with small excess energy has close marginals to the original
unit ground vector. The left side is the full trace norm of the difference.
The Hamiltonian and gap are those of the full system.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 320–365,
`eq:patch-energy-bound`, `eq:patch-kappa-choice`, `eq:patch-marginal-closeness`,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem re_trace_abs_reducedPure_sub_le_sqrt_energy
    {H : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    {E₀ Δ : ℝ} {Ω φ : EuclideanSpace ℂ ((v : V) → β v)}
    (hgs : Matrix.IsGappedGroundState H E₀ Ω Δ) (hΔ : 0 < Δ)
    (hφ : ‖φ‖ = 1) (R : Finset V) :
    (CFC.abs (reducedPure β φ R - reducedPure β Ω R)).trace.re ≤
      2 * Real.sqrt (((⟪φ, Matrix.toEuclideanLin H φ⟫_ℂ).re - E₀) / Δ) := by
  refine (div_le_iff₀' (show (0 : ℝ) < 2 from zero_lt_two)).mp
    ((traceDistance_reducedPure_le β φ Ω hφ hgs.1 R).trans
      ((Matrix.traceDistance_vecMulVec_eq hφ hgs.1).le.trans
        (Real.sqrt_le_sqrt ((le_div_iff₀' hΔ).2 ?_))))
  simpa only [hφ, one_pow, mul_one, norm_inner_symm (𝕜 := ℂ) Ω φ] using
    Matrix.PosSemidef.gap_le (Ω := Ω) hgs.2.2 φ

/-- An energy excess at most one 1024th of the original spectral gap gives
full marginal trace norm at most one sixteenth. This is an auxiliary energy
criterion, with no lower bound on any local dimension.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 339–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem re_trace_abs_reducedPure_sub_le_one_sixteenth_of_energy
    {H : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    {E₀ Δ : ℝ} {Ω φ : EuclideanSpace ℂ ((v : V) → β v)}
    (hgs : Matrix.IsGappedGroundState H E₀ Ω Δ) (hΔ : 0 < Δ)
    (hφ : ‖φ‖ = 1)
    (henergy : (⟪φ, Matrix.toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ Δ / 1024)
    (R : Finset V) :
    (CFC.abs (reducedPure β φ R - reducedPure β Ω R)).trace.re ≤ (1 / 16 : ℝ) := by
  refine (re_trace_abs_reducedPure_sub_le_sqrt_energy β hgs hΔ hφ R).trans
    ((le_div_iff₀' (show (0 : ℝ) < 2 from zero_lt_two)).mp ?_)
  norm_num [Real.sqrt_le_iff, div_le_iff₀' hΔ]
  linarith

end FiniteProduct
