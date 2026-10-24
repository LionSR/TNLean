/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.RangeSquareGroundState

/-!
# Polynomial PEPS approximation at interaction range `R`

The polynomial-PEPS manuscript proves its Theorem 1.1 for site and nearest-neighbour
interactions. This file states the same conclusion for interactions of range `R`: for every
`q ≥ 2`, `R ≥ 1` and `J, Δ > 0` there are `C, c > 0` such that every unit gapped ground vector
of a range-`R` Hamiltonian on the `L × L` square, `L ≥ 2`, is within `L⁻¹` of a normalized PEPS
of bond dimension at most `C L^c`, up to a global phase. It is an extension of the source; its
range-one case contains the nearest-neighbour theorem.

## Main definitions and results

* `RangePolynomialPEPSApproximation`: the range-`R` target.
* `polynomialPEPSApproximation_of_range`: the range-`R` target implies the nearest-neighbour
  target `PolynomialPEPSApproximation`, through its range-one case.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 1.1 (`00-introduction.tex`, lines 36–57), read with interactions of range `R` as in
*A two-dimensional area law from a global spectral gap*, Theorem 1.1, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The polynomial-PEPS target at interaction range `R`, with constants chosen before the grid
size, the Hamiltonian and the ground vector: for `q ≥ 2`, `R ≥ 1` and `J, Δ > 0` there are
`C, c > 0` such that every ground vector of the range-`R` family on the square of side `L ≥ 2`
has a PEPS approximation with bond dimensions at most `C L^c` and error at most `L⁻¹`.
No proof of the target is asserted here.

Source: polynomial-PEPS Theorem 1.1 (`00-introduction.tex`, lines 36–57), read with
interactions of range `R` as in area-law Theorem 1.1. -/
def RangePolynomialPEPSApproximation : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ R : ℕ, 1 ≤ R → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ L : ℕ, 2 ≤ L → ∀ Ω : StateSpace L q,
        IsRangeSquareGroundState q R J Δ L Ω → HasPEPSApproximation C c L q Ω

/-- The range-`R` polynomial-PEPS target implies the nearest-neighbour target of the source:
every gapped ground vector of a square-grid Hamiltonian is a ground vector at range one, so the
constants of the range-one case serve.

Source: polynomial-PEPS Theorem 1.1 (`00-introduction.tex`, lines 36–57) and `eq:model`
(lines 40–45). -/
theorem polynomialPEPSApproximation_of_range (h : RangePolynomialPEPSApproximation) :
    PolynomialPEPSApproximation := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, c, hC, hc, happrox⟩ := h q hq 1 le_rfl J Δ hJ hΔ
  exact ⟨C, c, hC, hc, fun L hL H E₀ Ω hgap ↦
    happrox L hL Ω (IsSquareGroundState.isRangeSquareGroundState ⟨H, E₀, hgap⟩)⟩

end TNLean.PEPS.Approximation
