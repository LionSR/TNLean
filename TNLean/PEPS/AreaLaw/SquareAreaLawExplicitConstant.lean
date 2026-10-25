/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawElementaryConstant
import TNLean.PEPS.Approximation.RangeSquareGroundState

/-!
# The square-grid area law with an explicit constant

The square-grid entropy area law of the polynomial-PEPS manuscript (Proposition 2.1) is the
range-one, equal-side specialization of the area law. Read with interactions of range `R`, it
holds for the unit gapped ground vectors of range-`R` Hamiltonians on the `L × L` square at the
closed-form constant `uniformAreaLawConstantClosed q R J Δ` and at the elementary constant
`uniformAreaLawConstantElementary q R J Δ` of the area law at range `R`, with no hypothesis
beyond `q ≥ 1`, `J ≥ 0` and `Δ > 0`. The nearest-neighbour statement is the range-one case.

These are auxiliary results: the polynomial-PEPS manuscript treats only nearest-neighbour
interactions, Proposition 2.1 asserts only that a constant exists, and
`squareEntropyAreaLaw` is that statement.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), and *A two-dimensional area law from a
global spectral gap*, proof of Theorem 1.1 (`10-geometry.tex`, lines 803–857), at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

open Approximation

/-- **The square-grid area law at range `R` at the closed-form constant.** For `q ≥ 1`,
`J ≥ 0` and `Δ > 0`, the square-grid entropy area law holds for the unit gapped ground vectors
of range-`R` Hamiltonians on the `L × L` square with the constant
`uniformAreaLawConstantClosed q R J Δ` of the area law at range `R`.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), read with
interactions of range `R`, with the constant of the proof of area-law Theorem 1.1
(`10-geometry.tex`, lines 803–857). -/
theorem squareEntropyAreaLawAt_range_closed (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    SquareEntropyAreaLawAt q (IsRangeSquareGroundState q R J Δ)
      (uniformAreaLawConstantClosed q R J Δ) :=
  squareEntropyAreaLawAt_range_of_areaLawBound (uniformAreaLaw_closed q R hq hJ hΔ).1
    (uniformAreaLaw_closed q R hq hJ hΔ).2

/-- **The square-grid area law at range `R` at the elementary constant.** For `q ≥ 1`,
`J ≥ 0` and `Δ > 0`, the square-grid entropy area law holds for the unit gapped ground vectors
of range-`R` Hamiltonians on the `L × L` square with the constant
`uniformAreaLawConstantElementary q R J Δ`, which iterates no recursion.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), read with
interactions of range `R`, with the constant of the proof of area-law Theorem 1.1
(`10-geometry.tex`, lines 803–857). -/
theorem squareEntropyAreaLawAt_range_elementary (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    SquareEntropyAreaLawAt q (IsRangeSquareGroundState q R J Δ)
      (uniformAreaLawConstantElementary q R J Δ) :=
  squareEntropyAreaLawAt_range_of_areaLawBound (uniformAreaLaw_elementary q R hq hJ hΔ).1
    (uniformAreaLaw_elementary q R hq hJ hΔ).2

/-- **The square-grid area law at the closed-form constant.** For `q ≥ 1`, `J ≥ 0` and
`Δ > 0`, the square-grid entropy area law holds at `q, J, Δ` with the constant
`uniformAreaLawConstantClosed q 1 J Δ` of the range-one area law. This is the range-one case of
`squareEntropyAreaLawAt_range_closed`.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), with the
constant of the proof of area-law Theorem 1.1 (`10-geometry.tex`, lines 803–857). -/
theorem squareEntropyAreaLawAt_closed {q : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    SquareEntropyAreaLawAt q (IsSquareGroundState q J Δ)
      (uniformAreaLawConstantClosed q 1 J Δ) :=
  (squareEntropyAreaLawAt_range_closed q 1 hq hJ hΔ).mono
    fun _ _ hΩ ↦ hΩ.isRangeSquareGroundState

end TNLean.PEPS.AreaLaw
