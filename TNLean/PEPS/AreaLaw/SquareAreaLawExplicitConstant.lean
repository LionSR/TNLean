/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawExplicitConstant
import TNLean.PEPS.Approximation.OriginalNestedPatchEntropy

/-!
# The square-grid area law with an explicit constant

The square-grid entropy area law of the polynomial-PEPS manuscript (Proposition 2.1) is the
range-one, equal-side specialization of the area law. At the closed-form constant
`uniformAreaLawConstantClosed q 1 J Δ` of the range-one area law, it holds with no hypothesis
beyond `q ≥ 1`, `J ≥ 0` and `Δ > 0`.

This is an auxiliary result: Proposition 2.1 asserts only that a constant exists, and
`squareEntropyAreaLaw` is that statement.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), and *A two-dimensional area law from a
global spectral gap*, proof of Theorem 1.1 (`10-geometry.tex`, lines 803–857), at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- **The square-grid area law at the closed-form constant.** For `q ≥ 1`, `J ≥ 0` and
`Δ > 0`, the square-grid entropy area law holds at `q, J, Δ` with the constant
`uniformAreaLawConstantClosed q 1 J Δ` of the range-one area law.
Source: polynomial-PEPS Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), with the
constant of the proof of area-law Theorem 1.1 (`10-geometry.tex`, lines 803–857). -/
theorem squareEntropyAreaLawAt_closed {q : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    Approximation.SquareEntropyAreaLawAt q (Approximation.IsSquareGroundState q J Δ)
      (uniformAreaLawConstantClosed q 1 J Δ) := by
  obtain ⟨hC, hbound⟩ := uniformAreaLaw_closed q 1 hq hJ hΔ
  exact ⟨hC, fun _ _ ⟨h, _, hΩ⟩ A ↦
    Approximation.finiteProductEntropy_le_of_areaLawBound hJ hbound h hΩ A⟩

end TNLean.PEPS.AreaLaw
