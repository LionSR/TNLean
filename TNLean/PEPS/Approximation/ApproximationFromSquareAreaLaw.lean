/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchConstraintFromAreaLaw
import TNLean.PEPS.Approximation.DyadicProtocolPatchApproximation

/-!
# Polynomial PEPS approximation from the square entropy area law

The polynomial-PEPS theorem follows from the square-grid entropy area law,
through the adaptive patch constraint of Proposition 4.1.

**Scope restriction (conditional area law):** the theorem assumes the square
entropy area law explicitly. Its deduction from the spectral-gap hypotheses is
the separate area-law problem described in
`docs/paper-gaps/arealaw2d_rectangular_specialization_scope.tex`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 36–57),
  Proposition 2.1 (`01-preliminaries.tex`, lines 39–58) and Proposition 4.1
  (`03-patches.tex`, lines 26–603). Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- Theorem 1.1 of the polynomial-PEPS manuscript, assuming the square entropy
area law of its Proposition 2.1. Source: `00-introduction.tex`, lines 36–57,
with Proposition 4.1 (`03-patches.tex`, lines 26–603) deduced from the area law. -/
theorem polynomialPEPSApproximation_of_squareEntropyAreaLaw
    (harea : SquareEntropyAreaLaw) : PolynomialPEPSApproximation :=
  polynomialPEPSApproximation_of_adaptivePatchConstraint harea.adaptivePatchConstraint

end TNLean.PEPS.Approximation
