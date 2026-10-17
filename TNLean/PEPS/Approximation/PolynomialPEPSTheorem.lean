/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximationFromSquareAreaLaw
import TNLean.PEPS.AreaLaw.AreaLawTheorem

/-!
# Polynomial PEPS approximation of gapped square-grid ground states

Theorem 1.1 of the polynomial-PEPS manuscript: for every local dimension
`q ≥ 2` and all `J, Δ > 0` there are constants `C, c > 0` such that every
gapped ground state of a nearest-neighbor Hamiltonian on the `L × L` grid is
approximated in trace norm by a PEPS of bond dimension polynomial in `L`.
The square entropy area law it consumes (Proposition 2.1 of the same
manuscript) is the square-grid specialization of the two-dimensional area law.

## Main results

* `adaptivePatchConstraint`: Proposition 4.1, the adaptive patch constraint.
* `polynomialPEPSApproximation`: Theorem 1.1.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 36–57),
  Proposition 2.1 (`01-preliminaries.tex`, lines 39–58) and Proposition 4.1
  (`03-patches.tex`, lines 26–603). Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 39–53).

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- Proposition 4.1 of the polynomial-PEPS manuscript, `03-patches.tex`,
lines 26–49 (proof lines 51–603): adaptive square patches with polynomially
many cylinder terms around every center and at every logarithmic radius. The
square entropy area law used in its proof is supplied by the two-dimensional
area law. -/
theorem adaptivePatchConstraint : AdaptivePatchConstraint :=
  AreaLaw.squareEntropyAreaLaw.adaptivePatchConstraint

/-- Theorem 1.1 of the polynomial-PEPS manuscript, `00-introduction.tex`,
lines 36–57: gapped ground states of nearest-neighbor Hamiltonians on the
`L × L` grid have trace-norm PEPS approximations of polynomial bond dimension,
with constants depending only on `q`, `J` and `Δ`. The square entropy area law
of Proposition 2.1 (`01-preliminaries.tex`, lines 39–58) is supplied by the
two-dimensional area law. -/
theorem polynomialPEPSApproximation : PolynomialPEPSApproximation :=
  polynomialPEPSApproximation_of_squareEntropyAreaLaw AreaLaw.squareEntropyAreaLaw

end TNLean.PEPS.Approximation
