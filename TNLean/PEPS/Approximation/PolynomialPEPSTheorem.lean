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
within `L⁻¹`, up to a global phase and in the Euclidean norm of the normalized
vector, of a PEPS of bond dimension polynomial in `L`.
The square entropy area law it consumes (Proposition 2.1 of the same
manuscript) is the square-grid specialization of the two-dimensional area law.

## Main results

* `adaptivePatchConstraint`: Proposition 4.1, the adaptive patch constraint.
* `largeSizeDyadicProtocolConsequences`: Proposition 7.1, the distribution protocol.
* `polynomialPEPSApproximation`: Theorem 1.1.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1 (`00-introduction.tex`, lines 36–57),
  Proposition 2.1 (`01-preliminaries.tex`, lines 39–58), Proposition 4.1
  (`03-patches.tex`, lines 26–603) and Proposition 7.1 (`06-geometry.tex`,
  lines 12–53 and 559–681). Source revision:
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

/-- Proposition 7.1 of the polynomial-PEPS manuscript, `06-geometry.tex`, lines 12–53 (proof
lines 559–681): for all sufficiently large `L`, with constants uniform in the Hamiltonian and in
`L`, there is a protocol distributing the gapped ground vector through the padded dyadic
hierarchy with the four items of the proposition, at patch and information power `60`
(`07-assembly.tex`, line 11). -/
theorem largeSizeDyadicProtocolConsequences : LargeSizeDyadicProtocolConsequences :=
  largeSizeDyadicProtocolConsequences_of_adaptivePatchConstraint adaptivePatchConstraint

/-- Theorem 1.1 of the polynomial-PEPS manuscript, `00-introduction.tex`,
lines 36–57: gapped ground states of nearest-neighbor Hamiltonians on the
`L × L` grid are within `L⁻¹` of normalized PEPS vectors of polynomial bond
dimension, up to a global phase,
with constants depending only on `q`, `J` and `Δ`. The square entropy area law
of Proposition 2.1 (`01-preliminaries.tex`, lines 39–58) is supplied by the
two-dimensional area law. -/
theorem polynomialPEPSApproximation : PolynomialPEPSApproximation :=
  polynomialPEPSApproximation_of_squareEntropyAreaLaw AreaLaw.squareEntropyAreaLaw

end TNLean.PEPS.Approximation
