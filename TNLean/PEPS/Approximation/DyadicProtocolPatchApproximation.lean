/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolCompression
import TNLean.PEPS.Approximation.DyadicProtocolConsequences

/-!
# Uniform polynomial PEPS approximation from Proposition 4.1

The consequences of Proposition 7.1 used in §8, with separate count, expansion and error
constants, follow from the adaptive patch constraint of Proposition 4.1
(`largeSizeDyadicProtocolBounds_of_adaptivePatchConstraint`), and §8 turns them into the
uniform polynomial PEPS approximation
(`polynomialPEPSApproximation_of_largeSizeDyadicProtocolBounds`). Composing the two leaves
Proposition 4.1 as the only hypothesis of Theorem 1.1.

* `polynomialPEPSApproximation_of_adaptivePatchConstraint` : Theorem 1.1 from Proposition 4.1.

## References

* Polynomial-PEPS manuscript (September 24, 2026): Theorem 1.1 (`00-introduction.tex`,
  lines 36–57), Proposition 4.1 (`03-patches.tex`, lines 26–49), Proposition 7.1
  (`06-geometry.tex`, lines 12–53 and 559–681), and §8 (`07-assembly.tex`, lines 9–214).
-/

namespace TNLean.PEPS.Approximation

/-- **Theorem 1.1 from Proposition 4.1.** The adaptive patch constraint of Proposition 4.1
implies the uniform polynomial PEPS approximation of gapped square-grid ground states.

This is a conditional form of Theorem 1.1: Proposition 4.1 is a hypothesis.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Theorem 1.1 `thm:main`,
`00-introduction.tex:36–57`, with Proposition 4.1 (`03-patches.tex:26–49`), Proposition 7.1
(`06-geometry.tex:12–53, 559–681`) and its use in §8 (`07-assembly.tex:9–214`). -/
theorem polynomialPEPSApproximation_of_adaptivePatchConstraint
    (hpatch : AdaptivePatchConstraint) : PolynomialPEPSApproximation :=
  polynomialPEPSApproximation_of_largeSizeDyadicProtocolBounds
    (largeSizeDyadicProtocolBounds_of_adaptivePatchConstraint hpatch)

end TNLean.PEPS.Approximation
