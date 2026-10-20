# The polynomial PEPS approximation as a corollary of its explicit form

Theorem 1.1 of the polynomial-PEPS manuscript, `polynomialPEPSApproximation` in
`TNLean/PEPS/Approximation/PolynomialPEPSTheorem.lean`, is now proved from
`polynomialPEPSApproximation_explicit` (`PolynomialPEPSClosedConstant.lean`), with the bond
prefactor `pepsBondPrefactor q J Δ` and the bond exponent `pepsBondExponent q J Δ`. Before this
change it was proved along an existential route: the square entropy area law gave the adaptive
patch constraint of Proposition 4.1, that constraint gave protocol bounds with existential
constants, and a large-size network proposition with existential constants gave the uniform
approximation. After the change, no proof uses that route, and it is removed here.

## Import order

`TNLean.PEPS.Approximation.PolynomialPEPSExplicitConstant` used to import
`TNLean.PEPS.Approximation.ApproximationFromSquareAreaLaw`. It now imports the three modules
that the removed modules imported: `AdaptivePatchConstraintFromAreaLaw`,
`DyadicProtocolCompression` and `DyadicProtocolConsequences`. `PolynomialPEPSTheorem` drops its
import of `ApproximationFromSquareAreaLaw`; it reaches the same modules through
`PolynomialPEPSClosedConstant`.

## Removed modules

| Removed | Content | Replacement |
|---|---|---|
| `TNLean/PEPS/Approximation/ApproximationFromSquareAreaLaw.lean` | `polynomialPEPSApproximation_of_squareEntropyAreaLaw` | `polynomialPEPSApproximation_of_ratios` (`PolynomialPEPSExplicitConstant.lean`) |
| `TNLean/PEPS/Approximation/DyadicProtocolPatchApproximation.lean` | `polynomialPEPSApproximation_of_adaptivePatchConstraint` | `polynomialPEPSApproximation_of_ratios` |
| `TNLeanTest/PEPS/Approximation/ApproximationFromSquareAreaLawAxioms.lean` | axiom test of the first module | none |
| `TNLeanTest/DyadicProtocolPatchApproximationAxioms.lean` | axiom test of the second module | none |

## Removed declarations

| Removed | File | Reason | Replacement |
|---|---|---|---|
| `polynomialPEPSApproximation_of_squareEntropyAreaLaw` | `ApproximationFromSquareAreaLaw.lean` | No user | `polynomialPEPSApproximation_of_ratios` |
| `polynomialPEPSApproximation_of_adaptivePatchConstraint` | `DyadicProtocolPatchApproximation.lean` | Its only user was the theorem above | `polynomialPEPSApproximation_of_ratios` |
| `polynomialPEPSApproximation_of_largeSizeDyadicProtocolBounds` | `DyadicProtocolCompression.lean` | Its users were the theorem above and the next one | `polynomialPEPSApproximation_of_ratios` |
| `polynomialPEPSApproximation_of_largeSizeDyadicProtocolConsequences` | `DyadicProtocolCompression.lean` | No user | `polynomialPEPSApproximation_of_ratios` |
| `largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolBounds` | `DyadicProtocolCompression.lean` | Its users were the removed theorems of this file | `dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt` (same file) |
| `largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences` | `DyadicProtocolCompression.lean` | No user | `dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt` |
| `polynomialPEPSApproximation_of_largeSizeDyadicOperatorNetwork` | `GroundStateApproximation.lean` | Its only user was `polynomialPEPSApproximation_of_largeSizeDyadicProtocolBounds` | `hasPEPSApproximation_of_dyadicOperatorNetworkAt` (same file) with the small sizes in `polynomialPEPSApproximation_explicit` |
| `LargeSizeDyadicOperatorNetwork` | `GroundStateApproximation.lean` | Its users were the removed theorems | `DyadicOperatorNetworkAt` (same file) |

All declarations are in the namespace `TNLean.PEPS.Approximation`. The axiom tests
`TNLeanTest/PEPS/Approximation/PolynomialPEPSTheoremAxioms.lean` and
`TNLeanTest/PEPS/Approximation/PolynomialPEPSExplicitConstantAxioms.lean` no longer list the
removed theorems. No compatibility alias is kept.

## Blueprint

The removed theorems were auxiliary results, not source-labelled formalizations. The entries
whose only declarations were removed are deleted: `thm:peps_approximation_of_square_area_law`
(`ch24_peps_adaptive_patch_bridge.tex`), `cor:peps_ground_state_approximation_from_protocol`
and `thm:peps_ground_state_approximation_from_patch_bound`
(`ch34_peps_exact_finite_exception.tex`). The entries
`def:peps_large_size_dyadic_operator_network`,
`thm:peps_ground_state_approximation_conditional` and
`thm:peps_large_size_network_from_protocol` keep their labels and now state the forms at given
constants of their surviving declarations. The proof of `thm:openai_polynomial_peps` no longer
cites the removed entry.

## Kept declarations

Proposition 4.1 and Proposition 7.1 (`adaptivePatchConstraint`,
`largeSizeDyadicProtocolConsequences`, `largeSizeDyadicProtocol_of_le`,
`largeSizeDyadicProtocolBounds`) are source statements and are kept, together with
`largeSizeDyadicProtocolBounds_of_adaptivePatchConstraint` and the propositions
`LargeSizeDyadicProtocolConsequences` and `LargeSizeDyadicProtocolBounds`.
`polynomialPEPSApproximation_iff_sufficiently_large` (`ExactFiniteException.lean`) loses its
only proof user but keeps its blueprint entry `thm:peps_approximation_iff_large` and its test,
and is kept.
