# Promoted-pattern hygiene: matrix-unit spans, square-root inverses, explicit gauge inverses (2026-09-19)

Three proof-body cleanups. One new shared helper is added,
`Complex.ofReal_sqrt_inv_mul_self` in `TNLean/Algebra/ComplexSqrt.lean`; no
existing statement changes, no blueprint `\lean{}` tag is redirected, and only
two private declarations are removed. The removals follow the direct-removal
policy in `docs/project_conventions.md`: both are private, both had a single
use, and neither name encoded misleading terminology.

## 1. Nine inline copies of the promoted matrix-unit span helper

`Submodule.eq_top_of_forall_single_mem` (`TNLean/Algebra/MatrixSingleSpan.lean`)
was promoted on 2026-09-17 as the closing step of a normality or injectivity
certificate: a submodule of matrices containing every matrix unit is the whole
space. Nine further certificates still carried the helper's own proof inline,
expanding a matrix as the sum of its entries against the matrix units and
closing each summand by `Submodule.smul_mem`.

| Module | Certificate |
|---|---|
| `TNLean/PEPS/TorusRowColumnReductionObstruction.lean` | `Aunits_isInjective` |
| `TNLean/MPS/FundamentalTheorem/Reduction/Examples/Zsqrt2Ring.lean` | `MPSTensor.isNormal_of_single_eq_smul_zsqrt2` |
| `TNLean/MPS/FundamentalTheorem/Reduction/Examples/GoldenCompression.lean` | `MPSTensor.isNormal_of_golden_single` |
| `TNLean/MPS/FundamentalTheorem/Reduction/Examples/OneSlotGauge.lean` | `MPSTensor.isNBlkInjective_two_of_int` |
| `TNLean/MPS/RFP/BellPairCIDObstruction.lean` | `MPSTensor.bellPairChainTensor_isInjective` |
| `TNLean/MPS/MPDO/CZXTensorInjectivity.lean` | `MPOTensor.CZX.tensor_isInjective` |
| `TNLean/MPS/MPDO/BondTwoSingletonGramBoundary.lean` | `MPOTensor.BondTwoSingletonGramBoundary.singletonTensor_isInjective` |
| `TNLean/MPS/MPDO/BiCFDerivation/DiagonalRestrictionCounterexample.lean` | `diagonalRestrictionUnits_isInjective` (private) |
| `TNLean/MPS/MPDO/PositiveMinimalRealizationCounterexample.lean` | `MPSTensor.PositiveMinimalRealizationCounterexample.tensor_isInjective` |

Each now ends in one application of the helper, and each file gains the import
of `TNLean.Algebra.MatrixSingleSpan`. The last of the nine expanded the sum over
a two-by-two index by hand rather than through `Matrix.matrix_eq_sum_single`;
it is the same closing step and is folded in here.

Seven of the nine already carried the matrix-unit hypothesis in the form the
helper expects. The Bell-pair certificate produced the matrix unit from the
rescaled letter inside the summand instead, so its rescaling step moved above
the helper application and now produces the unrescaled unit directly.

`docs/tactic_patterns.md` recorded on 2026-09-17 that every call site of this
pattern had been refactored. That was wrong for the nine sites above; the entry
now records the sweep and the corrected claim.

## 2. One owner for the inverse of a real square root in the complex numbers

`TNLean/Algebra/ComplexSqrt.lean` owns the square identity
`(↑(√x))² = x`. Six example and counterexample modules each proved the companion
inverse identity privately, in six different spellings of `1/√2`. The new owner
lemma `Complex.ofReal_sqrt_inv_mul_self` states it once for a nonnegative real,
and the six private lemmas keep their statements and spellings with one- or
two-line bodies.

| Module | Private lemma now reusing the owner |
|---|---|
| `TNLean/MPS/Examples/Cluster.lean` | `MPSTensor.inv_sqrt2_sq` |
| `TNLean/MPS/Examples/EvenParity.lean` | `MPSTensor.inv_sqrt2_mul_self` |
| `TNLean/MPS/Examples/MajumdarGhosh.lean` | `MPSTensor.inv_ofReal_sqrt2_mul_self` |
| `TNLean/MPS/MPDO/LocalPurificationRFP.lean` | `MPOTensor.sqrt2_inv_mul_self` (private) |
| `TNLean/MPS/MPDO/CaseIIAbsorptionCounterexample.lean` | `MPOTensor.CaseIIAbsorptionCounterexample.invSqrtTwo_mul_self` |
| `TNLean/MPS/RFP/CPSVCIDNotRFPExample.lean` | `MPSTensor.cpsvExample34_invSqrtTwo_sq` |

Retained deliberately: the three private constants naming `1/√2`
(`MPOTensor.TwistedDimer.invSqrt2` is real-valued, the other two are complex and
each has some twenty use sites), and the nine general-`d` `sourceSqrt`
cancellations of `TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean`, which are
consumed as rewrite rules in fixed associativity shapes and two of which carry
source citations.

## 3. Two gauges that recomputed their own inverse

`TNLean/MPS/MPDO/BondTwoSingletonGramBoundary.lean` and
`TNLean/MPS/MPDO/PositiveMinimalRealizationCounterexample.lean` each built a
concrete two-by-two gauge through
`Matrix.GeneralLinearGroup.mkOfDetNeZero`, then recovered its inverse
coordinate by building a second `mkOfDetNeZero` for the inverse matrix, proving
the product is one through `Units.ext`, and rewriting with
`inv_eq_of_mul_eq_one_right`. Both now carry the inverse in the unit itself, so
both coordinate lemmas are `rfl`.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.BondTwoSingletonGramBoundary.gaugeMatrix_det_ne_zero` (private) | `gaugeMatrix_mul_inv` (private), the entrywise product identity supplying both unit fields through `mul_eq_one_comm` |
| `MPSTensor.PositiveMinimalRealizationCounterexample.gaugeMatrix_det_ne_zero` (private) | `gaugeMatrix_mul_inv` (private), likewise |

`gauge`, `gaugeMatrix`, `gauge_val` and `gauge_inv_val` keep their names,
statements and mathematical content in both modules, so the blueprint entries
naming the singleton gauge and its matrix are untouched. The cross-module
consumers of `gauge_inv_val` see the same statement.

Retained: the seven `mkOfDetNeZero` gauges in `TNLean/MPS/Examples/`, where the
involution product lemmas survive for other consumers and the saving is at most
one or two lines, and the two renormalization fixed-point uses on an abstract
matrix with only a determinant hypothesis, where the explicit-inverse form does
not apply.

## What was checked

The whole library builds. Every edited module and its importers elaborate under
the package linter options. No `sorry`, `axiom` or `native_decide` is
introduced. No blueprint tag names a removed declaration.

## Deferred (both landed 2026-09-23)

`MPOTensor.sourceSqrt_mul_inv` and `MPOTensor.sourceSqrt_inv_mul`
(`TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean`) were pure pass-throughs of
`mul_inv_cancel₀` with one use each; they were retired in the 2026-09-23
second pass together with the wider attribute sweep over that file, and the
two copies of the normalized-ancilla cancellation in
`TNLean/MPS/MPU/PhysicalAncilla.lean` now route through
`Complex.ofReal_sqrt_inv_mul_self`. Recorded in
`docs/audits/2026-09-23_hygiene_second_pass.md`.
