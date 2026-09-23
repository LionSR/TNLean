# Hygiene second pass: square-root pass-throughs, dead simp lemmas, and the two-sided multiplication hoist

This note records the second pass over the deferred items of
`docs/audits/2026-09-19_promoted_pattern_hygiene.md` and
`docs/audits/2026-09-19_upstream_shadow_removals.md`. No mathematical content
changes: every edit is a deletion of a declaration whose body was a one-line
instantiation, or a relocation of a statement to an earlier module.

## Square-root cancellations

The private lemmas `MPOTensor.sourceSqrt_mul_inv` and
`MPOTensor.sourceSqrt_inv_mul` in
`TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean` were pass-throughs of
`mul_inv_cancel₀` and `inv_mul_cancel₀` at the nonzero proof
`sourceSqrt_ne_zero`, each consumed once, by the two local hypotheses
`hs_mul_inv` and `hs_inv_mul` of `rightShiftPaperSourceFactors`. The two
hypotheses now carry the cancellation directly. The owner lemma
`Complex.ofReal_sqrt_inv_mul_self` does not match their shape: it cancels two
inverses against a square, while the pass-throughs cancelled a factor against
its own inverse, so inlining the general cancellation is the faithful
replacement rather than routing through the owner.

The two copies of the normalized-ancilla cancellation
`(x : ℂ) * (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = 1` in
`TNLean/MPS/MPU/PhysicalAncilla.lean`
(`MPOTensor.transferMap_normalizedDiagonalLift` and
`MPOTensor.leftCanonical_normalizedDiagonalLift`) each re-derived the inverse
square by hand through `mul_inv`, `Complex.ofReal_mul` and
`Real.mul_self_sqrt`. Both now rewrite once with
`Complex.ofReal_sqrt_inv_mul_self`, and the module imports
`TNLean.Algebra.ComplexSqrt` explicitly. The surrounding sum-collapse
structure is unchanged.

## Dead simp lemmas on shift-example rank coordinates

`TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean` carried six
`@[simp] ... := rfl` lemmas evaluating the source-rank coordinate
equivalences of the three shift examples. Five of them are deleted:

- `MPOTensor.shiftExampleU₁LeftRankEquiv_apply`
- `MPOTensor.shiftExampleU₁RightRankEquiv_apply`
- `MPOTensor.shiftExampleU₂LeftRankEquiv_apply`
- `MPOTensor.shiftExampleU₂RightRankEquiv_apply`
- `MPOTensor.shiftExampleU₃LeftRankEquiv_apply`

None is named by any other declaration in the repository, and no bare `simp`
call can fire them: the head equivalences appear only inside definitions that
no simp-family proof mentions, so no goal ever contains the head constant in a
rewritable position. Any future need is `rfl` at the use site, since each head
equivalence is a chain of `Equiv.trans` and `Equiv.prodCongr` definitions.

The sixth, `MPOTensor.shiftExampleU₃RightRankEquiv_apply`, is retained: the
blueprint entry `def:threeMPU_supplied_source_factors` of
`blueprint/src/chapter/ch28_mpu.tex` cites it in its `\lean{}` payload, so
deleting it would break the declaration check. The tag predates this pass and
is left untouched.

## Hoisting the set-indexed two-sided multiplication lemma

`TNLean.PEPS.conj_eq_conj_of_span`, which extends agreement of two two-sided
multiplication maps from a spanning set to the whole matrix algebra, moved
from `TNLean/PEPS/CycleMPSOverlapCapstone.lean` to
`TNLean/PEPS/CycleMPSChainOverlapCapstone.lean`. Its fully qualified name is
unchanged, and the overlap capstone imports the chain capstone, so its two
consumers there and the one in `TNLean/PEPS/CycleMPSTranslationInvariant.lean`
resolve as before.

The move deletes the private range-indexed duplicate
`MPSChainTensor.conj_eq_conj_of_span_range` in the chain module, whose only
consumer now applies the set-indexed form at the same spanning family with the
membership witness unpacked inline. The reverse relocation was impossible: the
chain module cannot import the overlap capstone without closing an import
cycle, so the surviving statement had to move earlier.

## What was checked

Every edited module and every module importing one builds clean under the
package linter options: the four edited modules
(`MPS.MPU.Examples.ShiftSourceFactors`, `MPS.MPU.PhysicalAncilla`,
`PEPS.CycleMPSChainOverlapCapstone`, `PEPS.CycleMPSOverlapCapstone`) plus the
importers `MPS.MPU.Examples`, `MPS.MPU.Equivalence`, `MPS.MPU`,
`PEPS.CycleMPSConstantDescription`, `PEPS.CycleMPSFundamentalTheorem` and the
`PEPS` aggregator. No proof-integrity token is introduced. The
only blueprint `\lean{}` payload touching this family names the retained
`shiftExampleU₃RightRankEquiv_apply`, so no tag is redirected.

## Retained and deferred

Retained: the remaining general-`d` `sourceSqrt` cancellations of
`ShiftSourceFactors.lean` (`sourceSqrt_sq`,
`sourceSqrt_mul_nat_inv_mul_sourceSqrt`, `sourceSqrt_inv_mul_nat_mul_inv`,
`nat_mul_sourceSqrt_inv_mul_inv` and the source-cited
`shiftSourceScale_cancel` family), which are consumed as rewrite rules in
fixed associativity shapes.

Deferred unchanged: the `Submodule.flagQuot`/`LinearMap.flagQuotMap` collapse
into `Submodule.subquot`/`LinearMap.subquotMap` of
`docs/audits/2026-09-19_upstream_shadow_removals.md`, whose gate work is still
open, is not part of this pass.
