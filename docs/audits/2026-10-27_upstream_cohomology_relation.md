# Scalar cohomology uses native coboundaries and degree-two classes

This continues [#8317](https://github.com/LionSR/TNLean/issues/8317), after
[#10233](https://github.com/LionSR/TNLean/pull/10233) and
[#10235](https://github.com/LionSR/TNLean/pull/10235). The local predicate for
cohomologous scalar two-cochains is deleted. Its mathematical content is
expressed directly with Mathlib's multiplicative coboundary predicate or,
for genuine cocycles, equality of degree-two cohomology classes.

## Removed declarations and replacements

Names beginning with `ScalarCocycle` or `StabilizerRepresentatives`, and the
unqualified replacement names below, belong to `TNLean.Algebra`.

| Removed declaration | Native replacement |
| --- | --- |
| `ScalarCocycle.CohomologousTo` | `groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂)` for arbitrary cochains; equality of `groupCohomology.H2π` classes for cocycles |
| `ScalarCocycle.CohomologousTo.refl` | `isMulCoboundary₂_div_self` |
| `ScalarCocycle.CohomologousTo.symm` | `isMulCoboundary₂_div_symm` |
| `ScalarCocycle.CohomologousTo.trans` | `isMulCoboundary₂_div_trans` |
| `ScalarCocycle.CohomologousTo.equivalence` | The three preceding consequences of equality in Mathlib's cochain quotient, without a replacement local relation or setoid |
| `ScalarCocycle.CohomologousTo.comap` | `isMulCoboundary₂_div_comap`, including arbitrary two-cochains |
| `ScalarCocycle.isMulCocycle₂_of_cohomologousTo` | `isMulCocycle₂_of_isMulCoboundary₂_div` |
| `ScalarCocycle.cohomologousTo_iff_isMulCoboundary₂_div` | `isMulCoboundary₂_div_iff`, which relates the upstream predicate directly to the source witness equation |
| `ScalarCocycle.cohomologousTo_iff_H2π_eq` | `H2π_eq_iff_isMulCoboundary₂_div`, comparing two upstream constructions with both cocycle proofs |
| `ScalarCocycle.cohomologousTo_one_iff_H2π_eq_zero` | `H2π_eq_zero_iff_isMulCoboundary₂` |
| `ScalarCocycle.commPhase_eq_of_cohomologousTo` | `ScalarCocycle.commPhase_eq_of_isMulCoboundary₂_div` |
| `ScalarCocycle.cohomologousTo_circlePhaseInclusion` | `ScalarCocycle.H2π_circlePhaseInclusion`, with the phase cocycle proved by `ScalarCocycle.circlePhaseInclusion_isMulCocycle₂` |
| `StabilizerRepresentatives.cohomologousTo_iff_exists_actionGauge_inducedLSymbol_eq` | `StabilizerRepresentatives.isMulCoboundary₂_div_iff_exists_actionGauge_inducedLSymbol_eq` |
| `MPSTensor.isMulCoboundary₂_div_of_continuous_unital_supported_family` | `MPSTensor.H2π_eq_of_continuous_unital_supported_family`, deriving the endpoint cocycle proofs from the supplied trace-one support data |

No compatibility aliases or comparison lemmas with the deleted local
predicate remain. Other public theorem names are retained where their
mathematical meaning is unchanged, but their hypotheses and conclusions now
refer directly to the upstream constructions. Chapter 12, chapter 29, and
the symmetry appendix cite the replacement declarations.

## Witness and class orientation

For the trivial action on complex units, the source equation is

```text
ω₁(g,h) = φ(g) φ(h) φ(gh)⁻¹ ω₂(g,h).
```

The same witness `φ`, not its inverse, proves the upstream equation

```text
φ(h) / φ(gh) * φ(g) = ω₁(g,h) / ω₂(g,h).
```

Thus the numerator remains the first representative. For two genuine
cocycles, their additive representatives differ by precisely this
multiplicative ratio. Mathlib's `H2π_eq_iff` therefore identifies
`[ω₁] = [ω₂]` with the stated coboundary ratio, in the same order.
The zero-class criterion follows directly from `H2π_eq_zero_iff`.

Cocycle propagation uses the inclusion of coboundaries in cocycles and the
closure of the cocycle submodule under addition. Commutator invariance and
pullback of a coboundary use its witness equation and require no cocycle
hypothesis on either input. Reflexivity, symmetry, and transitivity are
consequences of equality in the existing upstream quotient of all cochains
by coboundaries.

## Genuine cocycles versus arbitrary cochains

The gauge, fixed-point, global support, and projective-path results use
existing positive-dimensional projective representations to derive the
cocycle proofs needed for their H² expressions. Support-frame positivity
comes from the existing isometry or trace-one assumptions. The matrix-only
endpoint results bundle their existing invertible matrices as projective
representations within the conclusion; no additional representation or
cocycle premise is required.

The following boundaries remain statements about arbitrary cochains:

- The determinant/path primitive does not establish the cocycle condition
  for its individual factors, so it concludes a coboundary ratio.
- `ProjectiveRepresentation.exists_unitary_rephase_of_cohomologous` has no
  positive-dimension assumption and concerns the included phase factors;
  its input is a coboundary ratio.
- `MPSTensor.IsSameSPTPhase` permits zero bond dimension and retains a
  coboundary-ratio conjunct rather than imposing new cocycle conditions.
- Stabilizer action-gauge comparisons on unrestricted scalar cochains and
  the commutator invariant retain their unrestricted ratio statements.
- The two local-only compression primitives have data only on a
  neighborhood. Their eventual conclusions remain ratios; no unjustified
  total map to H² is constructed outside that neighborhood.
- The generic local-to-global quotient theorem from #10235 still applies
  to arbitrary cochains and has no cocycle premise.

The exact-ground-path conclusion now supplies a derived cocycle-proof family
alongside its existing existential data, so its final all-pairs equality can
refer directly to H². Every former input hypothesis and existential
condition remains. The additional proof witness follows from the already
supplied positive dimensions and projective representations; it is not an
extra assumption or a new choice of factor systems.

## Regression coverage and remaining gate

The native core tests cover the same-witness equation, coboundary propagation,
class equality with two cocycle proofs, the zero-class criterion, and standard
`#print axioms` reports. The earlier arbitrary-cochain quotient regressions
are preserved. `UpstreamCohomologyBoundary.lean` constructs zero-dimensional
projective actions for arbitrary factors and checks both rephasing and the
SPT supplied-data relation without any cocycle hypothesis.

The `ScalarCocycle` abbreviation and its remaining helper namespace still
need migration, including their degree-three cochain consumers and Blueprint
targets. They remain an explicit gate in #8317 under #8315; this slice alone
does not permit the next TNLean Mathlib bump. The distinct degree-three
cohomology predicates are unchanged.
