# Scalar two-cocycles use Mathlib's predicate

This is the next slice of [#8317](https://github.com/LionSR/TNLean/issues/8317),
after the uncurrying in [#9418](https://github.com/LionSR/TNLean/pull/9418).
It uses the already pinned Mathlib v4.35.0-rc3
(`c55e6e786f49471c72fbddbec5415808896aec1e`); it does not change the Lean or
Mathlib pin and does not close the migration issue.

## Removed declarations and replacements

| Removed declaration | Replacement |
| --- | --- |
| `TNLean.Algebra.ScalarCocycle.IsCocycle` | `groupCohomology.IsMulCocycle₂` under the scoped trivial action on complex units |
| `ScalarCocycle.isCocycle_iff_isMulCocycle₂` | `TNLean.Algebra.isMulCocycle₂_iff`, which states the source-oriented equation directly for the upstream predicate |
| `ScalarCocycle.IsCocycle.isMulCocycle₂` | No declaration: the hypothesis is already the upstream predicate |
| `ScalarCocycle.IsCocycle.of_cohomologousTo` | `ScalarCocycle.isMulCocycle₂_of_cohomologousTo` |
| `ScalarCocycle.isCocycle_of_projRep` | `ScalarCocycle.isMulCocycle₂_of_projRep` |
| `ScalarCocycle.IsCocycle.comap` | `ScalarCocycle.isMulCocycle₂_comap` |
| `ScalarCocycle.IsCocycle.coboundary_mul` | `ScalarCocycle.isMulCocycle₂_coboundary_mul` |
| `LSymbol.ratioCocycle_isCocycle` | `LSymbol.ratioCocycle_isMulCocycle₂`, now carrying the proof itself rather than a bridge |

Names without an explicit root in the table are in `TNLean.Algebra`.
No deprecated aliases or parallel two-cocycle predicates are retained. The
non-Archive callers and the declaration tags in chapters 12 and 29 are retargeted.

## Equation orientation and hypotheses

For the scoped trivial action, Mathlib states

```text
ω (g * h, k) * ω (g, h) = ω (h, k) * ω (g, h * k).
```

Commutativity of complex units makes this equivalent to the source convention

```text
ω (g, h) * ω (g * h, k) = ω (g, h * k) * ω (h, k).
```

The single equation theorem `isMulCocycle₂_iff` records this reordering. It is
not an equivalence between two local/upstream notions: both directions are
about Mathlib's predicate and an explicit equation. The projective-representation,
restriction, phase, stabilizer, L-symbol, SPT, and example statements keep their
mathematical hypotheses. In particular, the projective factor-system result
still requires positive bond dimension; no cocycle hypothesis is introduced
into an arbitrary-cochain statement.

The degree-three predicate `ScalarThreeCochain.IsCocycle` is not part of this
slice and is unchanged. The Klein three-cocycle tables and their completeness
statements therefore keep that predicate.

## Blueprint source checking

The cocycle definition now points directly to
`groupCohomology.IsMulCocycle₂`. The blueprint source checker therefore scans
the manifest-selected Mathlib source library as well as TNLean and QICLean;
no local wrapper is retained to satisfy the checker. Existing local-source
precedence is preserved, and a regression checks both a real upstream name
and rejection of a misspelled one. The checker does not scan unrelated Lake
packages or acquire build artifacts.

## Regression coverage

`TNLeanTest/UpstreamTwoCocyclePredicate.lean` checks the source-oriented
predicate equivalence, constant cocycles without normalization, the zero
class of the unit cocycle, the arbitrary-cochain coboundary comparison, and
class equality with both cocycle hypotheses. These checks use an arbitrary
group, with neither finiteness nor commutativity assumed.
`TNLeanTest/UpstreamTwoCocyclePredicateAxioms.lean` guards the axiom reports for
the orientation theorem, the projective factor-system theorem, and the
cohomology-class comparison; all use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Remaining gate for #8317

1. Replace `ScalarCocycle.CohomologousTo` and its equivalence/setoid helpers.
   For two genuine cocycles, use equality of `H2π` classes. For arbitrary
   two-cochains, use `groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂)` without
   adding a cocycle hypothesis. The arbitrary-cochain quotient consumers
   also need a mathematically equivalent quotient by Mathlib coboundaries.
2. Remove the `ScalarCocycle` abbreviation and relocate the remaining
   namespaced helpers to a suitable upstream-facing home. Migrate their
   non-Archive callers and remaining blueprint tags together.

The deferred layers remain tracked by #8317 under #8315. This slice does not
satisfy the whole prerequisite for opening the next TNLean Mathlib bump.
