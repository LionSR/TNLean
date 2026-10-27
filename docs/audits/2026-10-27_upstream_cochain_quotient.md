# Arbitrary scalar cochains use Mathlib's coboundary quotient

This is a further slice of [#8317](https://github.com/LionSR/TNLean/issues/8317),
following [#10233](https://github.com/LionSR/TNLean/pull/10233). It removes the
custom equivalence-relation instance used by the two local-to-global path
arguments. It does not close the whole migration gate.

## Removed declarations and replacements

| Removed declaration | Replacement |
| --- | --- |
| `TNLean.Algebra.scalarCocycleSetoid` | The quotient by `groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G ℂˣ)` of all additive-valued two-cochains |
| `TNLean.Algebra.ScalarCocycle.cohomologousTo_of_eventually_at_all_points` | `TNLean.Algebra.isMulCoboundary₂_div_of_eventually_at_all_points` |
| `MPSTensor.cohomologousTo_of_continuous_unital_supported_family` | `MPSTensor.isMulCoboundary₂_div_of_continuous_unital_supported_family` |

No local quotient type, setoid, abbreviation, or compatibility alias replaces
the removed instance. The endpoint declaration tags in chapter 12 are
retargeted, and the appendix's arbitrary-cochain comparison also states the
equivalent quotient equality. The duplicate private local-constancy argument
in `ExactGroundPathTransferClass` is deleted in favor of the same generic
upstream-quotient theorem, and
`ExactMPSGroundPath.exists_constant_virtual_class_of_uniform_transfer_bound`
states its all-pairs conclusion directly with the upstream coboundary
predicate.

## Arbitrary cochains are not cohomology classes

For the scoped trivial action on complex units, the quotient used here is

```text
(G × G → Additive ℂˣ) / coboundaries₂ (Rep.ofMulDistribMulAction G ℂˣ).
```

Its representatives are arbitrary two-cochains, not only cocycles. Equality
of the images of `ω₁` and `ω₂` means that the additive difference belongs to
the coboundary submodule. Under the additive type synonym, this is precisely
`groupCohomology.IsMulCoboundary₂ (ω₁ / ω₂)`.
The theorem `isMulCoboundary₂_div_iff_quotient_mk_eq` records this comparison
between Mathlib's quotient and Mathlib's multiplicative predicate. Neither
side is a new local notion.

The local-to-global arguments retain preconnectedness and all their original
mathematical hypotheses. They require no cocycle, normalization, finite-group,
or commutative-group assumption. Existing local stability results are converted
at the input boundary using the existing arbitrary-cochain comparison.
The genuine `H²` constructions and their two-cocycle hypotheses are unchanged.

## Regression coverage

`TNLeanTest/UpstreamCochainQuotient.lean` checks the ratio orientation and the
reflexive, symmetric, and transitive consequences for arbitrary cochains. It
also exhibits a noncocycle that still has a class in the quotient by
two-coboundaries. `UpstreamCochainQuotientAxioms.lean` guards the comparison
theorem's `#print axioms` report.

## Remaining gate for #8317

The local predicate `ScalarCocycle.CohomologousTo`, its still-used operations,
and its existing conversion lemmas remain for the subsequent whole-predicate
migration. In particular, `ScalarCocycle.CohomologousTo.equivalence` still
supports the appendix's equivalence-relation theorem and is not deleted
prematurely just because the custom setoid is gone.

The remaining declarations must be stated on upstream coboundary ratios for
arbitrary cochains, or on equal `H2π` classes when genuine cocycle hypotheses
are available. The two public path conclusions in this slice retain the
equivalent coboundary-ratio formulation. A later genuine-`H²` restatement must
derive the required cocycle proofs from the existing supplied path data,
rather than adding them as new hypotheses. The `ScalarCocycle` abbreviation
and remaining namespaced
helpers also still need migration. All non-Archive callers and blueprint tags
must move with those deletions. These tasks remain in #8317 under #8315;
this slice does not satisfy the prerequisite for the next TNLean Mathlib bump.
