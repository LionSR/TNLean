# Restriction of scalar cochains named `comap` in every degree

This audit records the declarations renamed when restriction of scalar
`ℂˣ`-valued cochains along a group homomorphism `f : K →* G` received one name,
`comap`, in degrees two and three. It is the audit note required by
`docs/project_conventions.md` §Style. All non-`Archive` uses are migrated, the
blueprint `\lean{...}` tags of chapter 29 cite only the new names, and no
compatibility alias is kept.

## Renamed declarations

| Removed | Replacement |
|---|---|
| `TNLean.Algebra.ScalarCocycle.pullback` | `TNLean.Algebra.ScalarCocycle.comap` |
| `TNLean.Algebra.ScalarCocycle.pullback_apply` | `TNLean.Algebra.ScalarCocycle.comap_apply` |
| `TNLean.Algebra.ScalarCocycle.IsCocycle.pullback` | `TNLean.Algebra.ScalarCocycle.IsCocycle.comap` |
| `TNLean.Algebra.ScalarCocycle.CohomologousTo.pullback` | `TNLean.Algebra.ScalarCocycle.CohomologousTo.comap` |
| `TNLean.Algebra.H2.pullback` | `TNLean.Algebra.H2.comap` |
| `TNLean.Algebra.H2.pullback_mk` | `TNLean.Algebra.H2.comap_mk` |
| `TNLean.Algebra.H2.mem_range_pullback_subtype_iff` | `TNLean.Algebra.H2.mem_range_comap_subtype_iff` |

Statements are unchanged. `ScalarCocycle.comap` and `comap_apply` moved from
`TNLean/Algebra/CocycleRestriction.lean` to
`TNLean/Algebra/ProjectiveRepresentation.lean`, next to `ScalarCocycle`. The
three-cochain restriction `ScalarThreeCochain.comap` and its lemmas keep their
names and moved from `TNLean/Algebra/ScalarThreeCocycleCyclicInvariant.lean` to
`TNLean/Algebra/ScalarThreeCocycle.lean`.

## Comparison with Mathlib

`ScalarCocycle.toInhomogeneousCochain_comap` and
`ScalarThreeCochain.toInhomogeneousCochain_comap` in
`TNLean/Algebra/ScalarThreeCocycleGroupCohomology.lean` identify both
restrictions with Mathlib's `groupCohomology.cochainsMap f` and the identity
coefficient morphism `scalarRepresentationRes f`.
