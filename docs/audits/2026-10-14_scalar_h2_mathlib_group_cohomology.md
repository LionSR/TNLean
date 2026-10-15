# Scalar `H²(G, ℂˣ)` on Mathlib's group cohomology

This audit records the public declarations removed when the second cohomology
of a group with coefficients `ℂˣ` (trivial action) moved from a TNLean quotient
to Mathlib's `groupCohomology.H2 (Rep.ofMulDistribMulAction G ℂˣ)`. It is the
audit note required by `docs/project_conventions.md` §Style for public
removals. All non-`Archive` uses are migrated, the blueprint `\lean{...}` tags
cite only Mathlib or surviving names, and no compatibility alias is kept.

The trivial action is the scoped instance
`TNLean.Algebra.ScalarCohomology.trivialMulDistribMulAction`
(`open scoped TNLean.Algebra.ScalarCohomology`); Mathlib defines no action of an
arbitrary group on `ℂˣ`. The class of a cocycle `ω` with `hω : ω.IsCocycle` is
`groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω.isMulCocycle₂)`.

## Removed declarations

| Removed | Replacement |
|---|---|
| `TNLean.Algebra.H2`, `ScalarCocycle.IsCocycle.instSetoid` | `groupCohomology.H2 (Rep.ofMulDistribMulAction G ℂˣ)` |
| `TNLean.Algebra.ScalarCocycle.trivialMulDistribMulAction` (def) | scoped instance `TNLean.Algebra.ScalarCohomology.trivialMulDistribMulAction` |
| `TNLean.Algebra.scalarH2Representation` | `Rep.ofMulDistribMulAction G ℂˣ` |
| `TNLean.Algebra.scalarH2Representation_ρ_apply` | `TNLean.Algebra.ScalarCohomology.ofMulDistribMulAction_ρ_apply` |
| `TNLean.Algebra.ScalarThreeCochain.norm_scalarH2Representation_apply` | `TNLean.Algebra.ScalarThreeCochain.norm_scalarRepresentation_apply` |
| `TNLean.Algebra.ScalarCocycle.IsCoboundary` | `groupCohomology.IsMulCoboundary₂` |
| `TNLean.Algebra.ScalarCocycle.isCoboundary_iff_isMulCoboundary₂`, `isCoboundary_iff_mem_mathlibCoboundaries`, `cohomologousTo_iff_isCoboundary_div`, `isCoboundary_iff_cohomologousTo_one` | `TNLean.Algebra.ScalarCocycle.cohomologousTo_iff_isMulCoboundary₂_div` |
| `TNLean.Algebra.ScalarCocycle.toMathlibCocycle` | `groupCohomology.cocyclesOfIsMulCocycle₂` with `ScalarCocycle.IsCocycle.isMulCocycle₂` |
| `TNLean.Algebra.ScalarCocycle.ofMathlibCocycle`, `representativesEquivMathlib` | `TNLean.Algebra.ScalarCocycle.exists_H2π_eq` |
| `TNLean.Algebra.h2ToGroupCohomology`, `h2ToGroupCohomology_injective`, `h2ToGroupCohomology_surjective`, `h2EquivGroupCohomology` | none; `ScalarCocycle.cohomologousTo_iff_H2π_eq` and `ScalarCocycle.exists_H2π_eq` |
| `TNLean.Algebra.ScalarCocycle.IsNontrivialClass` | `groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω.isMulCocycle₂) ≠ 0`, with `ScalarCocycle.cohomologousTo_one_iff_H2π_eq_zero` |
| `TNLean.Algebra.ScalarCocycle.isNontrivialClass_of_commPhase_ne_one` | `TNLean.Algebra.ScalarCocycle.H2π_ne_zero_of_commPhase_ne_one` |
| `TNLean.Algebra.ProjectivelyEquivalent`, `projRep_equiv_iff_cohomologous`, `ProjectiveRepresentation.cocycle` | none; the relation was `ScalarCocycle.CohomologousTo` of the factor systems |
| `TNLean.Algebra.H2.comap`, `H2.comap_mk` | `groupCohomology.map f (scalarRepresentationRes f) 2`, with `ScalarCocycle.map_H2π` |
| `TNLean.Algebra.H2.mem_range_comap_subtype_iff` | `TNLean.Algebra.ScalarCocycle.H2π_mem_range_map_subtype_iff` |
| `TNLean.Algebra.ScalarCocycle.positiveResidual_isCoboundary` | folded into `ScalarCocycle.cohomologousTo_circlePhaseInclusion` |
| `TNLean.Algebra.ScalarCocycle.ofMathlibCocycle_map_circlePhaseMathlibCocycle` | none; `ScalarCocycle.H2π_map_circlePhaseMathlibCocycle` now takes a scalar cocycle |

`scalarRepresentationRes` moved from
`TNLean/Algebra/ScalarThreeCocycleGroupCohomology.lean` to
`TNLean/Algebra/CocycleCohomology.lean`, unchanged.

## Changed statements

Statements that took `IsNontrivialClass ω` now take `hω : ω.IsCocycle` and the
nonvanishing of the class of `ω` in Mathlib's `H²`:
`ProjectiveRepresentation.finrank_eigenspace_ne_one_of_commute` and
`MPSTensor.finrank_eigenspace_ne_one_of_isNontrivialClass`. The examples
`MPSTensor.cluster_isNontrivialSPT`, `MPSTensor.aklt_isNontrivialSPT`,
`MPSTensor.akltTensorRMP_virtual_projRep` and
`MPSTensor.isNontrivialClass_of_clusterSPTFixedPoint` conclude that the class is
nonzero. `StabilizerRepresentatives.h2EquivSolutionClasses_H2π` takes a scalar
cocycle on the stabilizer instead of a Mathlib cocycle.

## Remaining

The curried cochain type `ScalarCocycle G = G → G → ℂˣ`, its cocycle
predicate `ScalarCocycle.IsCocycle` and the relation
`ScalarCocycle.CohomologousTo` remain; replacing them by uncurried
representatives `G × G → ℂˣ` satisfying `groupCohomology.IsMulCocycle₂` and by
equality of classes is the next step of issue #8317.
