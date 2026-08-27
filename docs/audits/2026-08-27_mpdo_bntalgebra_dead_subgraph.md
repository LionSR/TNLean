# MPDO BNT algebra-clause dead subgraph and attribute-carrying batch

Two zero-reference passes over `TNLean/MPS/MPDO/` were applied in one commit.
The first audited a closed subgraph of seven declarations whose only occurrence
anywhere in `TNLean/`, `blueprint/`, or `docs/` was the definition site plus a
module-docstring bullet. All seven are deleted directly under TNLean's explicit
no-public-API-compatibility policy. The second removed six
attribute-carrying declarations
in the same directory, which a name-level grep cannot settle on its own — a
`@[simp]` lemma can be consumed by a name-free tactic invocation — so both sets
were validated together by a root `lake build`.

Both passes fall under the pass-through exception of
`docs/project_conventions.md` §Style: every removed declaration is a
restatement, a projection, or an abbreviation of something that survives, no
blueprint `\lean{...}` tag cites any of the removed names, and each removal is
paired with its replacement below.

## Audited: the dead subgraph

| Audited declaration | File | Disposition / replacement |
|---|---|---|
| `MPOTensor.BNTAlgebraTensorClause.isVerticalCF` | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean` | build `IsVerticalCF M` from the clause fields at the use site: `⟨H.labelCount, H.bondDim, H.multiplicity, H.weight, H.tensor, H.verticalCoisometry, H.multiplicity_pos, H.weight_pos, H.coisometry, H.isBNT, H.forward, H.reconstruction⟩` |
| `MPOTensor.HasBNTAlgebraTensorClause.isVerticalCF` | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean` | destructure the `Nonempty` and use the anonymous constructor above |
| `MPOTensor.BNTFusionTensorClause.isVerticalCF` | `TNLean/MPS/MPDO/BNTFusionTensorClause.lean` | the same, after `BNTFusionTensorClause.toBNTAlgebraTensorClause` |
| `MPOTensor.BNTAlgebraTensorClause.TwoSiteMultiplicitySpectrum.RelabeledTwoSiteWeightedSectorSpace` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseAmbientSectorCoordinates.lean` | removed; use `VerticalWeightedSectorSpace S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity` directly |
| `MPOTensor.BNTAlgebraTensorClause.TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_identityMarkedRealization` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseConditionalUnitary.lean` | `gauge_gram_eq_pos_smul_one_of_identityMarkedRealization` followed by `exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one`, both retained |
| `MPOTensor.BNTAlgebraTensorClause.toMultiplicitySpectrumComparison` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseSpectrum.lean` | removed; use `(H.toTwoSiteMultiplicitySpectrum hCanonical hM).toComparison` |
| `MPOTensor.BNTAlgebraTensorClause.TwoSiteExactSectorGauge.IdentityMarkedRealization.ofPositiveCoefficientPhysicalRealization` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseConditionalGram.lean` | removed; the live constructor is `IdentityMarkedRealization.ofPositiveTailReflectedTarget`, with its distinct hypothesis set |

The first three are one restatement carried through three carriers: the clause
structure already exposes every field of the vertical canonical form, so the
theorem was the anonymous constructor written out with a name attached, and each
downstream carrier re-forwarded it. Nothing consumed any of the three.

The subgraph remains closed after deleting all seven audited strands. No
aliases, wrappers, or deprecated declarations restore the former compatibility
surface. The bullets naming `RelabeledTwoSiteWeightedSectorSpace`,
`toMultiplicitySpectrumComparison`, and
`IdentityMarkedRealization.ofPositiveCoefficientPhysicalRealization` are removed
with those declarations. The bullet naming
`exists_unitary_sector_conjugacy_of_identityMarkedRealization` was removed with
that declaration; the sibling bullets around it (`RelabeledTwoSiteSectorAlgebra`,
`relabeledTwoSiteRetainedEquiv`,
`exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one`,
`exists_unitary_sector_conjugacy_of_positive_tail_reflected_target`,
`toTwoSiteMultiplicitySpectrum`, `toTwoSiteExactSectorGauge`) all name live
declarations and were left alone. No `import` line was touched: the modules
supplying `IsVerticalCF` also supply the clause structures, so the removals do
not make any import dead.

## Removed: the attribute-carrying batch

| Removed declaration | File | Replacement |
|---|---|---|
| `MPOTensor.BNTAlgebraTensorClause.operators_operator` | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean` | `rfl`; it was a `@[simp]` projection of `operators`, which is `verticalBNTOperatorFamily H.tensor` by definition |
| `MPOTensor.CPSVExample412Literal.M_zero_zero` | `TNLean/MPS/MPDO/CPSVExample412Literal.lean` | unfold `M` directly, as the surviving call sites already do |
| `MPOTensor.CPSVExample412Literal.M_one_one` | `TNLean/MPS/MPDO/CPSVExample412Literal.lean` | unfold `M` directly |
| `MPOTensor.CPSVExample412Literal.M_zero_one` | `TNLean/MPS/MPDO/CPSVExample412Literal.lean` | unfold `M` directly |
| `MPOTensor.CPSVExample412Literal.M_one_zero` | `TNLean/MPS/MPDO/CPSVExample412Literal.lean` | unfold `M` directly |
| `MPOTensor.CPSVExample411BinarySupport.complementPathWeight_cons` | `TNLean/MPS/MPDO/CPSVExample411BinarySupport.lean` | `rfl`; it restated the recursive branch of `complementPathWeight` |

The four `M_*` lemmas were predicted to be the likeliest survivors, because the
literal-example computations expand `M`, `sigmaZ`, and `SpinCover.pauli` in the
same `norm_num` call that the deleted lemmas would also have matched. The
prediction was wrong: with the lemmas gone, the explicit `M` unfolding in those
calls closes the goals on its own.

Their underlying definitions all keep independent consumers: `M` and `sigmaZ`
through the literal-example computations, `weightMatrix` and
`complementPathWeight` through the binary-support development, `operators`
through `traceScalars_traceScalar`'s neighbourhood in the clause API.
`sigmaZ_apply_ne` and `complementPathWeight_zero` are attribute-carrying
siblings of removed lemmas but are both used by name, and are untouched.

## Direct deletion: no compatibility restoration

The earlier root build was clean across all reverse dependents and exposed no
name-free in-tree consumers. API review initially restored two declarations and
marked the alternative identity-realization constructor deprecated. The
maintainer then clarified that TNLean promises no public API compatibility.
Accordingly, all three are now deleted, their module-docstring bullets are
removed, and no alias or wrapper is retained. This batch adds no tactic pattern
to `docs/tactic_patterns.md`.

## Refuted candidate

`MPOTensor.physicalSliceColumns_apply_finProdFinEquiv`
(`TNLean/MPS/MPDO/BNTLayerOrthogonality.lean`) was proposed for the same batch
and is retained. It is name-level zero-reference, but it is an implicit `@[simp]`
consumer at `TNLean/MPS/MPDO/BNTLayerOrthogonality.lean:152`, where the
surrounding rewrite depends on it firing. The file is untouched.

## Alternative identity-marked constructor

`MPOTensor.BNTAlgebraTensorClause.TwoSiteExactSectorGauge.IdentityMarkedRealization.ofPositiveCoefficientPhysicalRealization`
was initially deprecated because its hypotheses are incomparable with
`IdentityMarkedRealization.ofPositiveTailReflectedTarget`: it derives the
`target` field from block positivity of a same-sided physical realization.
Under the clarified no-compatibility policy, that distinction remains recorded
here but does not justify retaining an unused compatibility constructor. The
declaration and its module-docstring exception are deleted directly.

## Blueprint

No `\lean{...}` tag cites any removed name, so no blueprint label was
redirected and `leanblueprint checkdecls` is a regression check here rather than
a migration check.
