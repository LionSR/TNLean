# MPDO BNT algebra-clause dead subgraph and attribute-carrying batch

Two zero-reference passes over `TNLean/MPS/MPDO/` were applied in one commit.
The first removed a closed subgraph of six declarations whose only occurrence
anywhere in `TNLean/`, `blueprint/`, or `docs/` was the definition site plus a
module-docstring bullet. The second removed six attribute-carrying declarations
in the same directory, which a name-level grep cannot settle on its own — a
`@[simp]` lemma can be consumed by a name-free tactic invocation — so both sets
were validated together by a root `lake build`.

Both passes fall under the pass-through exception of
`docs/project_conventions.md` §Style: every removed declaration is a
restatement, a projection, or an abbreviation of something that survives, no
blueprint `\lean{...}` tag cites any of the removed names, and each removal is
paired with its replacement below.

## Removed: the dead subgraph

| Removed declaration | File | Replacement |
|---|---|---|
| `MPOTensor.BNTAlgebraTensorClause.isVerticalCF` | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean` | build `IsVerticalCF M` from the clause fields at the use site: `⟨H.labelCount, H.bondDim, H.multiplicity, H.weight, H.tensor, H.verticalCoisometry, H.multiplicity_pos, H.weight_pos, H.coisometry, H.isBNT, H.forward, H.reconstruction⟩` |
| `MPOTensor.HasBNTAlgebraTensorClause.isVerticalCF` | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean` | destructure the `Nonempty` and use the anonymous constructor above |
| `MPOTensor.BNTFusionTensorClause.isVerticalCF` | `TNLean/MPS/MPDO/BNTFusionTensorClause.lean` | the same, after `BNTFusionTensorClause.toBNTAlgebraTensorClause` |
| `MPOTensor.BNTAlgebraTensorClause.TwoSiteMultiplicitySpectrum.RelabeledTwoSiteWeightedSectorSpace` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseAmbientSectorCoordinates.lean` | `VerticalWeightedSectorSpace S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity`, which it abbreviated |
| `MPOTensor.BNTAlgebraTensorClause.TwoSiteExactSectorGauge.exists_unitary_sector_conjugacy_of_identityMarkedRealization` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseConditionalUnitary.lean` | `gauge_gram_eq_pos_smul_one_of_identityMarkedRealization` followed by `exists_unitary_sector_conjugacy_of_gauge_gram_eq_pos_smul_one`, both retained |
| `MPOTensor.BNTAlgebraTensorClause.toMultiplicitySpectrumComparison` | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseSpectrum.lean` | `(H.toTwoSiteMultiplicitySpectrum hCanonical hM).toComparison` |

The first three are one restatement carried through three carriers: the clause
structure already exposes every field of the vertical canonical form, so the
theorem was the anonymous constructor written out with a name attached, and each
downstream carrier re-forwarded it. Nothing consumed any of the three.

The subgraph is closed: removing these six strands no helper. The module
docstring bullets naming `RelabeledTwoSiteWeightedSectorSpace`,
`exists_unitary_sector_conjugacy_of_identityMarkedRealization`, and
`toMultiplicitySpectrumComparison` were removed alongside their declarations;
the sibling bullets around them (`RelabeledTwoSiteSectorAlgebra`,
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

## Restored set: empty

The root `lake build` was clean on the first attempt across all 10,365 jobs,
with every reverse dependent of the seven edited modules rebuilt. No declaration
had to be put back, so there is no "fires inside a bare tactic call" retention
to record and no tactic pattern to promote into `docs/tactic_patterns.md` from
this batch.

## Refuted candidate

`MPOTensor.physicalSliceColumns_apply_finProdFinEquiv`
(`TNLean/MPS/MPDO/BNTLayerOrthogonality.lean`) was proposed for the same batch
and is retained. It is name-level zero-reference, but it is an implicit `@[simp]`
consumer at `TNLean/MPS/MPDO/BNTLayerOrthogonality.lean:152`, where the
surrounding rewrite depends on it firing. The file is untouched.

## Deprecated rather than removed

`MPOTensor.BNTAlgebraTensorClause.TwoSiteExactSectorGauge.IdentityMarkedRealization.ofPositiveCoefficientPhysicalRealization`
(`TNLean/MPS/MPDO/BNTAlgebraTensorClauseConditionalGram.lean`) is also
zero-reference, but it is not a restatement of anything retained: it is a
substantive alternative constructor that reaches `IdentityMarkedRealization`
from a positive-coefficient same-sided physical realization, deriving the
`target` field from block positivity of the blocked tensor instead of taking the
positive-tail reflected target as a hypothesis. Its hypothesis set is therefore
incomparable with the retained
`IdentityMarkedRealization.ofPositiveTailReflectedTarget`, and the pass-through
exception does not cover it. It carries a dated `@[deprecated]` attribute
instead, and its module-docstring bullet and scope-restriction marker are
retained unchanged while the declaration is still present.

## Blueprint

No `\lean{...}` tag cites any removed name, so no blueprint label was
redirected and `leanblueprint checkdecls` is a regression check here rather than
a migration check.
