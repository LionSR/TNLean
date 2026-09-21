# Vertical canonical decomposition as a shared parent structure

This audit records the restructuring of the three matrix-product-density-
operator carriers that recorded a vertical canonical decomposition, and the
declarations that the restructuring made redundant. It is the audit note
required by `docs/project_conventions.md` §Style for removals under the
pass-through exception. No compatibility alias is provided for any removed
declaration.

## The duplication

`MPOTensor.CPSVVerticalDecomposition` records a vertical canonical
decomposition of an MPO tensor which retains the literal CPSV16
basis-of-normal-tensors predicate: the label count, the bond dimensions, the
multiplicities, the positive diagonal weights, the basis tensors, the vertical
coisometry, and the two conjugation identities of arXiv:1606.00608,
Proposition 4.13.

`MPOTensor.BNTAlgebraTensorClause` (Theorem 4.14(ii)) and
`MPOTensor.BNTFusionTensorClause` (Theorem 4.14(iii)) each restated the same
twelve fields, with the same source citations, before adding their own data.
Both carriers therefore held a vertical canonical decomposition that could not
be handed to a theorem stated for one, and the repository paid for this in two
field-by-field transcriptions and two duplicated pass-through lemmas.

## What changed

`MPOTensor.CPSVVerticalDecomposition` moved from
`TNLean/MPS/MPDO/RFPPositiveFusionDecomposition.lean` to
`TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean`. The move is upstream and was
forced: `RFPPositiveFusionDecomposition` already imports
`BNTAlgebraTensorClause` transitively through
`VerticalBlockedOperatorRepresentations`, so the two clauses could not have
extended a structure that lived downstream of them. The declaration keeps its
name, its namespace, and its statement; the per-field source citations of the
clause copies were merged onto its fields, so every field now names the
Proposition 4.13 passage it formalizes. The import of `BNTAlgebraTensorClause`
into `RFPPositiveFusionDecomposition` is now explicit.

`MPOTensor.BNTAlgebraTensorClause` and `MPOTensor.BNTFusionTensorClause` now
extend `MPOTensor.CPSVVerticalDecomposition` and declare only their own
fields: `coeffs` and `algebraClause` for the algebra clause, and `chi` through
`idempotent` for the fusion clause. Field access is unchanged for consumers,
because the parent projection resolves `H.labelCount` and its siblings.

`MPOTensor.BNTFusionTensorClause.toBNTAlgebraTensorClause` and the fusion
clause assembled in `TNLean/MPS/MPDO/BNTFusionTensorClauseFromRFP.lean` now
pass the parent structure as a whole instead of transcribing its twelve
fields.

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPOTensor.BNTAlgebraTensorClause.isBNT` | `H.isCPSVBNT.isBNT`, the composition it abbreviated |
| `MPOTensor.BNTFusionTensorClause.isBNT` | `H.isCPSVBNT.isBNT`, the composition it abbreviated |

Both lemmas had a one-line body, existed in two namespaces for the same
reason, and had no consumer anywhere outside their own statements. Under the
shared parent they would have collapsed into a single lemma on
`CPSVVerticalDecomposition`, which would still have no consumer, so they were
deleted rather than merged.

## What was checked

Every construction site of the three carriers uses named fields, so the change
in flattened constructor order is invisible: they are at
`RFPPositiveFusionDecomposition.lean`, `BNTFusionTensorClauseFromRFP.lean`,
`RescalingStableExplicitVerticalBNT.lean`, `TwistedDimerBNTAlgebraClause.lean`,
`BondTwoSingletonPhysicalGauge.lean`, `BondTwoSingletonBaseModel.lean`, and
`VerticalCoefficientPresentationCounterexample.lean`. No positional
constructor, `mk.injEq` rewrite, numeric projection, or positional
`cases`/`rcases` on any of the three carriers exists in the repository, and no
declaration refers to a clause projection by its fully qualified name.

No blueprint `\lean{}` tag cites either removed lemma, and every tag on the
two clauses and their namespaces cites a name that survives unchanged. The
blueprint declaration sync reports full coverage.

The whole transitive importer closure of the four edited modules is
sixty-four modules, all of them inside `TNLean/MPS/MPDO` apart from the `MPS`
aggregator, and it builds clean.

## What is retained and why

`MPOTensor.BNTAlgebraTensorClauseSpectrum` keeps its own
`decomposition : CPSVVerticalDecomposition (blockTwo M)` field. This is the
two-site decomposition of the blocked tensor `blockTwo M`, a different tensor
from the one the clause decomposes, so it is not a parallel copy of the
clause's own data and the parent projection cannot supply it.

`MPOTensor.cpsvVerticalDecomposition_of_grouped_orthogonal_sectors` and
`MPOTensor.IsHorizontalCF.exists_cpsvVerticalDecomposition` stay in
`RFPPositiveFusionDecomposition.lean`: they are constructions from the
renormalization fixed-point development, not part of the definition, and they
depend on material that the clause module does not import.
