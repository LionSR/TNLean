# Elementary declarations removed from the PEPS approximation development

[PR #9889](https://github.com/LionSR/TNLean/pull/9889) removes four unused
auxiliary declarations. The source examined here is
`9a7466cd2c2b42328f521a42beb8c2c32980c87e`, including its immediate predecessor
for the deleted statements and proofs. The geometric definitions, generation
and separation results, and dyadic repainting schedule remain in place.

## Removed declarations and their replacements

No replacement declaration is needed by a surviving proof. The following
arguments recover the four elementary assertions if they are needed later.

| Removed declaration | Module under `TNLean/PEPS/Approximation/` | Retained definition or mathematical argument |
|---|---|---|
| `TNLean.PEPS.Approximation.CellPartition.Generation.tile_subset_box` | `CellColouredGeneration.lean` | Tile membership includes membership in the containing box as its first conjunct. Apply `fun _ hp ↦ hp.1`. |
| `TNLean.PEPS.Approximation.dyadicAnchor_ne_zero` | `DyadicAnchors.lean` | For a nonzero scale index $j$, use the retained `dyadicAnchor_of_ne_zero`: the anchor is $2^{j-1}(2r+1)$, a positive natural number, hence nonzero. |
| `TNLean.PEPS.Approximation.holeRadius_nonneg` | `DyadicProtocolConstants.lean` | The retained definition is $\operatorname{holeRadius}(\varepsilon_0,n,t)=\varepsilon_0\min(n,t)$. Nonnegativity follows from `mul_nonneg` and `le_min` when all three arguments are nonnegative. |
| `TNLean.PEPS.Approximation.edgeOperations_eq_append` | `DyadicRepaintingSchedule.lean` | Unfold the retained `edgeOperations`, `auxSteps` and `mainSteps`. The edge schedule is, by definition, the auxiliary list followed by the main list; the deleted equality was proved by `rfl`. |

## Consumer and blueprint checks

Every final name component listed above was searched, as a whole identifier,
in all tracked files outside `Archive/` at the stated revision. There are no
remaining occurrences in Lean sources, tests, scripts or blueprint sources.
The only remaining occurrences are the descriptions of these deletions in
`docs/proof_debt_ledger.md`. In particular, no blueprint `\lean{...}` tag,
axiom-check test or named automation registration refers to a removed name.
The deleted declarations carried no registered attributes. In the immediate
predecessor, each name occurs only in its own declaration; none has a consumer.

This records the names, elementary replacements and absence of surviving uses
required by `docs/project_conventions.md`. The added audit note changes no Lean
source, test, blueprint tag or dependency input. Its checks are source searches
and comparison with the deleted proofs; no additional compilation is asserted.
