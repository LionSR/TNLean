# Dyadic protocol compression through the general distributed construction

This audit records the public declarations removed from
`TNLean/PEPS/Approximation/DyadicProtocolCompression.lean`. That module now reads a dyadic
protocol as a distributed construction and applies the general compression theorem for
distributed constructions in `TNLean/PEPS/Approximation/DistributedGateMapConstruction.lean`.
This is the audit note required by `docs/project_conventions.md` §Style. Every non-`Archive` use
on `main` has been migrated, and no open pull request uses the removed names. Blueprint
`\lean{...}` tags now cite the replacements, and no compatibility alias is kept.

## Removed declarations

| Removed | Replacement |
|---|---|
| `PairEffect.EffectCircuit.exactGateMaps` | `PairEffect.EffectCircuit.expansionGateMaps` |
| `PairEffect.EffectCircuit.selfLists` | `PairEffect.EffectCircuit.expansionGateLists` |
| `PairEffect.EffectCircuit.evalWithGateMaps_exactGateMaps` | `PairEffect.EffectCircuit.evalWithGateMaps_expansionGateMaps` |
| `PairEffect.EffectCircuit.castLayouts` | `PairEffect.OriginalCircuit.castLayouts` |
| `PairEffect.OriginalCircuit.isGateApproximation_produce` | `PairEffect.OriginalCircuit.isGateApproximation_reexpand_expansionGateLists` |
| `PairEffect.OriginalCircuit.monomialCount_produce_le` | `PairEffect.OriginalCircuit.monomialCount_reexpand_expansionGateLists_le` |
| `PairEffect.OriginalCircuit.isTermwiseBounded_produce` | `PairEffect.OriginalCircuit.IsExpansionBounded.isTermwiseBounded` with `PairEffect.OriginalCircuit.isTermwiseBounded_reexpand_expansionGateLists` |
| `PairEffect.OriginalCircuit.expandedGateCount_castLayouts_produce` | `PairEffect.OriginalCircuit.nonprivateCount_castLayouts` |
| `PairEffect.OriginalCircuit.exists_participants_castLayouts_produce`, `participationCount_castLayouts_produce`, `isGateApproximation_castLayouts_produce`, `isTermwiseBounded_castLayouts_produce`, `monomialCount_castLayouts_produce_le` | `PairEffect.OriginalCircuit.castLayouts_induction`, through `Approximation.DyadicProtocol.toDistributedConstruction_circuit_induction` |
| `PairEffect.OriginalCircuit.evalWithGateMaps_castLayouts_produce` | `PairEffect.OriginalCircuit.eval_castLayouts_memCongr` |
| `Approximation.DyadicProtocol.toGateMapConstruction` | `Approximation.DyadicProtocol.toDistributedConstruction`, composed with `PairEffect.DistributedConstruction.toGateMapConstruction` |
| `Approximation.DyadicProtocol.physicalDensity_toGateMapConstruction` | `Approximation.DyadicProtocol.physicalDensity_toDistributedConstruction`, with `PairEffect.DistributedConstruction.physicalDensity_toGateMapConstruction` |

The first three removed declarations are literally the same definitions and theorem as their
replacements. Casting the layouts of the original circuit before producing its chronology, rather
than casting the produced effect circuit, makes the existing original-circuit cast lemmas apply.

One step of the old proof is genuinely different from the general API, and it is kept as
`PairEffect.OriginalCircuit.IsExpansionBounded.isTermwiseBounded`. The protocol records the
absolute coefficient sum of each gate expansion, while the general theorem takes individual
coefficient bounds. A sum bound `S ≤ S'` bounds every coefficient by `S'`.
