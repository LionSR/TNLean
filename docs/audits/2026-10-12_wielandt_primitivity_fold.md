# Fold of the Wielandt primitivity auxiliary modules (2026-10-12)

Issue #7909 asked for the three single-consumer modules around the
primitivity equivalence to be folded into their consumers. The fold moves
every theorem under its existing name and removes one forwarder. The
consumers were found by searching every final name component across
`TNLean`, `TNLeanTest`, `blueprint/src`, `docs` and `scripts` on `main`.

## Modules folded

| Deleted module | Content now lives in |
|---|---|
| `TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducibleAux.lean` | `TNLean/MPS/Transfer/Primitivity/ImpliesStronglyIrreducible.lean`: `exists_hermitian_ne_zero_trace_zero_pow_fixedPoint`, `isPeripherallyPrimitive_of_isPrimitivePaper`, `isStronglyIrreduciblePaper_of_isPrimitivePaper`, unchanged |
| `TNLean/Wielandt/Primitivity/ImpliesIrreducible.lean` | `TNLean/MPS/Transfer/Primitivity/StronglyIrreducibleToFullRank.lean`: `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef`, unchanged |
| `TNLean/MPS/Structure/PrimitivityBridge.lean` | `TNLean/MPS/Transfer/Spectrum/PrimitiveOverlap.lean`: `IsPrimitiveMPS.overlap_tendsto_one`, unchanged |

## Removed declaration and its replacement

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.HasPrimitiveFixedPoint.overlap_tendsto_one` (`MPS/Structure/PrimitivityBridge.lean`, deleted) | `MPSTensor.IsPrimitiveMPS.overlap_tendsto_one` applied to the witness of `MPSTensor.HasPrimitiveFixedPoint`, which was its whole body; its one consumer, `overlap_tendsto_one_of_peripheralPrimitive_of_irreducible` in `MPS/Transfer/Spectrum/PrimitiveOverlap.lean`, now inlines that step |

No blueprint `\lean{...}` tag cites the removed name. The coherent
prerequisite allowlist `scripts/coherent_tn_prerequisites.json` now names
`TNLean.MPS.Transfer.Primitivity.ImpliesStronglyIrreducible` in place of the
deleted auxiliary module and drops `TNLean.MPS.Structure.PrimitivityBridge`,
whose content is in the already listed
`TNLean.MPS.Transfer.Spectrum.PrimitiveOverlap`.
