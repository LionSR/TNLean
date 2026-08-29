# Doubled-product shuffle consolidation

## Declaration mapping

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.doubledPhysicalAncillaShuffle` | `finDoubledProdEquiv` |
| `MPOTensor.doubledPhysicalAncillaShuffle_apply` | `finDoubledProdEquiv_apply` |

The inverse-coordinate formula is now recorded by
`finDoubledProdEquiv_symm_apply`.  The three replacement declarations live in
`TNLean/Algebra/FinTupleEquiv.lean`, where they describe the source-neutral
equivalence
`((i, k), (j, l)) ↦ ((i, j), (k, l))`.

## Consumer migration

The existing non-Archive consumers were
`MPOTensor.normalizedFlattening_tensorPhysicalId`,
`MPOTensor.tensorPhysicalIdCFIIData`, and
`MPOTensor.hasFullSupport_tensorPhysicalIdCFIIData`.  They now use
`finDoubledProdEquiv` directly.  The general tensor-product identity
`MPOTensor.normalizedFlattening_tensorProduct` uses the same equivalence.
A repository-wide search found no other non-Archive consumer of either removed
name.

## Blueprint and compatibility status

The old declarations had zero Blueprint tags, so no old tag remains to be
migrated.  The neutral equivalence and its two coordinate lemmas are attached
to the doubled product-coordinate definition in Chapter 28.

No compatibility alias is retained.  TNLean does not promise a stable external
Lean API, and retaining the ancilla-specific name would preserve a second
public name for a source-neutral coordinate equivalence.
