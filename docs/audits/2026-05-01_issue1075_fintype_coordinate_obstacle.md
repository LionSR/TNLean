# 2026-05-01 — Fintype-level coordinate obstacle (#1075/#990)

## Scope

This note records the precise remaining mathematical gap that blocks the
unconditional common primitive irreducible block decomposition from issue #942.

The gap is a single Fintype-level compatibility assertion: the two independent
instances of `Fintype.equivFin` used in the blocked-word infrastructure (one for
`Fin p → Fin d` and one for `Fin n → Fin (blockPhysDim d m)`) are compatible
under the natural currying and product-identification maps that send a function
`Fin p → Fin d` (where `p = m*n`) to the corresponding `n`-tuple of `m`-tuples.

## Lean statement

In `CyclicSectorDecomposition.lean`, the lemma
`flattenWordOfBlock_cast_eq` states:

```lean
theorem flattenWordOfBlock_cast_eq {d m n p : ℕ}
    (hp_eq : p = m * n) (h_card : blockPhysDim (blockPhysDim d m) n = blockPhysDim d p)
    (i : Fin (blockPhysDim d p)) :
    flattenBlockedWord d m
      (wordOfBlock (blockPhysDim d m) n (Fin.cast h_card.symm i)) =
    wordOfBlock d p i := by
  sorry
```

This lemma is the single remaining `sorry` that blocks:
- `CommonGroupedBlockCastHypothesis d`
- `CommonSectorRelabelingHypothesis d`
- `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` (making it unconditional)
- The closure of issues #1075, #990, and #942.

## Dependencies

The lemma `groupedBlockCastAgrees_iff_flatten_eq` reduces the coordinate
assertion `groupedBlockCastAgrees` to exactly the equation above.
The lemma `unconditional_commonPrimitiveIrreducibleBlocks` in
`StructuralTheorem.lean` shows that proving `flattenWordOfBlock_cast_eq`
immediately yields the unconditional common-block theorem.

The reduction chain is:
1. `flattenWordOfBlock_cast_eq` → `CommonGroupedBlockCastHypothesis d`
2. → `CommonSectorRelabelingHypothesis d`
3. → `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
   (unconditional)

## Mathematical content

The equality concerns two ways to decode a blocked physical index
`i : Fin (blockPhysDim d p)` (`= Fin (d^p)`) into a list of `p` physical letters:

1. **Direct decoding** (RHS): `wordOfBlock d p i` uses `Fintype.equivFin (Fin p → Fin d)`
   to interpret `i.val` as a function `Fin p → Fin d`, then lists its values.

2. **Grouped decoding** (LHS): First interpret `i` through
   `Fintype.equivFin (Fin n → Fin (blockPhysDim d m))` (where `blockPhysDim d m = d^m`),
   obtaining an `n`-tuple of `Fin d^m` values; then decode each of those through
   `Fintype.equivFin (Fin m → Fin d)`; then flatten the `n` lists of length `m` into
   one list of length `p = m*n`.

The equality asserts that these two decoding paths produce the same length-`p` word
over `Fin d`.  This is true for the standard Mathlib `Fintype` instances for
function types, which use lexicographic enumeration, because the lexicographic
ordering of `Fin p → Fin d` coincides with the lexicographic ordering of
`Fin n → (Fin m → Fin d)` under the natural currying isomorphism.

Proving this in Lean requires chasing the specific `Fintype` instances for
`Pi` types through `Fintype.equivFin`, `Fintype.truncEquivFin`, and the
underlying `Finset` enumerations of `Fin n → Fin (blockPhysDim d m)`.
The key lemma is likely `Fintype.truncEquivFin` applied to both function types,
together with a lemma relating the `Finset` of all functions `Fin p → Fin d`
to the product of `Finset`s of functions `Fin m → Fin d`.

## References

- `Mathlib/Data/Fintype/EquivFin.lean` — definition of `Fintype.equivFin`
- `Mathlib/Data/Fintype/Basic.lean` — `Pi.fintype` instances
- `Mathlib/Data/Fin/Fin.mp` — binary product decomposition of `Fin (m*n)`
- `TNLean/MPS/Core/BlockingInfrastructure.lean` — `directToIteratedBlockIndex`, `iteratedBlockIndex`, etc.
- `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean` — `flattenWordOfBlock_cast_eq`, `groupedBlockCastAgrees_iff_flatten_eq`
- `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` — `unconditional_commonPrimitiveIrreducibleBlocks`
