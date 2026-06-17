# Issue #138 follow-up — finite-POVM compression auxiliaries (2026-04-24)

This pass did **not** close `posMap_rpow_concave_jensen` or
`cor52_item1_rpow_of_subunital`.

It did, however, promote a substantial part of the earlier scratch work into
committed code:

- new module `TNLean/Channel/Schwarz/OperatorJensenAux.lean`
- `TNLean/Channel/Schwarz/OperatorConvexity.lean` imports the new auxiliary
  module and records the partial-progress status in its docstring

## New formalized lemmas

The new auxiliary module now proves the compression / finite-POVM half of the
planned direct route:

- `inverse_compression_le`
- `povmIsometry`
- `povmDiagonal`
- `povmIsometry_star_mul`
- `povmIsometry_compress_diagonal`
- `povm_sum_add_defect`
- `povmDiagonal_posDef`

These are exactly the ingredients needed to turn a finite PSD family with
`∑ᵢ Bᵢ ≤ 1` into an isometric compression of a scalar block-diagonal matrix.

## What is still missing

The unresolved step is the explicit **diagonal-inverse / resolvent packaging**:

1. rewrite the inverse of the scalar block-diagonal matrix in the exact form
   needed for the resolvent inequality;
2. derive the finished finite-POVM resolvent inequality;
3. carry that pointwise inequality through the Löwner-integral representation
   to `posMap_rpow_concave_jensen`.

So the branch now contains genuine reusable code for the hard compression step,
but the Jensen theorem itself remains axiom-backed.

## Checks

- `lake env lean TNLean/Channel/Schwarz/OperatorJensenAux.lean`
- `lake env lean TNLean/Channel/Schwarz/OperatorMonotone.lean`
- `lake build`
- `cd blueprint && leanblueprint checkdecls`
