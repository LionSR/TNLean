# Addresses of the dyadic hierarchy as dyadic anchors

This audit records the declarations removed when the integer address of a
square of the padded dyadic hierarchy, equation `eq:geometry-addresses` of the
September 24, 2026 polynomial PEPS manuscript (`06-geometry.tex:633–646`), was
identified with the dyadic anchor of the routing step (`eq:anchors`,
`07-assembly.tex:108–114`). It is the audit note required by
`docs/project_conventions.md` §Style. The two definitions were literally equal,
`if j = 0 then r else 2 ^ j * r + 2 ^ (j - 1)`; the module docstring of
`TNLean/PEPS/Approximation/DyadicHierarchyCounts.lean` had recorded that they
were to be unified. All non-`Archive` uses are migrated, no blueprint
`\lean{...}` tag cites a removed name, and no compatibility alias is kept.

## Removed declarations and their replacements

All removed declarations were in `TNLean/PEPS/Approximation/DyadicHierarchyCounts.lean`.

- `TNLean.PEPS.Approximation.squareAddress`. Replacement:
  `TNLean.PEPS.Approximation.dyadicAnchor` in
  `TNLean/PEPS/Approximation/DyadicAnchors.lean`, with the same defining
  expression.
- `TNLean.PEPS.Approximation.squareAddress_mem`, the address lies in its square,
  `2 ^ j r ≤ a < 2 ^ j r + 2 ^ j`. Replacement:
  `TNLean.PEPS.Approximation.dyadicAnchor_mem_block`, which states the upper
  bound as `a < 2 ^ j (r + 1)`.
- `TNLean.PEPS.Approximation.squareAddress_lt`, the addresses of the hierarchy of
  `[0, 2 ^ k] ^ 2` lie below `2 ^ k`. Replacement:
  `TNLean.PEPS.Approximation.dyadicAnchor_lt_two_pow`, with the same hypotheses,
  proved from `dyadicAnchor_lt`.
- `TNLean.PEPS.Approximation.squareAddress_lt_add`. Replacement:
  `TNLean.PEPS.Approximation.dyadicAnchor_lt_add`, with the same statement for
  `dyadicAnchor`.
- `TNLean.PEPS.Approximation.squareAddress_dist_lt`. Replacement:
  `TNLean.PEPS.Approximation.dyadicAnchor_dist_lt`, with the same statement for
  `dyadicAnchor`.

The same change adds `TNLean.PEPS.Approximation.dyadicAnchor_dist_lt_of_adjacent`,
the address bound for the owners of a repainted block, of its neighbors and of
their parents. The blueprint entries `def:peps_dyadic_hierarchy` and
`lem:peps_dyadic_address_locality` in
`blueprint/src/chapter/ch24_peps_dyadic_geometry.tex` cite the replacements.
