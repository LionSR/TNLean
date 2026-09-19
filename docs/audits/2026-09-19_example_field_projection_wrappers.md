# Per-example field-projection wrappers in the asymmetric-compression examples

This audit records the removal of five theorems whose whole content was a
projection of a field of the example's own compression datum, together with the
zero-consumer matrix-product-operator reduction lemma removed in the same pass.
It is the audit note required by `docs/project_conventions.md` §Style: all
non-`Archive` uses are migrated, no blueprint `\lean{...}` tag cites a removed
name, and no compatibility alias is provided.

## The convention

Each worked example of the multi-block asymmetric compression theorem builds a
`MPSTensor.MultiBlockCompression` datum for its own tensor. The clauses of that
theorem — biorthogonality of the compression pairs, the reduction onto each
matched slot, and, when the remainder vanishes, the two sitewise intertwining
relations — are theorems about an arbitrary datum, proved once on the general
structure. Restating them for one example adds no mathematics: the restatement's
proof is the general theorem applied to that example's datum, and the datum's
type already determines every such statement.

`docs/blueprint_style_guide.md` §"Display hierarchy for formal declarations"
now carries this as item 6. A worked-example entry tags the data and the
statements that carry example-specific content — the compression datum, its
remainder theorem, and its numeric slot and dimension counts — and the clauses
that hold of every example are carried by the `\uses` edge to the general
theorem whose field lemmas prove them. The numeric counts stay because the slot
count and the dimension identity are example content that the entry's prose
asserts and that no general statement supplies: `isingBondObject_z_eq` records
sixteen zero slots and `isingBondObject_dim_eq` records `24 = 4 + 4 + 16`.

## Removed declarations and their replacements

In `TNLean/MPS/FundamentalTheorem/Reduction/Examples/IsingWeightedTwist.lean`:

- `IsingTwist.isingBondObject_isReduction`, replaced by
  `MPSTensor.MultiBlockCompression.isReduction` applied to
  `IsingTwist.isingCompression`;
- `IsingTwist.isingBondObject_left_mul_right_of_ne`, replaced by
  `MPSTensor.MultiBlockCompression.left_mul_right_of_ne`;
- `IsingTwist.isingBondObject_mul_right_eq_right_mul`, replaced by
  `MPSTensor.MultiBlockCompression.mul_right_eq_right_mul` applied to
  `IsingTwist.isingBondObject_remainder`;
- `IsingTwist.isingBondObject_left_mul_eq_mul_left`, replaced by
  `MPSTensor.MultiBlockCompression.left_mul_eq_mul_left` applied to the same
  remainder theorem.

In `TNLean/MPS/FundamentalTheorem/Reduction/Examples/IsingSectorAction.lean`:

- `IsingTwist.sectorAction_isReduction`, replaced by
  `MPSTensor.MultiBlockCompression.isReduction` applied to
  `IsingTwist.sectorCompression`.

In `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`:

- `MPOTensor.isReduction_evalWord`, a reindexing of
  `MPSTensor.IsReduction.evalWord` along the pair-alphabet identification
  `MPOTensor.evalWord_toMPSTensor_pairConfig`. It had no consumer anywhere in
  the repository, carried no blueprint tag, and was absent from the module's
  "Main results"; a caller that needs the pair-word form obtains it from those
  two declarations directly.

## Blueprint entries retagged

All three are in `blueprint/src/chapter/ch25_asymmetric_examples_ising.tex`.

- `thm:asymex_ising_compression` keeps `IsingTwist.isingCompression` as its
  principal declaration together with the two numeric counts, and now records
  `thm:asym_multiblock` among its `\uses`, which its prose already cited by
  reference.
- `thm:asymex_ising_split` keeps `IsingTwist.isingBondObject_remainder` and now
  records `prop:asym_projector_weighted_sum`, the entry that states the sitewise
  intertwining relations for a datum with vanishing remainder.
- `thm:asymex_ising_action_compression` keeps its data, the datum
  `IsingTwist.sectorCompression` and the two numeric counts, and gains the same
  `thm:asym_multiblock` edge.

Every entry keeps `\leanok`: the datum it tags is constructed in Lean, the
numeric counts it tags are proved there, and the clauses it states are the
clauses of the general theorem now named in its `\uses`.

## What was checked

- `rg -F` over `TNLean`, `blueprint/src`, `docs` and `scripts` for each of the
  six removed names returns nothing after the change; before the change each
  returned its own declaration and, for the five wrappers, one `\lean{...}`
  payload line.
- The three edited modules and the two aggregator modules that import them build
  clean with the package linters enabled.
- `python3 scripts/blueprint_lean_sync.py --ci` resolves all 8938 tagged
  declarations, 66 of them in the edited chapter file.

## What is retained and what is deferred

Retained here: every `_z_eq` and `_dim_eq`, which print the counts their entries
assert; `IsingTwist.isingBondObject_remainder` and
`IsingTwist.sectorAction_remainder`, which are example content, not projections.

Deferred: a census of the same directory finds twenty-six further theorems of
this shape, in twelve modules, and every one of them is tagged, by thirteen
entries across the other `ch25_asymmetric_examples*` chapter files. They are
`czxPlusIdentity_isReduction` and `czxPlusIdentity_left_mul_right_of_ne`;
`fibonacci_isReduction` and `fibonacci_left_mul_right_of_ne`;
`ghzSectors_isReduction`; `kwSquare_isReduction` and
`kwSquare_left_mul_right_of_ne`; `plus_isReduction`; `kwGHZ_isReduction`;
`oneLabel_isReduction`, `oneLabel_left_mul_right_of_ne`,
`oneLabel_mul_right_eq_right_mul` and `oneLabel_left_mul_eq_mul_left`;
`parityGraded_isReduction` and `parityGraded_left_mul_right_of_ne`;
`repeatedBlock_isReduction`; `dimer_isReduction`,
`dimer_left_mul_right_of_ne`, `dimer_mul_right_eq_right_mul` and
`dimer_left_mul_eq_mul_left`; `defectSquare_isReduction` and
`defectSquare_left_mul_right_of_ne`; `uu_isReduction` and `dd_isReduction`;
`ud_isReduction` and `du_isReduction`. Those modules are under active
development in queued work, so the removals and retags are recorded as a
separate item rather than taken here. Four entries —
`thm:asymex_ghz_compression`, `thm:asymex_repeated_compression`,
`thm:asymex_kw_plus` and `thm:asymex_kw_ghz` — name such a wrapper as their
principal declaration, so each needs a surviving declaration named in its place
when its module is treated.

Excluded from that count and not proposed: the
`AnomalousCondensationZ2Z2NonSplit` statements, whose file is owned by other
open work; the per-pair twisted-dimer trios, which are specializations of the
parametrized `dimerFusion_*` statements; the `trace_evalWord` and
`remainder_ofEq` projections of the Z2×Z2 split example, which name the
stacking identity each one depends on and are not projections of the file's own
datum. `CZXCompression.czxSquare_isReduction` is not of this shape either: it
carries a real proof and has a consumer, and it stays.
