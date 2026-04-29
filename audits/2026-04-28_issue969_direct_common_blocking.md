# 2026-04-28 — Issue #969 direct common-blocking progress after PR #981

## Scope and issue-thread check

This branch continues issue #969 after merged predecessors #973, #975, #976, and #981.
Before finalizing statements, I read the issue bodies and comments for #969, #971, #970,
#944, #942, #652, #840, #924, #932, and #982.

The important conclusions from those threads are:

- #975 already introduced `MPSTensor.CommonBlockedCyclicSectorFamily` and the one-sided
  common reblocking constructor.  This branch should not duplicate that construction.
- #981 already supplied the iterated-blocking physical relabeling
  `MPSTensor.iteratedBlockIndex` and the theorem
  `MPSTensor.sameMPV₂_blockTensor_blockTensor_mul_reindex`.  This branch uses it inside
  the common cyclic-sector data rather than reproving it.
- #973 already supplied the weight and zero-tail reblocking lemmas.  This branch calls
  `zeroTail_toTensorFromBlocks_blockPower` and reuses the powered-weight nonvanishing
  pattern instead of reproving zero-tail arithmetic inline.
- #976 reduced the later span-equality step to common MPV phase-cover data. This
  branch does not attempt to close #970/#944; it only makes the #969 common-sector data
  more usable by exposing the direct, explicitly relabeled one-shot sector family.
- The issue #969 addendum remains binding: the full route to #944/#652 still needs a
  later common injectivity/Wielandt blocking stage.  The present branch preserves the
  distinction between period removal and later injectivity blocking.

## Paper route checked

The statements follow the non-Gemma CPSV/CPGSV route.

- `Papers/2011.12127/TN-Review-main.tex` lines 1815--1820 explains the period-removal
  step: irreducible CP maps can have peripheral eigenvalues `e^{i2\pi q/p}`, and
  "In order to remove them, we block $p$ spins."  The branch models this as the
  per-block `period k` datum.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 227--231 states the common-period move:
  "If there are $t$ $p$-periodic vectors ... by blocking lcm$(p_1,\ldots,p_t)$ systems,
  one obtains a vector without $p$-periodic ones."  The branch keeps the LCM-produced
  common length `F.p` and the quotients `F.extra k` explicit.
- `Papers/quant-ph_0608197/MPSarchive.tex` lines 849--880 gives the older periodic-sector
  picture: a one-block canonical TI-MPS with $p$ peripheral eigenvalues decomposes into
  $p$ periodic states, nonzero only when the period divides the chain length.  This is the
  origin of the cyclic-sector indexing by `Fin (F.period k)`.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 317--332 defines injectivity and recalls
  the Wielandt blocking step: "after blocking at most $D^4$ times, every NT becomes
  injective."  That later injectivity stage is not asserted by this branch.

## Lean progress in this branch

### `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean`

New derived operations for an existing `F : MPSTensor.CommonBlockedCyclicSectorFamily blocks`:

- `F.flatKey`: decodes a flattened sector index as `(k,s)`.
- `F.commonSectorBlock`: the common-alphabet sector obtained by later reblocking
  `F.sectorBlocks k s` and substituting the equality of physical alphabet sizes.
- `F.commonFlatDim` and `F.commonFlatBlocks`: a derived flattened family tied directly to
  `F.sectorBlocks`, avoiding any dependence on abstract `F.flatBlocks` coincidences.
- `F.commonSectorTensor`: the unit-weight sector tensor for one original nonzero-weight block.
- `F.oneShotReindexedBlock`: the reindexed one-step nonzero-weight block with the explicit
  blocked-word reindexing supplied by `MPSTensor.iteratedBlockIndex`.
- `F.commonFlatWeight μ`: the flattened sector weights `(μ k) ^ F.p`.

New structural/nonvanishing facts:

- `F.commonBlockWeight_ne_zero` and `F.commonFlatWeight_ne_zero`.
- `F.commonSectorBlock_tp`, `F.commonSectorBlock_primitive`,
  `F.commonSectorBlock_irreducible`, `F.commonSectorBlock_dim_pos`.
- `F.commonFlatBlocks_tp`, `F.commonFlatBlocks_primitive`,
  `F.commonFlatBlocks_irreducible`, `F.commonFlatDim_pos`.

New MPV comparison facts:

- `F.nestedBlock_sameMPV₂_oneShotReindexedBlock`: composes `F.nested_same` with
  `sameMPV₂_blockTensor_blockTensor_mul_reindex`, keeping the per-block physical relabeling
  explicit.
- `F.oneShotReindexedBlock_sameMPV₂_commonSectorTensor`: the relabeled one-shot nonzero-weight block
  is represented by the corresponding common-alphabet cyclic sectors.
- `F.sameMPV₂_weightedOneShotReindexedBlock_commonFlat`: the weighted direct sum of
  relabeled one-shot nonzero-weight blocks flattens to the derived common-sector family with weights
  `F.commonFlatWeight μ`.

### `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`

New theorem:

- `MPSTensor.fundamentalTheorem_after_blocking_1606_reindexed_commonSector_live_with_zeroTail`.

This theorem starts from `SameMPV₂ A B`, reuses the already-merged common cyclic-sector
families on both sides, and exposes:

1. zero-tail/live equations after the corresponding common reblocking on each side;
2. a `SameMPV₂` comparison between the weighted relabeled one-shot nonzero-weight blocks and the
   derived flattened common-sector family;
3. nonzero transported sector weights;
4. trace preservation, primitive transfer maps, tensor irreducibility, and positive bond
   dimensions for the derived common-sector families.

The statement is explicit about labels. It does **not** assert an unlabeled
`SameMPV₂ (blockTensor (blocks k) F.p) ...`; instead it uses `F.oneShotReindexedBlock k`,
which includes the explicit blocked-word reindexing from iterated blocking to one-shot
blocking.  Because the relabeling can depend on the nonzero-weight block through `F.period k` and
`F.extra k`, a global label-independent equality for the original weighted nonzero part is
not claimed here.

## Interface toward the #970/#944 span adapter

Current `main` already contains the span adapter from #976:

- `MPSTensor.MPVBlockPhaseEquiv`;
- `MPSTensor.mpv_span_eq_of_common_phase_cover`;
- `MPSTensor.fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_phaseCover`.

This branch therefore aims only to make the #969 common-blocking data closer to the
exact nonzero-part data those theorems will eventually need. The new data provide:

- **Sector families:** `family.commonFlatBlocks` at physical dimension
  `blockPhysDim d family.p`.
- **Weights:** `family.commonFlatWeight μ`, equal to `(μ k) ^ family.p` on every sector
  coming from nonzero-weight block `k`; `family.commonFlatWeight_ne_zero` proves nonvanishing from
  the original nonzero weights.
- **TP/primitive/irreducible/positive dimension:** the `commonFlatBlocks_*` theorems give
  all four structural properties needed before a later injectivity refinement.
- **Exact relabeled nonzero decomposition:**
  `family.sameMPV₂_weightedOneShotReindexedBlock_commonFlat` proves that the weighted
  family of explicitly relabeled one-shot nonzero-weight blocks has the same MPV family as the
  flattened common sectors.
- **Zero-tail equations after common reblocking:**
  `fundamentalTheorem_after_blocking_1606_reindexed_commonSector_live_with_zeroTail`
  records the zero-tail/live equation for `blockTensor A familyA.p` and `blockTensor B familyB.p`
  with canonical blocked nonzero-weight blocks, and separately records the relabeled common-sector
  flattening.

The theorem **does not yet** supply the final exact decomposition
`SameMPV₂ (blockTensor A p) (toTensorFromBlocks ... commonFlatBlocks)` in canonical physical
labels.  It supplies the exact decomposition for the explicitly relabeled nonzero-block family.
This is intentional: `iteratedBlockIndex` is a real blocked-word reindexing, and the branch
keeps it visible rather than asserting label-independent equality.

## Remaining blockers after this branch

1. **Global agreement after reindexing blocked physical words.** The branch proves the strongest currently exact
   statement with explicit per-block relabeling. To feed exact nonzero-part theorems that expect
   canonical `blockTensor A p` labels, one still needs either a global relabeling statement or a
   later theorem formulated for this explicit relabeled family.
2. **One common length for both sides plus injectivity.**  The current one-sided families have
   their own common lengths.  The final #944/#652 route needs a combined refinement that also
   performs the Wielandt/injectivity blocking stage flagged in #969.
3. **Common phase-cover maps.**  #976 provides the span adapter, but the actual surjective maps
   from the final nonzero-sector families to a common MPV phase-cover family still have to be
   constructed from the structural equal-MPV data.
4. **Zero-tail closure at the final exact nonzero-part theorem.**  This branch transports the zero-tail
   equations through each side's common reblocking.  The final theorem still has to align the
   two sides at the same physical blocking length and settle the exact length-zero contribution.
