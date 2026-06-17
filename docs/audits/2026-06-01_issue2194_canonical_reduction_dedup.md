# Issue 2194 canonical-form reduction deduplication audit

Date: 2026-06-01.

This note records the final audit for issue #2194, whose subject is the
deduplication of canonical-form reduction declarations common to the
single-tensor and after-blocking chapters.

The audit was run on `origin/main` at commit
`aeb6bb617560432d3afe3d445fc10c5cc9f307bc`, after PR #2219 had merged.

## Scope

The checked blueprint chapters are:

- `blueprint/src/chapter/ch08_canonical.tex`
- `blueprint/src/chapter/ch11b_after_blocking.tex`

The checked Lean files are the canonical-form reduction and sector-comparison
files under `TNLean/MPS/CanonicalForm/`, together with the downstream
fundamental-theorem supplier files that consume the common-sector results.

## Conclusion

The issue #2194 audit is complete for the canonical-form reduction chain.
The remaining Chapter 8 and Chapter 11b `\lean{}` tags point to existing Lean
declarations, and the recent sequence of cleanup PRs has removed or internalized
the redundant declaration layers listed in the issue discussion.

The remaining public statements have distinct mathematical roles:

- `MPSTensor.exists_tp_gauge_blockwise` is the blockwise TP-gauge theorem.
  `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail` derives the
  arbitrary-input zero-tail statement from it after irreducible block
  decomposition.
- `MPSTensor.exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`
  is the period-removal existence theorem for an irreducible TP tensor.
  `MPSTensor.primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking`
  is the sector-block theorem used inside that construction and kept as a named
  public result because Chapter 11b cites it directly.
- `MPSTensor.CommonBlockedCyclicSectorFamily.derived_properties`,
  `MPSTensor.CommonBlockedCyclicSectorFamily.reindexed_sameMPV₂`,
  `MPSTensor.CommonBlockedCyclicSectorFamily.reindexed_nonzero_part`, and
  `MPSTensor.CommonBlockedCyclicSectorFamily.blockTensor_sameMPV₂_commonReindexedBlock`
  are the surviving common-sector sources. The one-line projection and
  nonvanishing wrappers removed in PRs #2212 through #2219 are no longer cited
  in Chapter 8 or Chapter 11b.

## Verification

The canonical-form and sector-comparison targets build:

```text
lake build \
  TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorTransport \
  TNLean.MPS.CanonicalForm.SectorComparison.TPPrimitiveReduction \
  TNLean.MPS.CanonicalForm.NormalReduction \
  TNLean.MPS.CanonicalForm.Existence
```

Result:

```text
Build completed successfully (8516 jobs).
```

The root import builds:

```text
lake build TNLean
```

Result:

```text
Build completed successfully (8746 jobs).
```

The build emitted only pre-existing `sorry` warnings in PEPS and periodic
overlap files, not in the files touched by the canonical-form deduplication
sequence.

The blueprint web build succeeds:

```text
leanblueprint web
```

The only warning observed was the pre-existing unrecognized `path` command.

The blueprint/Lean synchronization script reports no missing Lean declarations
in the two chapters of this audit:

```text
python3 scripts/blueprint_lean_sync.py --root . --ci \
  --report /tmp/issue2194_blueprint_sync.json
```

Relevant chapter statistics:

```text
ch08_canonical.tex: total 48, formalized 47, missing_lean 0
ch11b_after_blocking.tex: total 11, formalized 11, missing_lean 0
```

The command exits nonzero because of unrelated missing declarations in the PEPS
and parent-Hamiltonian chapters. Those failures are outside the scope of issue
#2194.

Finally, filtering the declaration checker to the 59 Lean names occurring in
Chapter 8 and Chapter 11b succeeds:

```text
perl -ne 'while(/\\lean\{([^}]*)\}/g){ print "$1\n" }' \
  blueprint/src/chapter/ch08_canonical.tex \
  blueprint/src/chapter/ch11b_after_blocking.tex \
  | sort -u > /tmp/issue2194_canonical_lean_decls

lake exe checkdecls /tmp/issue2194_canonical_lean_decls
```

Result: exit code `0`.

## Stale-name search

No occurrence was found in the live canonical-form Lean files, the relevant
fundamental-theorem supplier files, or the two audited blueprint chapters for
the retired names:

```text
isNormalCanonicalForm_of_tp_primitive_irr_sorted
exists_normalCanonicalForm_of_primitive_input
exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero
isNormal_live_block_of_primitive
nestedBlock_sameMPV₂_commonReindexedBlock
CommonGroupedBlockCastHypothesis
CommonSectorRelabelingHypothesis
hasPrimitiveIrreducibleCyclicSectors_of_TP_of_isIrreducibleTensor
exists_blockTensor_isInjective_of_tp_primitive_irreducible
blocked_word_comparison
commonFlatWeight_ne_zero
common_blocked_cyclic_sector_flat_weight_ne_zero
```

Historical audit notes still mention some of these names as archaeology. Those
mentions are not live theorem references and do not affect Chapter 8 or Chapter
11b.

