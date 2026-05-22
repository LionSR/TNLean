# Canonical-form Lean refactor — Step 5.2 + 5.3 + 5.4 report

Scope: `TNLean/MPS/CanonicalForm/` and `blueprint/src/chapter/ch11b_after_blocking.tex`.

## 1. Build times

Cached-warm baseline `lake build` (full project, before refactor):
incremental rebuild on clean tree ≈ 4 s; cold uncached time not measured
(local cache served).  Cold uncached time was not available at the start of
the session because the workspace was already cached.

Post-refactor checkpoint after privatization + deletions (incremental from
the cache):

```
lake build  # full project — exit 0, 8728 jobs replayed/built
```

The two intermediate build checkpoints during the refactor took 45–55 s
wall-clock (driven by the changed files' downstream rebuilds in
`SectorComparison/`, `BNTGrouping`, and `PhaseClassSectorData`).
After the final trim the full `lake build` completed cleanly (exit 0;
sorries warnings preserved from `MPS/Periodic/Overlap/Case*.lean`, which
are out of scope here).

## 2. Declarations privatized

> **Audit-vs-final-state correction (post-review).** A first version of this
> report described 13 declarations as "privatized"; in fact only the
> SectorComparison/CommonSectorTransport.lean entries received the `private`
> keyword.  The PGVWC07 declarations in TPGauge.lean and WeightNormalization.lean
> were planned for privatization in Step 5.2 but later restored to public
> visibility in the PGVWC07 restoration step (see
> `audits/pgvwc07_restoration_report.md` and the `rev:` note in the next
> subsection below).  Only the public/private columns of the table below
> reflect the *final state on the PR HEAD*; the "PGVWC07 stack" rows are kept
> for historical traceability.

All call-graph verifications were done with
`grep -rln 'DeclName' TNLean --include='*.lean'` and confirmed the only
hits were either the definition file itself or module-summary docstrings
(no real call sites).  Lean `private` is file-scoped: only declarations whose
call sites all live in the same `.lean` file are eligible for `private`.

Declarations marked `private` on PR HEAD (final state):

| File | Declaration | Reason |
|---|---|---|
| `SectorComparison/CommonSectorTransport.lean` | `zeroTail_commonFlat_of_blockwise` | file-local; intermediate-hypothesis form |
| `SectorComparison/CommonSectorTransport.lean` | `zeroTail_commonFlat_of_groupedBlockCastAgrees` | file-local; intermediate-hypothesis form |

PGVWC07 stack — planned `private` (Step 5.2), then restored to public:

| File | Declaration | Original Step-5.2 plan | Final state |
|---|---|---|---|
| `NormalReduction/TPGauge.lean` | `exists_pgvwc07_unital_dualDiag_data_of_irreducible` | privatize (file-local) | **public** (blueprint entry restored in `sec:pgvwc07_intermediates`) |
| `NormalReduction/TPGauge.lean` | `exists_pgvwc07_unital_dualDiag_blockwise` | privatize (file-local) | **public** (blueprint entry restored) |
| `NormalReduction/TPGauge.lean` | `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail` | privatize (file-local) | **public** (blueprint entry restored) |
| `NormalReduction/TPGauge.lean` | `exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound` | privatize (file-local) | **public** (blueprint entry restored) |
| `NormalReduction/WeightNormalization.lean` | `PGVWC07PositiveLengthWitness.exists_weight_normalization` | privatize | **public** (blueprint entry restored) |
| `NormalReduction/WeightNormalization.lean` | `PGVWC07PositiveLengthWitness.exists_weight_normalization_projective` | privatize | **public** (blueprint entry restored) |
| `NormalReduction/WeightNormalization.lean` | `PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv` | privatize | **public** (blueprint entry restored) |
| `NormalReduction/WeightNormalization.lean` | `exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv` | privatize | **public** (blueprint entry restored) |
| `NormalReduction/WeightNormalization.lean` | `exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv` | privatize | **public** (blueprint entry restored) |
| `NormalReduction/WeightNormalization.lean` | `exists_pgvwc07_normalized_exact_form_after_rescaling_or_forall_pos_mpv_eq_zero` | privatize | **public** (blueprint entry restored) |

Always public (cross-file callees, never privatized):

| File | Declaration | Reason for keeping public |
|---|---|---|
| `NormalReduction/TPGauge.lean` | `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound` | cross-file: called from `WeightNormalization.lean` |
| `NormalReduction/TPGauge.lean` | `exists_pgvwc07_positiveLengthWitness` | cross-file: called from `WeightNormalization.lean` |
| `NormalReduction/TPGauge.lean` | `PGVWC07PositiveLengthWitness` (structure) | cross-file: used as type in `WeightNormalization.lean` |
| `SectorComparison/CyclicSectorDecomposition.lean` | `exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` | blueprint tag `thm:cyclic_sector_decomp_irr_tp` survives Step 5.1; docstring expanded to note `_prim_irr` is the consumed variant |
| `SectorComparison/CommonSectorTransport.lean` | `CommonSectorRelabelingHypothesis`, `CommonGroupedBlockCastHypothesis` | both blueprint-tagged; collapsing would touch >1 downstream file (audit S5.2.11 fallback). Module-head docstring now records that they are equivalent reformulations connected by the unconditional `of_flattenWordOfBlock_cast_eq`. |

### Privatization rationale: cross-file PGVWC07 callees

`exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`,
`exists_pgvwc07_positiveLengthWitness`, and the structure
`PGVWC07PositiveLengthWitness` are used across the
`TPGauge.lean` ↔ `WeightNormalization.lean` file split.  Lean 4 `private`
is file-scoped, so privatizing them would break the build.  They remain
public; the `NormalReduction.lean` module-header docstring is shortened
to the headline plus a pointer to `sec:pgvwc07_intermediates` rather than
enumerating every intermediate.

## 3. Declarations deleted

Each deletion was preceded by
`grep -rn 'DeclName' TNLean blueprint/src` and verified to return only
the definition site + module docstring lines.

| File | Declaration | Verification |
|---|---|---|
| `NormalReduction/WeightNormalization.lean` | `exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail` | grep: def site + `NormalReduction.lean` docstring only |
| `NormalReduction/WeightNormalization.lean` | `exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero` | grep: def site + `NormalReduction.lean` docstring + an unused intra-file comment line (cleaned up) |
| `NormalReduction/TPGauge.lean` | `PGVWC07PositiveLengthWitness.weight_ne_zero` | grep: def site only |
| `SectorComparison/CommonSectorData.lean` | `afterBlocking_reindexedCommonSectorDataWithZeroTail_of_sameMPV₂` | grep: def site + an intra-file companion-comment reference (cleaned up) |
| `SectorComparison/CommonSectorData.lean` | `afterBlocking_commonLengthCommonSectorData_of_reindexed` | grep: def site + module docstring bullet (cleaned up) |
| `SectorComparison/StructuralData.lean` | `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂` | grep: def site + module docstring bullet (cleaned up) |

Note: the audit recipe noted (for deletion #4) that the candidate
`afterBlocking_commonLengthCommonSectorData_of_reindexed` is in
`CommonSectorData.lean`, not `CommonSectorTransport.lean`.  Confirmed and
removed from `CommonSectorData.lean` line 340.

## 4. Plumbing trims applied (S5.4)

| File | Before LOC | After LOC | Delta | Trim description |
|---|---|---|---|---|
| `NormalReduction/TPGauge.lean` | 935 | 918 | −17 | Deleted `PGVWC07PositiveLengthWitness.weight_ne_zero` (a 6-line theorem that was already a one-line `obtain ⟨a, ha_pos, h⟩ := W.weight_pos k; …`); no remaining callers. |
| `NormalReduction/WeightNormalization.lean` | 598 | 432 | −166 | Deleted two dead theorems (`_after_rescaling_with_zeroTail`, `_projective_form_or_forall_pos_mpv_eq_zero`) plus tidied the docstring on `_or_forall_pos_mpv_eq_zero` private theorem. |
| `Existence.lean` | 630 | 595 | −35 | After privatization, both `exists_blockTensor_isPrimitive` and `exists_blockTensor_leftCanonical_isPrimitive` had no remaining external callers (and only the latter consumed the former).  Both are thin `NeZero`-wrappers around `exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor`.  Deleted both. |
| `SectorComparison/CommonSectorTransport.lean` | 679 | 642 | −37 | After privatizing the five `_of_blockwise / _of_word_eq / _of_groupedBlockCastAgrees` variants, two of them (`zeroTail_commonFlat_of_word_eq` and `sameMPV₂Pos_blockTensor_commonFlatAt_of_groupedBlockCastAgrees`) had no remaining intra-file callers.  Deleted both. |
| `SectorComparison/CommonSectorData.lean` | 634 | 366 | −268 | Combined effect of the two S5.3 deletions in this file (the dead `WithZeroTail_of_sameMPV₂` and `commonLengthCommonSectorData_of_reindexed` theorems with their docstrings). |
| `SectorComparison/StructuralData.lean` | 228 | 176 | −52 | S5.3 deletion of `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂`. |
| `NormalReduction.lean` | 46 | 46 | ±0 | Module docstring rewritten (LOC unchanged, but reduced from a 17-bullet list to a 4-bullet headline list). |

Aggregate canonical-form LOC delta:

```
Baseline   (canonical-form files listed above): 4386
After      (canonical-form files listed above): 3817
Delta:                                          −569 LOC (−13%)
```

The single biggest reduction is in `CommonSectorData.lean` (−268 LOC),
driven by removal of the two giant existential statements that had no
downstream consumer.

## 5. Blueprint cross-edits

These blueprint edits land in the **companion PR #1992**, not in this PR.
They are described here because the Lean-side privatizations and deletions
in this PR motivated them.

`blueprint/src/chapter/ch11b_after_blocking.tex`, theorem
`thm:zero_tail_common_flat_of_blocked_word_comparison`:

* The five-name `\lean{...}` block and the `\leanok` were removed (all
  five Lean declarations are now `private` or deleted on this PR's HEAD).
* The trailing sentence "The blockwise comparison, the word equality, and
  the coordinate-grouping condition are three ways to supply the same
  alphabet identification" was rewritten to a sentence pointing the reader
  to `thm:zero_tail_common_flat_of_reindexed` for the externally consumed
  form.  The blueprint `\uses{...}` chain to consumers was left intact:
  the theorem still exists as a mathematical waypoint, it just no longer
  claims a Lean tag.

No `blueprint/src/chapter/` files were modified by this PR; the edits
above land in PR #1992.

## 6. Risky things deliberately not done

The orchestrator's follow-up explicitly called out three risk classes; I
honored them.

* **Cross-file PGVWC07 privatization was declined.** Three declarations
  (`exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`,
  `exists_pgvwc07_positiveLengthWitness`, `PGVWC07PositiveLengthWitness`)
  are called across the `TPGauge.lean` / `WeightNormalization.lean` file
  split.  Plan (C) — folding `WeightNormalization.lean` into `TPGauge.lean`
  — would push the combined file to ≈1 350 LOC; this is within the
  orchestrator's 1 500 cap but the merge would touch the
  `exists_weight_normalization` proofs (≈250 LOC of weight-rescaling
  algebra), which is more invasive than this refactor was meant to be.
  I left it for a follow-up.

* **`exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor` was not
  privatized.**  The blueprint tag `thm:cyclic_sector_decomp_irr_tp`
  survived Step 5.1, so the audit's "fallback A" applies: leave public
  and add a docstring sentence pointing at the consumed `_prim_irr`
  variant.

* **`CommonSectorRelabelingHypothesis` / `CommonGroupedBlockCastHypothesis`
  collapse was deferred.**  Audit S5.2.11 says collapse only if it does
  not touch more than one downstream file.  Both predicates are
  blueprint-tagged (`thm:zero_tail_common_flat_transport_of_grouped_block_cast`
  and the surrounding theorems consume the predicate forms).  Collapsing
  would force matching changes in `CommonSectorData.lean` and in three
  consumer theorems in the same file.  Added a head-of-section comment
  in `CommonSectorTransport.lean` recording that the pair is a thin
  compatibility layer and that `of_flattenWordOfBlock_cast_eq` already
  proves the conversion unconditionally; left the two predicates alone
  pending a separate refactor.

* **No `noncomputable def` / `@[simp] rfl` → `abbrev` conversions
  applied.**  I scanned the touched files for them; the only `noncomputable def`s
  in `CanonicalForm/` (e.g. `gaugeMulVecLinearEquiv` in `TPGauge.lean`)
  are not `rfl`-shaped (they bundle four `LinearEquiv` fields), so they
  cannot become `abbrev`s.  No safe one-line collapses were found in the
  files in scope.

* **No collapse of `intro/refine/exact ⟨..., ..., ...⟩` proof patterns
  attempted.**  The dependent-product proofs in `CommonSectorData.lean`
  and `StructuralData.lean` use `refine ⟨…, ?_, ?_, …⟩` followed by
  bullet sub-goals where each branch typically calls a named lemma; the
  bullets are not all single-`simp`-closable, so the audit's S5.4
  recommendation does not apply cleanly.  Leaving alone.

* **Parallel "with weights / without weights" pair candidates.**  Two
  parallel lemma pairs in `SectorComparison/CommonSectorTransport.lean`
  look superficially like trivial-corollary pairs:
  `zeroTail_commonFlat_of_reindexed`  vs. its `_commonFlatAt_of_reindexed`
  companion, and `sameMPV₂Pos_blockTensor_commonFlatAt_of_reindexed`
  vs. `zeroTail_commonFlat_transport_of_reindexed`.  All four are public
  and blueprint-tagged (see `thm:zero_tail_common_flat_of_reindexed` and
  `thm:zero_tail_common_flat_transport_of_reindexed`), so consolidation
  is a blueprint-touching action and out of scope for this Lean-only
  step.  Listed here per the user's S5.4 reporting requirement.

## 7. Verification commands re-run after refactor

For every declaration that was privatized or deleted I re-ran
`grep -rn 'DeclName' TNLean blueprint/src` and confirmed no new caller
appeared during the refactor.  For the surviving public declarations I
verified the blueprint `\lean{...}` tags by extracting the tag list:

```
grep -roh '\\lean{[^}]*}' blueprint/src/chapter/ \
  | sed 's/\\lean{//;s/}//' | tr ',' '\n' \
  | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sort -u
```

PROTECTED list cross-checked against this output: every declaration
required by the audit's "PROTECTED" set still has a public Lean
counterpart with a matching blueprint tag.

## 8. Final status

* `lake build` exits 0 (8728 jobs).
* No new sorries introduced.
* Style-linter warnings unchanged (the pre-existing
  `Spectral/GaugeConstruction.lean:669` long-line and the two `simp`
  flexibility infos in `WeightNormalization.lean` lines 538–539 are
  pre-existing and out of scope).
* Pre-existing sorries in `MPS/Periodic/Overlap/` are untouched.
* No file under `MPS/FundamentalTheorem/`, `MPS/BNT/`, `MPS/Periodic/`,
  `MPS/ParentHamiltonian/`, or `Archive/` was modified.
* `lakefile.toml` and `lean-toolchain` are unchanged.
