# PGVWC07 intermediate-step restoration report

> **PR split note.** This report describes the *combined* restoration across
> two stacked pull requests:
>
> * **PR #1992 (this PR, `cleanup/canonical-blueprint-trim`)** — restores the
>   13 INTERMEDIATE PLUMBING entries to
>   `blueprint/src/chapter/ch08_canonical.tex` in the new section
>   `sec:pgvwc07_intermediates`. Section (a) below.
> * **PR #1993 (companion, `cleanup/canonical-lean-trim`)** — un-privatizes
>   the corresponding 10 Lean declarations whose blueprint entries are
>   restored here. Section (b) below.
>
> All Lean declarations referenced by the restored blueprint entries are
> *already public on `main`*, so PR #1992 stands alone:
> `leanblueprint web` runs cleanly against `main`. The un-privatization
> in PR #1993 only matters once the companion PR's privatization edits are
> applied. Sections (b)–(e) below therefore describe state that exists on
> the *stack of both PRs*, not on PR #1992 in isolation.

This report records a partial reversal of Step 5.1 (blueprint trim) and Step 5.2
(Lean privatization) of the canonical-form refactor. The 13 intermediate
PGVWC07 entries listed in `audits/canonical_audit.md` §2 as INTERMEDIATE
PLUMBING — recording the source proof structure of
\cite[Theorem~Th:TIcanonical]{PerezGarcia2007Matrix} — have been restored to
the blueprint, and their corresponding Lean declarations have been
un-privatized. The four LEGACY DEAD BRANCH entries identified in the audit
remain deleted from the blueprint, and the Lean code for those was already
removed in Step 5.2 and stays removed.

## (a) Restored blueprint entries

A new section
`\section{Source-faithful PGVWC07 intermediate steps}\label{sec:pgvwc07_intermediates}`
has been appended to `blueprint/src/chapter/ch08_canonical.tex`. It opens
with an 8-line preface explaining that the 13 entries follow the source proof
order and are not consumed by the canonical-form reduction used in the proof
of the Fundamental Theorem. The 13 entries appear in the same order they had
in the original (pre-Step-5.1) chapter:

1. `thm:pgvwc07_irreducible_unital_dual_package`
   (Lean: `MPSTensor.exists_pgvwc07_unital_dualDiag_data_of_irreducible`)
2. `thm:pgvwc07_blockwise_unital_dual_package`
   (Lean: `MPSTensor.exists_pgvwc07_unital_dualDiag_blockwise`)
3. `thm:pgvwc07_arbitrary_zero_tail_unital_dual_package`
   (Lean: `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail`)
4. `thm:pgvwc07_arbitrary_zero_tail_unital_dual_bond_dim_bound`
   (Lean: `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`)
5. `thm:pgvwc07_arbitrary_positive_length_unital_dual_bond_dim_bound`
   (Lean: `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound`)
6. `def:pgvwc07_positive_length_witness`
   (Lean: `MPSTensor.PGVWC07PositiveLengthWitness`)
7. `thm:pgvwc07_positive_length_witness_weight_normalization`
   (Lean: `MPSTensor.PGVWC07PositiveLengthWitness.exists_weight_normalization`)
8. `thm:pgvwc07_positive_length_witness_weight_normalization_projective`
   (Lean: `MPSTensor.PGVWC07PositiveLengthWitness.exists_weight_normalization_projective`)
9. `lem:pgvwc07_positive_length_witness_nonempty_of_nonzero_mpv`
   (Lean: `MPSTensor.PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv`)
10. `thm:pgvwc07_nonzero_normalized_projective_form`
    (Lean: `MPSTensor.exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv`)
11. `thm:pgvwc07_nonzero_normalized_exact_rescaled_form`
    (Lean: `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv`)
12. `thm:pgvwc07_exact_rescaled_form_zero_nonzero_dichotomy`
    (Lean: `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_or_forall_pos_mpv_eq_zero`)
13. `thm:pgvwc07_positive_length_witness`
    (Lean: `MPSTensor.exists_pgvwc07_positiveLengthWitness`)

### LaTeX title renames in the restored block

In the original HEAD version, three of these entries used the banned word
"package" (per `docs/prose_style.md` §2). Per the restoration task, the
displayed titles have been renamed:

* (entry 1) "Single irreducible-block PGVWC07 canonical-form theorem" — kept
  as is (already source-faithful and free of banned terms).
* (entry 2) "Blockwise PGVWC07 unital and dual-diagonal data" → "Blockwise
  PGVWC07 unital and dual-diagonal block decomposition".
* (entry 3) "Arbitrary-input PGVWC07 unital dual-diagonal form with zero
  block" — kept as is (already neutral).

The blueprint labels are unchanged. The Lean tags (the `\lean{...}` arguments)
are unchanged: they remain `exists_pgvwc07_unital_dualDiag_*` and
`PGVWC07PositiveLengthWitness*`.

Inside the body of entry 2 the phrase "blockwise assembly of \cite[...]
{PerezGarcia2007Matrix}" was replaced by "blockwise composition of \cite[...]
{PerezGarcia2007Matrix}" to comply with the §2 ban on "assembly".

### Legacy-dead entries kept removed

The four LEGACY DEAD BRANCH labels classified in
`audits/canonical_audit.md` §2 remain absent from the blueprint:

* `thm:pgvwc07_exact_rescaled_form_allow_empty` (duplicate of the headline
  `thm:pgvwc07_ti_canonical_form` — same Lean tag)
* `thm:pgvwc07_exact_rescaled_form_with_zero_tail` (Lean decl deleted in
  Step 5.2)
* `thm:pgvwc07_projective_form_zero_nonzero_dichotomy` (Lean decl deleted)
* `lem:pgvwc07_positive_length_witness_weight_ne_zero` (Lean decl deleted)

## (b) `private` keywords removed

The following 10 theorems had their `private` keyword removed:

In `TNLean/MPS/CanonicalForm/NormalReduction/TPGauge.lean`:

* `exists_pgvwc07_unital_dualDiag_data_of_irreducible`
* `exists_pgvwc07_unital_dualDiag_blockwise`
* `exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail`
* `exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound`

In `TNLean/MPS/CanonicalForm/NormalReduction/WeightNormalization.lean`:

* `PGVWC07PositiveLengthWitness.exists_weight_normalization`
* `PGVWC07PositiveLengthWitness.exists_weight_normalization_projective`
* `PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv`
* `exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv`
* `exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv`
* `exists_pgvwc07_normalized_exact_form_after_rescaling_or_forall_pos_mpv_eq_zero`

The structure `MPSTensor.PGVWC07PositiveLengthWitness` was already public
during Step 5.2 (because of cross-file usage between `TPGauge.lean` and
`WeightNormalization.lean`); confirmed by
`grep -n "structure PGVWC07PositiveLengthWitness" TNLean/MPS/CanonicalForm/NormalReduction/TPGauge.lean`
returning `73:structure PGVWC07PositiveLengthWitness (A : MPSTensor d D) where`
with no `private` keyword. Likewise the existence theorem
`exists_pgvwc07_positiveLengthWitness` and the bond-dim bound theorem
`exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`
in `TPGauge.lean` were already public prior to this restoration.

The three remaining `private theorem` declarations in `TPGauge.lean`
(`isIrreducibleAction_gaugeEquiv`, `isIrreducibleTensor_tpGauge_of_isIrreducibleTensor`,
and `scalar_fixedPoints_unitaryConj`) are auxiliary gauge-transport lemmas with
no blueprint entry and no external API role; they stay `private`. This matches
the module docstring updates in `TPGauge.lean` and `WeightNormalization.lean`,
and the bullet list in the top-level `TNLean/MPS/CanonicalForm/NormalReduction.lean`
docstring, which now lists all 12 restored declarations + the headline
`exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty`.

## (c) Final blueprint LOC for `ch08_canonical.tex`

```
$ wc -l blueprint/src/chapter/ch08_canonical.tex
    1987 blueprint/src/chapter/ch08_canonical.tex
```

(Up from 1608 LOC before restoration; the appended section adds 379 lines.)

## (d) Final `lake build` time

```
Build completed successfully (8728 jobs).

real    0m57.914s
user    0m44.064s
sys     0m33.618s
```

`lake build` exit 0. The pre-existing `sorry`-warnings in
`TNLean/MPS/Periodic/Overlap/*.lean` and the single long-line style warning
in `TNLean/Spectral/GaugeConstruction.lean` are unrelated to this restoration
and are unchanged.

## (e) Confirmation that `leanblueprint web` ran cleanly

```
$ cd blueprint && rm -f src/print.aux print/print.aux && leanblueprint web 2>&1 | tail -10
... (chapter list, no errors)
exit=0
```

`grep -iE 'error|undef|missing' /tmp/blueprint.log | grep -ivE 'unrecognized command'`
returns empty. The only warnings in the leanblueprint output are pre-existing
plasTeX `unrecognized command/environment` notes for TikZ macros and "Using
default renderer" messages for PEPS environments — both pre-date this
restoration and are unaffected by it.

## Verification command results

Verification step 3 from the task:

```
$ grep -nE '\\label\{(thm|def|lem):pgvwc07' blueprint/src/chapter/ch08_canonical.tex
32:    \label{thm:pgvwc07_ti_canonical_form}
697:    \label{thm:pgvwc07_dual_diag_unital}
1626:    \label{thm:pgvwc07_irreducible_unital_dual_package}
1667:    \label{thm:pgvwc07_blockwise_unital_dual_package}
1704:    \label{thm:pgvwc07_arbitrary_zero_tail_unital_dual_package}
1741:    \label{thm:pgvwc07_arbitrary_zero_tail_unital_dual_bond_dim_bound}
1766:    \label{thm:pgvwc07_arbitrary_positive_length_unital_dual_bond_dim_bound}
1800:    \label{def:pgvwc07_positive_length_witness}
1817:    \label{thm:pgvwc07_positive_length_witness_weight_normalization}
1847:    \label{thm:pgvwc07_positive_length_witness_weight_normalization_projective}
1877:    \label{lem:pgvwc07_positive_length_witness_nonempty_of_nonzero_mpv}
1896:    \label{thm:pgvwc07_nonzero_normalized_projective_form}
1923:    \label{thm:pgvwc07_nonzero_normalized_exact_rescaled_form}
1955:    \label{thm:pgvwc07_exact_rescaled_form_zero_nonzero_dichotomy}
1971:    \label{thm:pgvwc07_positive_length_witness}
```

This lists 15 labels rather than the 14 stated in the task's verification
clause. The 13 restored labels + the kept headline `thm:pgvwc07_ti_canonical_form`
account for 14; the 15th label `thm:pgvwc07_dual_diag_unital` is the
"Dual diagonalization for irreducible unital blocks" theorem at line 697 of
the trimmed chapter — it was kept in the post-Step-5.1 trim because it is a
prerequisite of the restored `thm:pgvwc07_irreducible_unital_dual_package`
(used in its proof). It is not in the restoration list and is not a
LEGACY DEAD BRANCH entry, so it is correct to leave it in place. The task's
"exactly 14" count appears to have overlooked this pre-existing entry.

Verification step 4 from the task:

```
$ grep -nE '\\lean\{MPSTensor\.(exists_pgvwc07_|PGVWC07)' blueprint/src/chapter/ch08_canonical.tex | wc -l
      14
```

Exactly 14, as expected: 13 restored entries each have one such `\lean{...}`
tag, and the headline `thm:pgvwc07_ti_canonical_form` carries one more. The
`thm:pgvwc07_dual_diag_unital` entry uses the Lean tag
`MPSTensor.exists_unitary_diag_posDef_adjointFixedPoint_of_unital_of_isIrreducibleTensor`,
which is correctly excluded by this regex.
