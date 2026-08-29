# MPDO purification-RFP alias and per-copy horizontal canonical-form deletion (2026-08-26)

This audit records a second slice of the open proof-debt ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564) under `TNLean/MPS/MPDO/`,
complementing `2026-08-26_mpdo_zero_reference_and_pass_through_cleanup.md`.
Two clusters were removed: a definitional alias of the purification
renormalization fixed-point predicate together with the identity theorems
relating it to the predicate it abbreviates, and the per-copy horizontal
canonical-form surface whose only client was itself unused. The removals use
the repository-local pass-through exception of `docs/project_conventions.md`
§Style, so no transition declaration is left behind. At the audited head each
removed name had no non-`Archive` consumer, and each blueprint entry naming
one was deleted rather than redirected, because its mathematical content is
already carried by a surviving entry.

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPOTensor.IsPRFPWithTracePreservingSpinReduction` (`TNLean/MPS/MPDO/PRFP.lean`) | `MPOTensor.IsPRFP` in the same file. The alias was definitionally equal to it; the trace-preserving spin reduction it advertised is proved unconditionally, for every ancillary dimension, by `MPOTensor.hasTracePreservingSpinReduction`, so recording it in a predicate added no hypothesis and no information. |
| `MPOTensor.IsPRFPWithTracePreservingSpinReduction.isPRFP` | None needed: with the alias gone the statement is `IsPRFP M → IsPRFP M`. Its body was `h`. |
| `MPOTensor.IsPRFP.withTracePreservingSpinReduction` | None needed, for the same reason; its body was `h`. |
| `MPOTensor.IsPRFPWithTracePreservingSpinReduction.hasTracePreservingSpinReduction` | `MPOTensor.hasTracePreservingSpinReduction`, which proves the same trace-preserving completely positive structure for every ancillary dimension without assuming a purification fixed point. The removed theorem merely extracted the ancillary dimension from the witness and applied it. |
| `MPOTensor.IsPerCopyHorizontalCF` (`TNLean/MPS/MPDO/PerCopyHorizontalCF.lean`) | `MPOTensor.IsHorizontalCF` (`TNLean/MPS/MPDO/HorizontalBNT.lean`) is the canonical-form predicate the development uses. The removed predicate was a stronger flattened per-copy variant with no consumer and no sanctioned bridge to the survivor; the bundled hypothesis structure `MPOTensor.HorizontalCFData` it packaged is retained and still consumed. |
| `MPOTensor.blockwise_opposite_insert_eq_of_mpv_agree` (same file) | `MPOTensor.blockwise_insert_eq_of_mpv_agree` in the same file, applied twice: the removed theorem chained that theorem's two instances through the shared left action. |
| `MPOTensor.blockwise_opposite_insert_eq_of_rotated_mpo_entries` (same file) | None. Its only caller was the theorem below, which is itself removed here. The invariant-projection conclusion it prepared is proved along the surviving route by `MPOTensor.basis_braRight_eq_ketLeftBraRight_of_invariant` in `TNLean/MPS/MPDO/InvariantProjection.lean`. |
| `MPOTensor.blockwise_braRight_eq_ketLeftBraRight_of_invariant` (`TNLean/MPS/MPDO/InvariantProjection.lean`) | `MPOTensor.basis_braRight_eq_ketLeftBraRight_of_invariant` in the same file, which draws the same blockwise conclusion from the representative-indexed canonical form instead of the stronger per-copy separation hypothesis. |

## Blueprint deletions

* `def:mpdo_prfp_trace_preserving_spin_reduction` and
  `lem:mpdo_prfp_trace_preserving_spin_reduction_iff`
  (`blueprint/src/chapter/ch21_mpdo_rfp_foundations.tex`) were deleted with
  their proof environment. The definition restated
  `def:mpdo_is_prfp`, and the lemma asserted the resulting vacuous
  equivalence. No surviving `\uses` or `\ref` names either label; the
  trace-preserving reduction itself remains stated at
  `cor:mpdo_has_trace_preserving_spin_reduction`, which is universal in the
  ancillary dimension.
* No blueprint entry named any per-copy horizontal declaration.
  `lem:blockwise_insert_eq_of_mpv_agree`
  (`blueprint/src/chapter/ch20_mpdo_canonical_forms_first_site_contractions.tex`)
  points at the surviving `MPOTensor.blockwise_insert_eq_of_mpv_agree` and is
  unchanged.

## Retained on purpose

* `MPOTensor.hasTracePreservingSpinReduction` (`TNLean/MPS/MPDO/PRFP.lean`)
  now has no Lean consumer, but it carries the `\lean{}` tag of
  `cor:mpdo_has_trace_preserving_spin_reduction` and states the tpCPM
  structure of arXiv:1606.00608, lines 761--764. Blueprint-cited declarations
  are load-bearing; it stays.
* `MPOTensor.HorizontalCFData` and `MPOTensor.blockwise_insert_eq_of_mpv_agree`
  stay: the structure is consumed by the surviving Lemma L, and Lemma L is
  blueprint-tagged and used along the horizontal-to-vertical route.
* `docs/paper-gaps/cpgsv17_bicf_block_separation.tex` stays: the scope
  restriction it records is still carried by the retained `biCF` field of
  `HorizontalCFData`.

## Documentation

* `docs/glossary.md`: the `MPOTensor.IsPerCopyHorizontalCF` bullet was removed
  from the MPDO canonical-form predicate list. The `IsHorizontalCF` and
  `IsVerticalCF` bullets are unchanged.
* `TNLean/MPS/MPDO/PerCopyHorizontalCF.lean`: the module docstring no longer
  advertises the removed consequences for the three contractions of
  Proposition 4.13.
* `TNLean/MPS/MPDO/InvariantProjection.lean`: the now-unused import of
  `TNLean.MPS.MPDO.PerCopyHorizontalCF` was dropped.

## Subsequent PRFP correction

On 2026-08-28, `MPOTensor.IsPRFP` was changed from the bare positive-length
global witness to the one-site ancillary-contraction presentation intended by
CPSV16 Definition 4.3. This does not alter the alias-deletion result recorded
above: the removed trace-preserving-spin-reduction predicate was definitionally
redundant at the audited head. The global family equation now remains as the
separate predicate `MPOTensor.HasGlobalPurificationEquation` and is a theorem
of the source-facing `IsPRFP` predicate.
