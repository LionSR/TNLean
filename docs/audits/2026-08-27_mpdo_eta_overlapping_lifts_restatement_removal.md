# MPDO eta-local overlapping-lift restatement removal (2026-08-27)

This audit continues the slice of the open proof-debt ledger entry S2
(`docs/proof_debt_ledger.md`, issue #4564) begun by
`docs/audits/2026-08-26_mpdo_zero_reference_and_pass_through_cleanup.md`:
declarations under `TNLean/MPS/MPDO/` that merely restate, one abstraction
layer up, a theorem already proved for the underlying data.

`MPOTensor.EtaLocalStructureData` carries a `bondData` field of type
`MPOTensor.TranslationInvariantBondData`, and its `pairBond` is by definition
`data.bondData.pairBond`. Four theorems in
`TNLean/MPS/MPDO/CommutingOverlappingCoordinates.lean` therefore stated nothing
beyond their `TranslationInvariantBondData` twins in the same file; each body
was the single projection `data.bondData.<twin>`. At the audited head none of
the four had a consumer anywhere outside its own defining block: the two call
sites that read like consumers —
`TNLean/MPS/MPDO/CommutingFormSpatialBridge.lean:61--63` and
`TNLean/MPS/MPDO/CommutingBondEtaDecomposition.lean:315` — are inside theorems
whose `data` is a `TranslationInvariantBondData`, so they resolve to the
surviving twins. The removals use the repository-local pass-through exception
of `docs/project_conventions.md` §Style, so no transition declaration is left
behind.

## Removed declarations

All four removed names lived in
`TNLean/MPS/MPDO/CommutingOverlappingCoordinates.lean`, namespace
`MPOTensor.EtaLocalStructureData`; all four replacements live in the same file,
namespace `MPOTensor.TranslationInvariantBondData`, reached from an eta-local
structure by `data.bondData`.

| Removed | Replacement |
|---|---|
| `MPOTensor.EtaLocalStructureData.pairBond_isHermitian` | `MPOTensor.TranslationInvariantBondData.pairBond_isHermitian` at `data.bondData`. The removed theorem's whole body was that projection. |
| `MPOTensor.EtaLocalStructureData.reindex_bondAt_zero_eq_leftOverlappingLift` | `MPOTensor.TranslationInvariantBondData.reindex_bondAt_zero_eq_leftOverlappingLift` at `data.bondData`; the eta-local length-three form `data.formAt 3` is the commuting-form data of `data.bondData`, so the two statements coincide. |
| `MPOTensor.EtaLocalStructureData.reindex_bondAt_one_eq_rightOverlappingLift` | `MPOTensor.TranslationInvariantBondData.reindex_bondAt_one_eq_rightOverlappingLift` at `data.bondData`, by the same identification. |
| `MPOTensor.EtaLocalStructureData.overlappingLifts_pairBond_comm` | `MPOTensor.TranslationInvariantBondData.overlappingLifts_pairBond_comm` at `data.bondData`. |

## Blueprint and documentation redirects

* `thm:mpdo_eta_bond_overlapping_lifts`
  (`blueprint/src/chapter/ch21_mpdo_rfp_commuting_form_bond_products.tex`): the
  four `MPOTensor.EtaLocalStructureData.*` tags were dropped. The entry keeps
  `MPOTensor.reindex_embedLocalOperator_zero_eq_leftOverlappingLift`,
  `MPOTensor.reindex_embedLocalOperator_one_eq_rightOverlappingLift`,
  `MPOTensor.TranslationInvariantBondData.pairBond_isHermitian`, and the three
  remaining `MPOTensor.TranslationInvariantBondData.*` tags. Its prose speaks of
  a translation-invariant positive two-site bond, which is exactly what the
  surviving tags state, so `\leanok` on both the statement and the proof
  remains correct.
* `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`: the three `\leanid`
  citations in the paragraph on the cyclic three-site coordinate identification
  now name the `TranslationInvariantBondData` forms. The eta-local bond is by
  definition the bond of its underlying translation-invariant data, so the
  surrounding sentences remain true verbatim; this is the same justification the
  2026-08-26 note gives for the migration it performed two paragraphs below. The
  `\doclink{TNLean/MPS/MPDO/CommutingOverlappingCoordinates}` footnote is
  unchanged: that file still supplies the coordinate and commutation
  hypotheses.
* The module docstring of
  `TNLean/MPS/MPDO/CommutingOverlappingCoordinates.lean` retargets its two
  reindex bullets to the `TranslationInvariantBondData` names and drops the
  eta-local commutation bullet, whose twin the list already carried.

## Retained on purpose

* `MPOTensor.EtaLocalStructureData.pairBond`
  (`TNLean/MPS/MPDO/CommutingOverlappingCoordinates.lean`) is retained: it is
  consumed at `TNLean/MPS/MPDO/CommutingBondEtaDecomposition.lean:340`, and its
  `\lean{}` tag on `def:mpdo_three_site_overlapping_coordinates` is untouched.
* `MPOTensor.EtaLocalStructureData.exists_positive_eta_pairBond_decomposition`
  (`TNLean/MPS/MPDO/CommutingBondEtaDecomposition.lean`) is retained, with the
  live consumers already recorded by the 2026-08-26 note.
* `private theorem two_le_three`
  (`TNLean/MPS/MPDO/CommutingOverlappingCoordinates.lean`) is retained: the
  surviving `TranslationInvariantBondData` theorems still use it.
