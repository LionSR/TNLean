# MPDO orthogonal-sector zero-correlation-length area-law twin deletion

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The removed theorem was the
all-scalars-equal-one instance of a general theorem in the same file: its whole
body applied the general theorem with the proportionality scalars set to one.

| Removed | Replacement |
|---|---|
| `MPOTensor.isSAL_of_orthogonalCommutingSectorFamily_of_sectorwise_isSourceZCL` (`TNLean/MPS/MPDO/OrthogonalSectorAreaLaw.lean`) | `MPOTensor.isSAL_of_proportionalOrthogonalCommutingSectorFamily_of_sectorwise_isSourceZCL` (same file), at $a_{x,N}=c_N=1$ via `OrthogonalCommutingSectorFamily.toProportional` |

## Blueprint

The blueprint node `thm:mpdo_orthogonal_commuting_sector_zcl_sal`
(`blueprint/src/chapter/ch21_mpdo_rfp_gsnnch_definitions.tex`) had the removed
declaration as its sole `\lean{}` tag and its whole proof was "take the scalars
equal to one" in the general theorem. The node is deleted rather than
redirected, because `thm:mpdo_proportional_orthogonal_commuting_sector_zcl_sal`
already carries the general statement of which this was an instance — exactly
the arrangement `cor:mpdo_orthogonal_commuting_sector_sum_sal` already records
for the non-zero-correlation-length half. Nothing `\ref`s or `\uses` the
deleted label, so no edge is redirected and no `\leanok` changes.

## What was checked

The removed declaration had no Lean consumer. Its two neighbours in the same
file are untouched and still live: `OrthogonalCommutingSectorFamily.toProportional`
and `MPOTensor.isSAL_of_orthogonalCommutingSectorFamily`. The CPSV16
`prop4to2` coverage rows in `docs/audits/2026-05-08-mps-ft-paper-coverage.md`
and the discussion in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` were
checked: both cite only surviving declaration names, so neither needed an edit.
The scope-restriction discussion that the removed docstring and the deleted
blueprint comment block carried is preserved in full in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` and in the surviving general
theorem's own restriction marker.

## Net effect

39 Lean lines and 39 blueprint lines removed.
