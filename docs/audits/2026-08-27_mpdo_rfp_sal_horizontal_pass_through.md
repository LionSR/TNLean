# MPDO renormalization fixed-point horizontal pass-through retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The removed declaration was a two-line
composition of two theorems that both survive; it had no Lean consumer and no
blueprint `\lean{}` tag.

| Removed | Replacement |
|---|---|
| `MPOTensor.isSourceZCL_and_isSAL_of_isRFPViaTS` (`TNLean/MPS/MPDO/RFPViaTSSAL.lean`) | `MPOTensor.isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero` (same file), applied to the nonvanishing positive-length traces supplied by `MPOTensor.trace_mpo_ne_zero_of_isHorizontalCF_isMPDO_isRFPViaTS` |

The removed theorem's whole body was that composition, so any future caller
reconstructs it in two lines at the use site.

## What was checked

The only references to the removed name outside its own declaration were prose
in `docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`, migrated in the same
change: the horizontal-specialization section now states the broader
scale-invariant conclusion as a consequence of the surviving
trace-nonvanishing theorem rather than naming a convenience wrapper. No
`\lean{}` tag in `blueprint/src` names the removed declaration, so
`leanblueprint checkdecls` is unaffected.

Four neighbours are retained deliberately and are untouched:
`isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero`, `isSAL_of_isRFPViaTS`,
`isSourceZCL_of_isRFPViaTS`, and
`trace_mpo_ne_zero_of_isHorizontalCF_isMPDO_isRFPViaTS`. Each is either
blueprint-tagged or covered by the retention decision recorded in
`docs/audits/2026-05-08-mps-ft-paper-coverage.md`.

The retained parent conjunction
`isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero` is now zero-reference in
Lean by design. That is not a build condition: an unreferenced theorem is not a
build error, and the repository has no unused-declaration linter for theorems.
It remains reachable through its paper-gap citation.

## Net effect

`TNLean/MPS/MPDO/RFPViaTSSAL.lean` goes from 504 to 480 lines.
