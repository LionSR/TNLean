# RFP zero-correlation-length spectral-pair ladder retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The four declarations below formed a
hypothesis ladder: each carried, as an explicit premise, the normalized nonzero
subleading eigenpair that the source asserts without proof, and each was
superseded once the eigenvalue-free trace-pairing repair gave the same
conclusions with no spectral premise at all.

| Removed | Replacement |
|---|---|
| `MPSTensor.IsBNTCanonicalForm.isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL_of_spectral_pair` (`TNLean/MPS/RFP/ZCLReverse.lean`) | `MPSTensor.IsBNTCanonicalForm.isTransferIdempotent_basisDirectSum_of_isPositiveGapBNTZCL` (same file) |
| `MPSTensor.IsBNTCanonicalForm.isPositiveGapBNTZCL_basisDirectSum_iff_isTransferIdempotent_of_spectral_pair` (`TNLean/MPS/RFP/ZCLReverse.lean`) | `MPSTensor.IsBNTCanonicalForm.isPositiveGapBNTZCL_basisDirectSum_iff_isTransferIdempotent` (same file) |
| `MPSTensor.IsBNTCanonicalForm.isTransferIdempotent_basisDirectSum_of_isPhysicalBNTZCL_of_spectral_pair` (`TNLean/MPS/RFP/ZCLReverse.lean`) | `MPSTensor.IsBNTCanonicalForm.isTransferIdempotent_basisDirectSum_of_isPhysicalBNTZCL` (same file) |
| `MPSTensor.IsBNTCanonicalForm.isPositiveGapBNTZCL_implies_hasNNCPHGroundSpaces_basisDirectSum_of_spectral_pair` (`TNLean/MPS/RFP/MainMPSConditional.lean`) | `MPSTensor.IsBNTCanonicalForm.isPositiveGapBNTZCL_implies_hasNNCPHGroundSpaces_basisDirectSum` (same file) |

Each replacement proves the same conclusion from the same data minus the
spectral premise, so every consumer of a removed name can use the replacement
unchanged, discarding the spectral argument it used to supply.

## What was checked

The only Lean references to the removed names were inside the ladder itself:
the equivalence and the physical-premise variant called the positive-gap
variant, and the ground-space implication called it through the fixed-point
theorem. No consumer outside the four declarations existed.

The contradiction theorem
`not_isPositiveGapPhysicalCID_basisDirectSum_of_basis_spectral_pair` is retained
on purpose and now has no Lean reference. It remains live through its `\lean{}`
tag on the subleading-pair blueprint entry and through its entry in
`docs/tactic_patterns.md`: it is the formal record of the source's printed
spectral step, taking the normalized nonzero subleading pair as an explicit
hypothesis rather than deriving it from non-idempotence. That blueprint entry is
consequently an isolated node with no inbound `\uses`, which is intended.

`TNLean/MPS/RFP/MainMPSConditional.lean` keeps its name even though it no longer
holds a conditional theorem. Renaming it would churn the generated aggregators
without reducing surface.

## Blueprint

Three numbered entries were deleted rather than redirected; all references to
their labels were inside the deleted block. Their surviving twins, all already
`\leanok`, are in
`blueprint/src/chapter/ch26_mps_rfp_zero_correlation_length.tex`:

| Deleted label | Surviving carrier |
|---|---|
| `thm:positive_gap_bnt_zcl_conditional_converse` | `thm:positive_gap_bnt_zcl_unconditional_converse` and `thm:positive_gap_bnt_zcl_multiplicity_one_iff_rfp` |
| `thm:positive_gap_bnt_zcl_conditional_nncph` | `thm:positive_gap_bnt_zcl_unconditional_nncph` |
| `thm:physical_bnt_zcl_conditional_converse` | `thm:physical_bnt_zcl_multiplicity_one_implies_rfp` |

The subleading-pair entry `thm:zcl_subleading_pair_excludes_cid` keeps its
`\lean{}` tag and its `\leanok`. The closing sentence of the remark on remaining
obstructions in the printed converse, which pointed at "the conditional theorems
above", now names that entry as the formal record of the printed spectral
argument.

## Paper-gap note

`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex` described the
retired declarations by their shared name suffix. That sentence now states, in
mathematical terms, that the formalized contradiction argument takes the nonzero
subleading left and right eigenvectors of the cited source lines as an explicit
hypothesis rather than deriving them from non-idempotence. The gap the note
records is unchanged.
