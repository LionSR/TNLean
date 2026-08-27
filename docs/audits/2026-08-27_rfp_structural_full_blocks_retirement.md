# RFP structural-form per-block restatement retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The three declarations below were
pointwise restatements: each took a family of blocks and returned its
single-tensor original applied to one block, with a proof body of the form
`fun k => <original> (A k) (hNT k) (hRFP k) (hLeft k)`.

| Removed | Replacement |
|---|---|
| `MPSTensor.isIsometryCanonicalForm_of_rfp_nt_blocks` (`TNLean/MPS/RFP/StructuralFull.lean`) | `MPSTensor.isIsometryCanonicalForm_of_rfp_nt` (same file), applied at each block |
| `MPSTensor.rfp_nt_structural_full_blocks` (`TNLean/MPS/RFP/StructuralFull.lean`) | `MPSTensor.rfp_nt_structural_full` (same file), applied at each block |
| `MPSTensor.rfp_nt_structural_full_blocks_unit_pair` (`TNLean/MPS/RFP/StructuralFull.lean`) | `MPSTensor.rfp_nt_structural_full_unit_pair` (same file), applied at each block |

## What was checked

None of the three had a non-`Archive` Lean consumer. The only in-file reference
to a removed name lived inside a docstring that was deleted with it.

The two cross-block scope-restriction markers that survive in the module keep it
compliant with the one-marker-per-(restriction, module) rule: each removed
docstring restated the same cross-block orthogonality restriction that those
markers already record.

After this deletion `MPSTensor.rfp_nt_structural_full` has no Lean consumer of
its own. It is retained deliberately: it is the tagged, `\leanok` formalization
of the Appendix B structural lemma and is cited by the isometry-scope paper-gap
note, which makes it a substantive public result rather than a pass-through. No
further dead-weight cascade follows.

Three call sites in `TNLean/MPS/RFP/ResidualIsometry.lean` inline the per-block
shape by hand. Migrating them to the removed wrappers instead of deleting the
wrappers was considered and rejected: each site is a two-line function that
supplies its own fixed-point hypothesis from the direct-sum block projection, so
a wrapper would save no lines.

## Blueprint

All three numbered entries were deleted rather than redirected. Their `\uses`
and `\ref` edges pointed only at each other or at the surviving single-tensor
theorems, and every reference to a deleted label was itself inside a deleted
region; a search confirms no remaining occurrence of any of the three labels
under `blueprint/src`.

The surviving carriers, all already `\leanok`, are the single-tensor entries in
`blueprint/src/chapter/ch26_mps_rfp_normal_isometry_canonical_forms.tex`:
`thm:isometry_canonical_form_of_rfp_nt`, `thm:rfp_nt_structural_full`, and
`thm:rfp_nt_structural_full_unit_pair`.

One sentence following the multiplicity-routing figure referred to "the
per-block theorem above" and was reworded to name the single-block square-root
form that applies at each block.

## Paper-gap note

`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` cited two of the removed names
in footnotes. Both citations were retargeted to the surviving single-tensor
declarations. The mathematics of the note is unchanged: its per-block equations
and their labels are cross-referenced later in the note, and the gap it records
— the missing trace normalization and the missing cross-block orthogonality
between distinct blocks — is a multi-block statement that still stands.
