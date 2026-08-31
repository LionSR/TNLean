# MPDO/RFP simplification follow-up

This audit applies `.claude/skills/find-simplification/SKILL.md` to the 365 Lean
files under `TNLean/MPS/MPDO/` and the 46 Lean files under `TNLean/MPS/RFP/`.
The survey started at `27b321fff450db6341cdcfb135ab1d89ee6a2ba5`; the
validated batch is rebased onto `3abe545abb173a4df58370f216d37ec8f82f6753`.
It follows the August 27 MPDO/RFP campaign and the August 30 word-evaluation cleanup. Issue #7553 tracks the
bounded deletion batch under proof-debt tracker #4529. The source paper,
Blueprint statements, and paper-gap classifications are unchanged.

## Validated removals

The deletion test removes the following declarations. Exact-name and
receiver-style searches found no remaining non-`Archive` Lean consumer, direct
Blueprint tag, or surviving documentation reference unless a consumer is named
below.

| Removed declaration | Survivor or replacement | Net reduction |
|---|---|---:|
| `MPOTensor.EtaLocalStructureData.formAt_bond` | The projection reduces by `rfl` from `EtaLocalStructureData.formAt`. | 3 lines |
| `MPOTensor.PhysicalSupportRestrictionData.liftedTranslationInvariantBondData_bond` | The projection reduces by `rfl` from `liftedTranslationInvariantBondData`. | 7 lines |
| `MPOTensor.PhysicalSupportRestrictionData.liftedEtaLocalStructureData_bond` | The projection reduces by `rfl` from `liftedEtaLocalStructureData`. | 8 lines |
| `MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause_labelCount` | The field reduces definitionally from `R_oneLabelBNTAlgebraTensorClause`. | 3 lines |
| `MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause_tensor` | The field reduces definitionally from `R_oneLabelBNTAlgebraTensorClause`. | 3 lines |
| `MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause_weight` | The field reduces definitionally from `R_oneLabelBNTAlgebraTensorClause`. | 3 lines |
| `MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause_coeffs` | The field reduces definitionally from `R_oneLabelBNTAlgebraTensorClause`. | 3 lines |
| `MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause_chi` | The field reduces definitionally from `R_oneLabelBNTAlgebraTensorClause`. | 3 lines |
| `MPSTensor.AppendixBStructuralData.hasOverlappingTwoSiteCommutation_of_support_commute` | Its sole consumer, `AppendixBStructuralData.hasOverlappingTwoSiteCommutation`, now performs the complement construction directly. | 18 net lines |

The one-label parent construction remains Blueprint-tagged and is consumed by
`RescalingStableLengthDependentRFPCapstone.lean`. That capstone already closes
its coefficient-family obligation by definitional equality and does not name
any removed projection theorem. The Appendix B capstone and its supporting
commutator remain Blueprint-tagged and unchanged in statement.

## Private duplicate

`TNLean/MPS/MPDO/KatoDeformedRFPObstruction.lean` defined both
`block0Weight` and `blockLetterAmplitude` as the same complex number,
`1 / Real.sqrt 2`, and proved the same square calculation twice. The deletion
test uses `blockLetterAmplitude` as the zero-block weight, removes
`block0Weight` and `block0Weight_times_amplitude`, and reuses
`blockLetterAmplitude_sq` at the two local simplification sites. Both removed
names were private. The change is a net reduction of 11 lines.

## Import edges

Three direct imports elaborate redundantly against the present dependency
graph and are removed:

- `Mathlib.LinearAlgebra.Dimension.Constructions` from
  `TNLean/MPS/RFP/BeigiGroundSpaceDimension.lean`;
- `QICLean.Algebra.MatrixIsometryEntries` from
  `TNLean/MPS/RFP/BeigiLoopInjectivity.lean`;
- `QICLean.Algebra.MatrixIsometryEntries` from `TNLean/MPS/RFP/Defs.lean`.

These removals change no declaration or Blueprint reference. Their net
reduction is 3 lines.

The complete proposed source change is 80 deleted and 11 added lines, for a net
reduction of 69 lines.

## Retained declarations

The same root-build deletion test covered two additional zero-name-reference
`@[simp]` lemmas, but this audit retains them:

- `MPOTensor.AlgebraStructureData.toBlockedCoefficients_reconstructFromBlockedCoefficients`
  is one direction of the natural equivalence API, paired with
  `reconstructFromBlockedCoefficients_toBlockedCoefficients`. Its independent
  statement is useful even without a current repository consumer.
- `MPOTensor.CommutingFormData.bondAt_apply` is the public evaluation theorem
  for a translated bond. It exposes the defining window condition rather than
  merely projecting a constructor field.

The following settled surfaces are also retained:

- source-facing or Blueprint-tagged RFP theorems, including
  `rfp_nt_structural_of_leftCanonical`, `rfp_nt_structural_full`, and the
  printed BNT spectral-pair obstruction;
- unexpired deprecations, including `blockTransferSum_blockTransferSum`;
- the Appendix B coordinate simp lemmas used by bare `simp` in finite-coordinate
  proofs;
- QICLean-owned channel and matrix APIs;
- all material associated with issue #7371, whose remaining PEPS-to-RFP claim
  lacks source specifications rather than library infrastructure.

## Verification

The candidate names were checked against non-`Archive` Lean sources, the
multiline-aware Blueprint declaration parser, reader-facing documentation,
Git history, and open and closed cleanup issues. The deletion batch passes the
changed-module builds and a root `lake build` with 10,437 jobs. Thus the root
importers were elaborated after all attribute-carrying declarations were
removed. The audit does not alter any source-facing statement or close any
paper-level question.
