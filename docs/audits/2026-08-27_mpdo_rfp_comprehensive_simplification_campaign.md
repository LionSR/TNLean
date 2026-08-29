# MPDO/RFP comprehensive simplification campaign

This record consolidates the simplification audits
`cf1c159b8a93`, `0ad2465bed99`, `449befb1e41d`, `658af4725c37`,
`4118d48ca65f`, `11d08c658d7d`, `2d2b429b67ed`, `dba1c7a6d609`,
`2353d76d852b`, `750620442e96`, `3e933403f2cd`, `cd9da3a49a47`,
`04a75a71f574`, `7ebd6dd28704`, and `5d485d471b07`, implementation
workflow `0e5f8a34ac8c9c1fc5e40dbd`, and integration validation
`4171579956d5`.

## Scope and census

The campaign covers the MPDO/RFP development sourced from
`Papers/1606.00608/MPDO-22-12-17-2.tex`, Blueprint Chapters 20, 21,
and 26, and the normal-tensor, canonical-form, BNT, and Wielandt
prerequisites used by those chapters. The source paper itself is unchanged.
Excluding this record, the integrated tracked diff contains 29 files:
20 Lean sources, four Blueprint chapter sources, and five audit, glossary, or
paper-gap documents. It has 118 added and 398 deleted lines, for a net reduction
of 280 lines. The Lean part removes or stops storing 33 named declarations,
private helpers, or structure fields while preserving the substantive tagged
results.

Consumer counts below treat `TNLean/`, `blueprint/src/`, and reader-facing
`docs/` as real consumers. `blueprint/lean_decls` and `blueprint/web/` are
build products, not consumers: the former still contains one stale campaign
name and the latter contains three rendered copies of that same old tag. They
were deliberately not regenerated or edited in this campaign.

## BNT and canonical-form layer

In `TNLean/MPS/BNT/Construction.lean`, the following unused projections and
intermediate construction rungs are removed:

- `MPSTensor.IsNormalCanonicalFormBNT.toHasIrreducibleBlocks`;
- `MPSTensor.IsNormalCanonicalFormBNT.toIsLeftCanonicalBlockFamily`;
- `MPSTensor.IsNormalCanonicalFormBNT.toHasPrimitiveBlocks`;
- `MPSTensor.IsNormalCanonicalFormBNT.toHasNormalizedSelfOverlap`;
- `MPSTensor.spans_mpv_and_eventually_li_of_separated_normal_bnt_data`;
- `MPSTensor.isBNT_of_separated_normal_bnt_data`.

The tagged theorem `MPSTensor.IsNormalCanonicalFormBNT.isBNT` now constructs
its `IsBNT` witness directly from `spans_mpv_toTensorFromBlocks`, overlap
limits, and the surviving canonical-form projections. In
`TNLean/MPS/CanonicalForm/Definitions.lean`, the two unused pass-throughs
`MPSTensor.CPSVCanonicalFormIIData.isCPSVCanonicalForm` and
`MPSTensor.IsCPSVCanonicalFormII.isCPSVCanonicalForm` are removed. The glossary
now names the surviving bridges `toIsNormalCanonicalForm`, `ofSeparatedData`,
and `isBNT`, rather than the deleted projections.

## MPDO and RFP leaves

The following zero-consumer or strictly weaker public leaves are removed:

- `MPOTensor.DiagonalChiFamily.PosEntries.comap` from
  `TNLean/MPS/MPDO/AlgebraStructure.lean`; its live caller
  `pulledBlockedChiFamily_toDiagonal_posEntries` in
  `TNLean/MPS/MPDO/BNTCoefficients.lean` proves the indexed positivity directly;
- `MPSTensor.IsResidualIsometryFamily.wordTupleSpanTop_one` from
  `TNLean/MPS/RFP/ResidualWordSpan.lean`; the sole proof now calls
  `wordTupleSpanTop_of_wordEntryFamily_linearIndependent` directly;
- the theorem `entry_eq_zero_or_eq_one_of_lengthIndependent` in the namespace
  `MPOTensor.BNTLabelCoefficientFamily.HasPositiveLengthChiTracePowerForm`, from
  `TNLean/MPS/MPDO/LengthIndependentCoefficients.lean`, strictly subsumed by
  `entry_eq_one_of_lengthIndependent`;
- `traceMatrix_row_sum`, `traceMatrix_rank_ge_two_minor`,
  `left_factor_injective`, and `right_factor_injective` from
  `TNLean/MPS/MPDO/NonCartesianActiveSectorCandidate.lean`, and
  `sectorCount_eq_four` from
  `TNLean/MPS/MPDO/NonCartesianActiveSectorObstruction.lean`, all in the
  `MPOTensor.NonCartesianActiveSectorCandidate` namespace.

`TNLean/MPS/MPDO/BiCFDerivation/Selectors.lean` also replaces the broad
`PairHomogenization` import by the direct `Core` owner. No biCF statement is
changed.

## Private Mathlib and QICLean shadows

`TNLean/MPS/MPDO/OperatorProduct.lean` generalizes
`MPOTensor.listProd_conj_of_conjTranspose_mul_self` from a `Fin` column index
to an arbitrary finite decidable type. The private cloned induction theorem of
the same mathematical content in
`TNLean/MPS/MPDO/BNTFusionCoisometries.lean` is removed, and its consumer uses
the generalized owner.

`TNLean/MPS/RFP/BellPairCIDObstruction.lean` removes the private matrix
`pauliZ` and its private square and trace lemmas. The proofs use
`SpinCover.pauli 2`, `SpinCover.pauli_mul_eq`, and `SpinCover.trace_pauli` from
QICLean. `TNLean/MPS/MPDO/CPSVExample410Spectrum.lean` retains the private
`single_mul_single_eq_if` and `trace_single_eq_if` lemmas as readable local
interfaces, proved from `Matrix.single_mul_single_same`,
`Matrix.single_mul_single_of_ne`, `Matrix.trace_single_eq_same`, and
`Matrix.trace_single_eq_of_ne`. It removes only the private `trace_zero` shadow
and uses `Matrix.trace_zero` directly.

`TNLean/MPS/MPDO/CyclicActiveFourthRegionContraction.lean` removes the private
index restatement `fourthRegion_retained_internal_index`, which is subsumed by
`Fin.succAbove_last_apply`; the two call sites prove the required equality
directly by extensionality and simplification. It also removes the three private
equality wrappers
`partialTraceRight_neighboringOperator_eq_of_right`,
`partialTraceLeft_neighboringOperator_eq_of_left`, and
`neighboringOperator_trace_eq_of_eq`. Their intended replacements are direct
dependent congruence and simplification at the call sites.

The QICLean boundary tracked by #7096 is outside this batch. The private
positive-definite trace-pairing theorem in the pinned QICLean dependency is not
made public here, and the three TNLean derivations awaiting that promotion are
not changed.

## Physical and vertical carriers

In `TNLean/MPS/MPDO/PhysicalSectorActiveCoordinates.lean`, the one-use theorem
`dependentSupportInclusion_range_eq_dependentPhysicalSupportProj` in the
`MPOTensor.PhysicalSectorFactorization` namespace is removed;
`PhysicalSectorActiveRestriction.lean` calls the underlying
`dependentSupportInclusion_range` theorem directly. The structure
`MPOTensor.PhysicalSectorFactorization.SectorActiveFactorSupportData` retains
both inactive-sector dimension invariants, including
`rightDim_eq_zero_of_not_isActiveSector`, and both constructor branches supply
them. Thus its contract continues to force both coordinate dimensions to vanish
in an inactive sector, alongside the retained active-sector positivity data.

In `TNLean/MPS/MPDO/VerticalProductSpectralFamily.lean`, the unprojected fields
`MPOTensor.RetainedProductSpectralFamily.local_compression`,
`local_sameMPV₂Pos`, and `local_dimension_bound` are removed. The existence
proof still obtains the stronger supplier outputs but discards these three
unused components; the retained intertwining and reconstruction fields, and
all flattened consequences consumed later, remain unchanged.

## Wielandt prerequisites

`TNLean/Wielandt/Primitivity/Equivalence.lean` removes the four descriptive
forwarders `MPSTensor.prop3_ba`, `MPSTensor.prop3_ac`, `MPSTensor.prop3_cb`, and
`MPSTensor.prop3_qIndex_le_iIndex`. Combined equivalence theorems now call the
owned implications
`isPrimitivePaper_of_hasEventuallyFullKrausRank`,
`isStronglyIrreduciblePaper_of_isPrimitivePaper`,
`hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper`, and
`qIndex_le_iIndex` directly. `TNLean/Wielandt/Inequality/Bounds.lean` is migrated
to the last owner. The normal-tensor basis retains the same mathematical
primitivity equivalences and quantitative bound.

## Consumers and Blueprint evidence

A repository search over real source consumers finds zero occurrences of every
removed public qualified name listed above. Private removals cannot have
out-of-file Lean consumers. The only campaign removal that had a direct
Blueprint tag was the weaker zero-or-one coefficient theorem; that tag is
removed from `ch21_mpdo_rfp_bnt_coefficients.tex`, while the stronger theorem
and all other declarations supporting the entry remain tagged and formalized.

The direct Blueprint scan finds 6,637 unique `\lean{}` references and 6,657
formalized theorem-like entries, with no reference lacking a matching Lean
source declaration. In particular, all direct Blueprint Lean references are
resolved after the source and tag migrations. The separate generated
`blueprint/lean_decls` census is globally out of date: the current verified
`blueprint_lean_sync.py --ci` log reports 310 stale entries and 1,149 direct
references absent from that generated file, for 1,459 metadata-sync issues.
This is pre-existing repository-wide baseline drift rather than a real
consumer or a campaign-specific unresolved Lean name; this campaign does not
regenerate `blueprint/lean_decls` or `blueprint/web/`.

## Blueprint and paper-gap corrections

The same integrated diff makes only the following source-facing corrections:

- `def:sector_bnt_cf` records dependencies on the abstract and literal BNT
  definitions as well as the sector-weight data;
- the fusion definition is described as a full-support labelled fusion family;
  BNT structure is supplied only in later tensor-attached applications, not
  added as an unstated hypothesis;
- the physical-support projection in the isometric-embedding theorem is written
  consistently as `\Pi_{\mathcal K}` rather than `P_{\mathcal K}`;
- malformed `SameMPV₂Pos` declaration names are corrected in the SAL/ZCL,
  Figure 11, and projector-closure paper-gap notes;
- the historical wave-two audit names the surviving `mixedMapLM` theorem, and
  the glossary gives the precise vertical-canonical-form source ranges.

These edits do not strengthen the mathematical claims or mark a source gap as
closed.

## Source faithfulness and governance exclusions

No unexpired deprecated declaration is removed or shortened. The campaign is
limited to private shadows, direct pass-throughs whose consumers are migrated,
unused structure fields, and zero-consumer or strictly weaker leaves. It does
not change the statement of a source-facing theorem, the source paper, or the
status of the following active boundaries:

- #6775 is resolved separately by the ambient biCF counterexample, which
  refutes the absorbed-representative neighboring-trace assertion in
  Theorem 4.9;
- #7088 supplies the project-derived embedded rank-one neighboring-trace
  obstruction and terminal unit-weight BNT blocks used by that counterexample;
  this campaign makes no claim that CPSV16 contains that construction;
- #7142 remains the unresolved choice of a purification-RFP predicate carrying
  the source's standing presentation; the existing counterexamples and printed
  status are untouched;
- #7096 remains the QICLean ownership task for the positive-definite
  trace-pairing lemma described above.

## Validation

All 20 modified Lean modules pass targeted cached `lake build` checks, with zero
warnings. No changed Lean file contains `sorry` or `axiom`, and no build target
remains blocked. In particular, the dependent-index substitutions and final
simplification in `CyclicActiveFourthRegionContraction.lean` were repaired, and
both modified four-letter obstruction modules compile against the result.

`git diff --check`, the HEAD-relative reader-facing prose check, and the CPSV16
source-label disposition audit pass. All three changed standalone paper-gap
notes compile with the repository-local `docs/paper-gaps/command.tex` preamble.
The Blueprint source scan resolves all direct `\lean{}` references. The stricter
`leanblueprint checkdecls` command remains blocked by a pre-existing generated
`blueprint/lean_decls` environment collision between
`QICLean.Algebra.PerronFrobenius.RankOne` and
`TNLean.Algebra.MatrixCyclicTracePower`; the separate generated-file baseline
drift is recorded above. Final CI and pull-request status are not claimed here.
