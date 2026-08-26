# MPDO cyclic-sector and BNT retirements (2026-08-26)

This note records four deletions in `TNLean/MPS/MPDO`, taken under the
pass-through exception of `docs/project_conventions.md` §Style: every removal
below has zero non-`Archive` Lean consumers, and each blueprint `\lean{...}`
tag that named a removed declaration is redirected in the same change.

## Declaration-free import facades

Four modules carried no declarations at all; each only re-exported another
module's imports.

| Removed module | Replacement import |
|---|---|
| `TNLean.MPS.MPDO.CyclicActiveMarkov` | `TNLean.MPS.MPDO.CyclicActiveMarkovDecomposition` |
| `TNLean.MPS.MPDO.CyclicActiveMarkovNormalization` | `QICLean.Algebra.PositiveSemidefiniteNormalization` together with `TNLean.MPS.MPDO.CyclicActiveFourthRegionFormula` |
| `TNLean.MPS.MPDO.CyclicActiveFourthRegion` | `TNLean.MPS.MPDO.CyclicActiveFourthRegionFormula` |
| `TNLean.MPS.MPDO.BNTAlgebraTensorClauseAmbientSectorMaps` | `TNLean.MPS.MPDO.BNTAlgebraTensorClauseAmbientSectorCoordinates`, `...OneSiteAmbientSectorMaps`, `...TwoSiteAmbientSectorMaps` |

The two in-library importers were migrated to the underlying modules:
`CyclicActiveCutCoordinates.lean` now imports `CyclicActiveFourthRegionFormula`,
and `BNTAlgebraTensorClauseConditionalPhysicalMaps.lean` now imports the three
ambient-sector modules directly. The remaining importer of each facade was the
generated aggregator `TNLean/MPS/MPDO.lean`, which was regenerated.

## A local lemma the library already provides

`MPOTensor.PhysicalSectorFactorization.dependent_apply_heq` (private, in
`CyclicActiveCutRegrouping.lean`) restated Mathlib's `congr_arg_heq` for a
dependent family. All 24 call sites now use `congr_arg_heq` with the same
positional arguments.

## Zero-reference cut-coordinate lemmas

Three lemmas in `CyclicActiveCutCoordinates.lean` had no consumer anywhere in
the production corpus and no blueprint tag:

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.PhysicalSectorFactorization.cyclicActiveSeparatedBoundary_eq_right_kronecker_left` | none needed; the equation is definitional (`rfl`) and is used inline where required |
| `MPOTensor.PhysicalSectorFactorization.leftSectorOpenEdgeEquiv_symm_fiber_heq` | `MPOTensor.PhysicalSectorFactorization.leftSectorOpenEdgeEquiv_symm_last_eq` |
| `MPOTensor.PhysicalSectorFactorization.rightSectorOpenEdgeEquiv_symm_fiber_heq` | `MPOTensor.PhysicalSectorFactorization.rightSectorOpenEdgeEquiv_symm_first_eq` |

The retained `@[simp]` lemma `rightSectorOpenEdgeEquiv_apply_fst` and the two
`symm_last_eq` / `symm_first_eq` lemmas cover every live use of the inverse
open-edge identifications.

## The common-copy-weight specialization of Proposition `prop3to4`

`MPOTensor.hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization_of_commonWeight`
was removed from `BNTPhysicalSectorGSNNCH.lean`; its replacement is
`MPOTensor.hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization`
in the same file. The removal is justified by the absence of consumers, **not**
by subsumption: the survivor drops the common-weight hypothesis but adds
`IsMPDO M` and positivity of every basis dimension, so the two statements are
incomparable. No downstream result loses a proved fact, since nothing cited the
removed one.

The three common-weight helpers
`exists_pairwise_orthogonal_twoSided_physicalSupport_commonWeightAbsorbedBasis`,
`hasGSNNCHForm_of_commonWeightAbsorbedBasisMPOTensor`, and
`commonWeightAbsorbedBasisMPOTensor_isInjective` are retained: each has a live
consumer and a blueprint tag. The now-unused import of
`TNLean.MPS.MPDO.CommonWeightAbsorbedBNTSupport` was dropped from
`BNTPhysicalSectorGSNNCH.lean`.

## The deprecated witness-repackaging module

`TNLean/MPS/MPDO/BNTTheoremWitnessConsequences.lean` (238 lines, eight
declarations, all deprecated on 2026-08-15) had zero Lean consumers.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_predicates` | `MPOTensor.BNTLabelTheoremWitness.same_length_product_form`, `.idempotent_coefficient_form`, `.positive_chi_trace_power`, `.positive_chi_pos_entries` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_positive_length_coeff_eq_ofChi` | `MPOTensor.BNTLabelTheoremWitness.coeff_eq_ofChi_coeff` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_ofChi_predicates` | `MPOTensor.BNTLabelTheoremWitness.same_length_product_form_ofChi`, `.idempotent_coefficient_form_ofChi` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_ofChi_equations` | `MPOTensor.BNTLabelTheoremWitness.same_length_product_eq_sum_ofChi`, `.idempotent_eq_sum_ofChi` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_blocked_chi_pullback` | `MPOTensor.BNTLabelTheoremWitness.positiveBlockedChi_toDiagonal_of_pos` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_blocked_coefficient_comparison` | `MPOTensor.BNTLabelTheoremWitness.blocked_coeff_eq` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_blocked_coefficient_comparison_ofChi` | `MPOTensor.BNTLabelTheoremWitness.blocked_coeff_eq_ofChi` |
| `MPOTensor.HasBNTLabelTheoremWitness.exists_source_coefficient_equations` | `MPOTensor.BNTLabelTheoremWitness.same_length_product_eq_sum`, `.idempotent_eq_sum` |

Two blueprint entries in `blueprint/src/chapter/ch21_mpdo_rfp_bnt_witnesses.tex`
were redirected:

- `thm:mpdo_has_bnt_label_theorem_witness_source_equations` lost seven tags and
  gained `MPOTensor.BNTLabelTheoremWitness.blocked_coeff_eq` and
  `.blocked_coeff_eq_ofChi`, so its final blocked-basis display keeps a Lean
  anchor. The surviving
  `MPOTensor.HasBNTLabelTheoremWitness.exists_source_chi_trace_equations` tag is
  untouched; that theorem lives in `BNTTheoremWitness.lean`.
- `thm:mpdo_bnt_label_theorem_witness_to_positive_blocked_chi_trace_power_form`
  lost the `exists_blocked_chi_pullback` tag; its replacement
  `positiveBlockedChi_toDiagonal_of_pos` was already tagged in the same entry.

No prose and no `\uses` were changed.

This supersedes the retention decision recorded at
`docs/audits/2026-08-15_mpdo_dead_proof_cleanup.md` lines 35--40 and 49, which
kept the eight packaging theorems and the module import path behind dated
deprecations. The deprecation cycle produced no consumer, and the same note
records the #6504 / #6544 precedent for removing a deprecation one day after it
is introduced.
