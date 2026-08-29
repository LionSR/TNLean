# MPDO simplicity: unit-weight and nonvanishing variants retired

This audit records the two degenerate readings of arXiv:1606.00608
Definition 4.7 that were retired, the declarations the retirement made
redundant, and the rename of the surviving predicate. It is the audit note
required by `docs/project_conventions.md` §Style for removals under the
pass-through exception, extended to the mathematical-language rename of
`docs/CONTRIBUTING.md` §Mathematical-language renames. No compatibility alias
is provided for any renamed or removed declaration.

It continues the pass begun in
`docs/audits/2026-08-23_nonzero_coefficient_convention.md`, which the
statements below supersede wherever the two disagree.

## Readings retired

**(i) The line-246 unit-weight witness is not a clause of Definition 4.7.**
The source blocks a positive number of physical sites (line 815), writes the
blocked doubled-index tensor over a basis of normal tensors, and calls the
tensor simple when no basis element has nilpotent ket-against-bra contraction
(lines 819–822). Line 246 is a separate normalization the authors may apply to
a canonical form: "we can always choose $|\mu_k| \le 1$ and at least one equal
to one." The formalization had read the two together, so that simplicity
required the blocked tensor itself to admit a canonical-form witness with a
unit-modulus copy weight.

That reading excludes the source's own examples. The dimer $R$ of
`RescalingStableLengthDependentRFP` has canonical-form weight
$\sqrt{337/512}$, has a non-nilpotent physical-trace transfer, and is simple
in the source's sense; the unit-weight reading would still exclude it, since
$\sqrt{337/512}$ is not a unit weight. (Example 4.12 is not a second such
witness: its second BNT basis element has vanishing one-by-one
physical-trace transfer, so it is not simple under any reading — see
`docs/paper-gaps/cpsv16_simple_tensor_nilpotency.tex`.) The tension between
the line-246 normalization and the scale that Definition 4.1 pins is real for
$R$, and it stays recorded in
`docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`; what it does not
do is refute simplicity of $R$.

**(ii) "The closed MPO is nonzero at every positive length" is not in the
source.** The formalization carried a strengthening of simplicity with that
extra clause. The source asks for nothing of the kind, and the clause is not
implied: it is separated from simplicity only by the one-letter tensor whose
sole virtual matrix is $\operatorname{diag}(1,-1)$, whose closed operator is
$(1+(-1)^N)I$ and therefore vanishes at odd lengths. That is exactly the
degenerate witness the convention rules out of scope. Positive-length
nontriviality — a nonzero closed MPO at *some* positive length — remains a
theorem of simplicity, `MPOTensor.IsSimple.exists_mpo_ne_zero`.

## The convention now in force

`MPOTensor.IsSimple` (in `TNLean/MPS/MPDO/SourceSimpleTensor.lean`) is the
only simplicity predicate: a tensor generating MPDOs is simple when, for some
positive blocking length, the blocked doubled-index tensor has a
basis-of-normal-tensors sector presentation whose representatives all have
non-nilpotent physical-trace transfer. Nonnilpotency is independent of the
chosen presentation (`MPOTensor.bnt_basis_not_isNilpotent_iff`), so the
existential quantifier over presentations is harmless.

`MPOTensor.IsSimpleCanonicalForm` is unaffected. It is not a simplicity
predicate but the Appendix C.2 hypothesis on an already-blocked tensor, and it
keeps its normalized canonical-form witness and its
`**Scope restriction (fixed representative)**` marker.

## Rename

`MPOTensor.IsSourceSimple` and its API are renamed to drop "source": the
qualifier existed only to distinguish the predicate from the unit-weight
variant, which no longer exists, and it wrongly suggested that the other
variant was equally source-faithful. Per
`docs/CONTRIBUTING.md` §Mathematical-language renames, no `@[deprecated]`
alias is provided.

| Old name | New name |
|---|---|
| `MPOTensor.IsSourceSimple` | `MPOTensor.IsSimple` |
| `MPOTensor.IsSourceSimple.exists_mpo_ne_zero` | `MPOTensor.IsSimple.exists_mpo_ne_zero` |
| `MPOTensor.IsSourceSimple.smul_ofReal` | `MPOTensor.IsSimple.smul_ofReal` |
| `MPOTensor.isSourceSimple_smul_ofReal_iff` | `MPOTensor.isSimple_smul_ofReal_iff` |
| `MPOTensor.RescalingStableLengthDependentRFP.R_isSourceSimple` | `MPOTensor.RescalingStableLengthDependentRFP.R_isSimple` |

The module file names `SourceSimpleTensor.lean`, `SourceSimpleScaling.lean`,
and `RescalingStableSourceSimple.lean` are unchanged in this pass.

## Removed declarations

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.IsSimple` (unit-weight reading, `SimpleTensor.lean`) | `MPOTensor.IsSimple` (Definition 4.7 reading, `SourceSimpleTensor.lean`). |
| `MPOTensor.IsSimple.isSourceSimple` | None; the two predicates it bridged are now one. |
| `MPOTensor.IsSimple.isNonvanishingSourceSimple` | None. |
| `MPOTensor.IsNonvanishingSourceSimple` | `MPOTensor.IsSimple`; the extra clause is not asserted by the source. |
| `MPOTensor.IsNonvanishingSourceSimple.isSourceSimple` | None. |
| `MPOTensor.IsNonvanishingSourceSimple.mpo_ne_zero` | None. |
| `MPOTensor.IsNonvanishingSourceSimple.smul_ofReal` | `MPOTensor.IsSimple.smul_ofReal`. |
| `MPOTensor.isNonvanishingSourceSimple_smul_ofReal_iff` | `MPOTensor.isSimple_smul_ofReal_iff`. |
| `MPOTensor.RescalingStableLengthDependentRFP.R_isNonvanishingSourceSimple` | `MPOTensor.RescalingStableLengthDependentRFP.R_isSimple`. |
| `MPOTensor.RescalingStableLengthDependentRFP.R_not_isSimple` | None; the dimer is simple. |
| `MPOTensor.RescalingStableLengthDependentRFP.R_isSourceSimple_and_not_isSimple` (deprecated) | None. |
| `MPOTensor.RescalingStableLengthDependentRFP.transferMap_blockTensor_R_toMPSTensor_quasi_idempotent` | None; only the non-simplicity proof used it. |
| `MPOTensor.RescalingStableLengthDependentRFP.blockTensor_R_not_isHorizontalCF` | None. |
| `MPOTensor.IsHorizontalCF.eq_one_of_transferMap_comp_self_eq_smul` | None. |
| `MPSTensor.IsBNTCanonicalForm.eq_one_of_transferMap_comp_self_eq_smul` | None; the deleted horizontal-form version was its only consumer. |
| `MPOTensor.SimpleVanishingCounterexample.*` (whole namespace) | None; the module is deleted. |

The private helper `R_mpo_ne_zero` went with
`R_isNonvanishingSourceSimple`. `MPSTensor.GaugeEquiv.transferMap_comp_self_eq_smul_iff`
and `MPSTensor.mixedMapLM_comp_self_eq_smul_of_transferMap_comp_self_eq_smul`
are kept: both are general transfer-map lemmas with their own blueprint nodes.

## Deleted modules

| Module | Disposition |
|---|---|
| `TNLean/MPS/MPDO/SimpleVanishingCounterexample.lean` | Deleted; its bond-two witness separated only the invented nonvanishing clause from Definition 4.7. |
| `TNLean/MPS/MPDO/RescalingStableNotSimple.lean` | Deleted; its content was the unit-weight obstruction for the dimer, which is a statement about the retired reading. |

## Blueprint nodes deleted

`def:mpdo_simple_tensor` (the unit-weight definition; the label is reused by
the surviving definition), `thm:mpdo_simple_implies_source_simple`,
`def:mpdo_nonvanishing_source_simple_tensor`,
`thm:mpdo_simple_implies_nonvanishing_source_simple_of_nonzero`,
`thm:mpdo_nonvanishing_source_simple_positive_rescaling`,
`thm:mpdo_nonvanishing_source_simple_positive_rescaling_iff`,
`thm:mpdo_simple_vanishing_source_simple_status`,
`thm:bnt_unit_weight_quasi_idempotent_scalar`,
`thm:mpdo_horizontal_cf_quasi_idempotent_scalar`,
`thm:mpdo_bnt_label_rescaling_stable_not_simple`,
`thm:mpdo_bnt_label_rescaling_stable_nonvanishing_source_simple`,
`thm:mpdo_bnt_label_rescaling_stable_simplicity_verdicts`.

## Blueprint labels renamed

| Old label | New label |
|---|---|
| `def:mpdo_source_simple_tensor` | `def:mpdo_simple_tensor` |
| `thm:mpdo_source_simple_exists_nonzero` | `thm:mpdo_simple_exists_nonzero` |
| `thm:mpdo_source_simple_positive_rescaling` | `thm:mpdo_simple_positive_rescaling` |
| `thm:mpdo_source_simple_positive_rescaling_iff` | `thm:mpdo_simple_positive_rescaling_iff` |
| `thm:mpdo_bnt_label_rescaling_stable_source_simple` | `thm:mpdo_bnt_label_rescaling_stable_simple` |

## Markers removed

The sentences asserting that a theorem "does not assert `MPOTensor.IsSimple R`"
were removed from `RescalingStableLengthDependentRFP.lean` and
`RescalingStableLengthDependentRFPCanonicalForm.lean`, together with the
`**Scope restriction (fixed representative)**` stamp on
`doubledPhysTraceTransfer_retainedBlock_not_isNilpotent`: under the convention
the dimer is simple, so the disclaimer was stale. The disambiguating sentence
in `TNLean/MPS/MPU/Simple.lean`, which distinguishes MPU simplicity
(arXiv:1703.09188 Definition III.2) from the CPSV16 predicate, is kept: it
names a predicate that still exists and separates two unrelated notions.

---

# Counterexamples and printed-status nodes outside the canonical-form convention

This second part of the pass removes counterexample modules and `\notready`
printed-status nodes whose refuting witness lies outside the standing
conventions of the source it was aimed at. Each witness below was read before
removal; each is excluded by a convention the source states in its own words.
A counterexample on nondegenerate data keeps its module and its note, and none
of those were touched.

Two of the five items, (i) and (v), were withdrawn on review and their
material restored; the reasons are recorded with the items. Retiring a
counterexample is admissible only once the intended reading is carried by the
predicate itself, and in both cases it is not.

## Readings retired

**(i) A bond space with a hidden nilpotent sector is not a canonical form —
withdrawn.** The reading proposed here was that CPSV16 reduces any tensor to a
canonical form before stating results about it (lines 205–222 iterate the
invariant-subspace projection until no non-trivial invariant subspace remains,
and the proposition at line 249 records that after blocking every tensor has
such a representative generating the same family), so that the two purification
witnesses — the zero tensor at $d=D=1$, and the constant one-letter tensor with
sole entry
$Q=\bigl(\begin{smallmatrix}1&0&0\\0&0&1\\0&0&0\end{smallmatrix}\bigr)$, whose
generated density operator is the scalar $1$ at every positive length while
$Q^2$ loses the $(2,3)$ entry — lie outside the convention.

At the time of this audit, this item was withdrawn and the witnesses were
restored because `MPOTensor.IsPRFP` recorded only positive-length global-family
equality. The audit therefore correctly retained $Q$ against that predicate
as it then stood.

This current-status conclusion was superseded on 2026-08-28. Lines 744–763
first give the one-site ancillary-contraction presentation `Psipuri`, interpret
it as the global MPDO equation, and then continue with the same tensor $A$.
`MPOTensor.IsPRFP` now carries that local presentation directly, without a
canonical-form assumption. The nilpotent $Q$ example consequently separates
global-family equality from the local presentation but is not a source
counterexample. The obsolete source-counterexample declarations were removed,
the local-presentation equivalence of clauses (i) and (ii) is proved, and the
full Theorem 4.4 node remains `\notready` only for equivalence with clause (iii),
the repeated-copy density form.

**(ii) Two identical blocks are not a basis of normal tensors.** The
duplicate-scalar example put the same $1\times1$ block in two sectors with
weights $1$ and $2$. Blocks related by similarity and phase are never a basis
of normal tensors in the source's sense, which every statement in the biCF
chain assumes. The example is a useful observation about which
`HorizontalCFData` fields are independent of the others, and it survives as
prose in `docs/paper-gaps/cpgsv17_bicf_block_separation.tex`; it is not a
counterexample and is no longer registered as one.

**(iii) A single physical letter cannot carry a physical direct sum.** The
display `III_CFI_RFP` (lines 543–554) was read as an ordinary virtual block
diagonal at each fixed physical letter, giving $\operatorname{diag}(1,-1)$ at
$d=1$ as a tensor satisfying the display but not $AA=A$. The very next
sentence of the source (lines 559–563) says that the indices $j$ and $q$
"give rise to a direct sum in both physical and virtual spaces", which a
one-letter tensor cannot realize. The genuine open question — the source gives
no $q$-indexed isometry equation and no dimension condition for the physical
routing — is unaffected and stays in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`.

**(iv) The MPU witness has no canonical-form-II presentation.** The source-$v$
Gram example at $d=1$, $D=2$ with $U^{00}=\bigl(\begin{smallmatrix}1&1\\
0&0\end{smallmatrix}\bigr)$ proved its own exclusion: its normalized transfer
map has no positive-definite fixed point, so it admits no canonical-form-II
presentation with full support. Canonical form II
(arXiv:1703.09188, equations (6a)–(6b)) is the standing presentation of every
statement around Theorem III.8, and $\rho_n>0$ is one of its two clauses.

**(v) Empty product sectors do not occur in the fusion clause — withdrawn.**
The reading proposed here was that the fields `multiplicity_pos` and
`weight_pos` of `MPOTensor.BNTFusionTensorClause`, both cited to Proposition
4.13, already exclude the empty product sectors the printed-status node
objected to.

They do not. Both fields are indexed by a single BNT label $\alpha$: they say
that each label has a nonempty multiplicity space with positive weights. The
fusion clause ranges over triples, and the size $\chi_{\alpha,\beta,\gamma}$ of
the diagonal matrix attached to a triple is an unconstrained natural number;
`chi_pos` bounds its entries from below but is vacuous when there are none. A
target label absent from a fixed product pair therefore still has empty active
support, exactly as the clause's own reconstruction field (the omitted corners
are zero) and the surviving `**Local fix (fixed-pair support and coisometry)**`
marker record. The active-support qualification of condition (iii) is a real
scope restriction, and this item is withdrawn: the `(iii_act)` label, the
`**Scope restriction (active product BNT)**` stamp, and the printed-status node
are restored. The coisometry orientation remains a recorded local
correction.

## Removed declarations

| Removed declaration | Replacement |
|---|---|
| `MPSTensor.scalarUnitTensor_isNormalTensor` (in `RFP/PhaseMultiplicityCounterexample.lean`) | Same name, relocated to `TNLean/MPS/FundamentalTheorem/SectorBNT/Examples.lean` beside `scalarUnitTensor`. |
| `MPSTensor.phaseFlipTensor` | None; the retired reading was its only consumer. |
| `MPSTensor.signPhase`, `MPSTensor.norm_signPhase` | None. |
| `MPSTensor.phaseFlipTensor_is_two_phase_copies` | None. |
| `MPSTensor.scalarUnitTensor_isIsometryCanonicalForm` | None. |
| `MPSTensor.phaseFlipTensor_no_blocking_coefficient` | None. |
| `MPSTensor.phaseFlipTensor_not_isTransferIdempotent` | None. |
| `MPSTensor.phaseFlipTensor_literal_display_ambiguity` | None. |
| `MPSTensor.duplicateScalarWeights`, `duplicateScalarDim`, `duplicateScalarBlocks` | None; the module is deleted. |
| `MPSTensor.duplicateScalarBlocks_isInjective` | None. |
| `MPSTensor.duplicateScalarBlocks_leftCanonical` | None. |
| `MPSTensor.duplicateScalarWeights_ne_zero` | None. |
| `MPSTensor.duplicateScalarBlocks_not_linearIndependent_wordEntryFamily` | None. |
| `MPSTensor.duplicateScalarBlocks_not_exists_linearIndependent_wordEntryFamily` | None. |
| `MPSTensor.duplicateScalarBlocks_not_hasBiCF` | None. |
| `MPSTensor.duplicateScalarBlocks_counterexample` (deprecated) | None. |
| `MPOTensor.SourceVCounterexample.*` (whole namespace) | None; the module is deleted. |

The 2026-08-28 source-presentation correction later removed the bare global
PRFP witnesses and the separate `MPOTensor.IsLocalPurificationRFP` name.
`MPOTensor.IsPRFP` now denotes the local ancillary-contraction predicate, while
`MPOTensor.HasGlobalPurificationEquation` remains as a separate family-level
condition.

| Removed PRFP declaration | Replacement or disposition |
|---|---|
| `MPOTensor.IsLocalPurificationRFP` | `MPOTensor.IsPRFP`. |
| `MPOTensor.IsLocalPurificationRFP.isLPDO` | `MPOTensor.IsPRFP.isLPDO`. |
| `MPOTensor.IsLocalPurificationRFP.isMPDO` | `MPOTensor.IsPRFP.isMPDO`. |
| `MPOTensor.exists_isLocalPurificationRFP_not_isZCL` | `MPOTensor.exists_isPRFP_not_isZCL`. |
| `MPOTensor.physTraceTransfer_sq_of_isLocalPurificationRFP` | `MPOTensor.physTraceTransfer_sq_of_isPRFP`. |
| `MPOTensor.isLocalPurificationRFP_iff_isLPDO_and_physTraceTransfer_sq` | `MPOTensor.isPRFP_iff_isLPDO_and_physTraceTransfer_sq`. |
| `MPOTensor.isSourceZCL_of_isLocalPurificationRFP` | `MPOTensor.isSourceZCL_of_isPRFP`. |
| `MPOTensor.isPRFP_of_isLocalPurificationRFP` | Removed as an obsolete conversion between names for the same adopted presentation. |
| `MPOTensor.IsNondegeneratePRFP.isPRFP` | The first conjunct of `MPOTensor.IsNondegeneratePRFP`; use `h.1`. |
| `MPOTensor.exists_isPRFP_not_isSourceZCL` | No replacement; `MPOTensor.isSourceZCL_of_isPRFP` records the required nonzero boundary, while `MPOTensor.IsPRFP.isPhysicalTraceIdempotent` gives the unconditional literal equation. |
| `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isSourceZCL` | No replacement; the nilpotent global-family witness does not satisfy the adopted one-site `IsPRFP` presentation. |
| `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isPhysicalTraceIdempotent` | No source-facing replacement; the witness still separates the surviving `HasPurificationRFPWitness` predicate, and hence `HasGlobalPurificationEquation`, from physical-trace idempotence. |

## Deleted modules

| Module | Disposition |
|---|---|
| `TNLean/MPS/MPU/SourceVCounterexample.lean` | Deleted; its own `not_hasFullSupport` theorem proved the witness outside the canonical-form-II hypotheses of the statement it was aimed at. |
| `TNLean/MPS/MPDO/BiCFDerivation/Counterexample.lean` | Deleted; two identical blocks are not a basis of normal tensors. The field-independence observation survives as prose in the paper-gap note. |
| `TNLean/MPS/RFP/PhaseMultiplicityCounterexample.lean` | Deleted; `scalarUnitTensor_isNormalTensor` relocated first. |

## Blueprint nodes deleted

`def:mpu_source_v_gram_counterexample_data`,
`thm:mpu_source_v_gram_identification_counterexample` (`ch28_mpu.tex`);
`thm:duplicate_scalar_blocks_counterexample`
(`ch20_mpdo_canonical_forms_intro_finite_separation.tex`);
`thm:phase_flip_tensor_not_rfp`
(`ch26_mps_rfp_direct_sums_residual_isometries.tex`).

At the audited head, `ch21_mpdo_rfp_foundations.tex` and
`ch21_mpdo_rfp_fusion_isometries_product_laws.tex` were unchanged:
`thm:cpsv_theorem44_printed_status`, `thm:global_prfp_not_source_zcl`,
`thm:nonzero_global_prfp_not_source_zcl`,
`thm:nonzero_global_prfp_not_physical_trace_idempotence`, and
`thm:cpsv_theorem414_printed_status` were retained, with items (i) and (v)
withdrawn. The 2026-08-28 correction later removed the three global-PRFP
counterexample nodes, retained the full Theorem 4.4 node as `\notready` for
clause (iii), and recorded the proved local-presentation equivalence of clauses
(i) and (ii).

## Markers and prose removed

`thm:cpsv_charact_mps_status` loses the sentence deriving a false converse
from the fixed-letter virtual-block reading; the rest of that node, which
records the missing physical-routing data, is unchanged.

`thm:mpdo_cpsv_bnt_rfp_equivalence` kept its `(iii_act)` subscript and its
`**Scope restriction (active product BNT)**` stamp. At the audited head, the
normalization marker on `isSourceZCL_of_isLocalPurificationRFP` was also
unchanged. The 2026-08-28 correction renamed the source-facing predicate to
`IsPRFP`: literal physical-trace idempotence needs no nonzero assumption, while
the separate project predicate `IsSourceZCL` still does.

## Paper-gap notes

At the audited head,
`docs/paper-gaps/cpsv16_purification_rfp_definition.tex` kept its
`false-source` (resolved) verdict together with the counterexamples it cited.
The 2026-08-28 source reading supplied the missing distinction: the one-site
presentation precedes the global equation and Definition 4.3 continues using
that same tensor. The note is now `local-correction` (resolved). The nilpotent
example is retained only as a separation between global-family equality and
the local presentation. The local-presentation equivalence of clauses (i) and
(ii) is proved; only equivalence with clause (iii), the repeated-copy density
form, remains open.

`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` moves from `false-source` to
`open-gap`, both still open: after the rewrite it records missing
physical-routing data rather than a counterexample satisfying the source
hypotheses, which is what the `false-source` kind is reserved for.
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex` keeps its verdict. In both,
the sections that cited the removed Lean declarations were rewritten to state
why the witness is out of scope, and the one docstring in
`TNLean/MPS/MPDO/PerCopyHorizontalCF.lean` that named a removed declaration now
cites only the note.

## Historical and living records

The source-wide audits
`docs/audits/2026-08-20_mpo_rfp_statement_integrity.md` and
`docs/audits/2026-08-10-cpsv16-every-label-audit.md` were updated to record the
corrected PRFP reading. Other dated records naming removed declarations were
left unchanged:
`docs/audits/2026-08-15_mpdo_dead_proof_cleanup.md`,
`docs/audits/2026-06-18_mathlib_4_31_replacement_audit.md`, and
`docs/audits/2026-04-24_issue822_biCF_finite_length.md`. This note supersedes
them where they disagree.

The living registries were also updated. The obsolete purification entry was
removed from `docs/counterexamples.md`;
`docs/audits/2026-05-08-mps-ft-paper-coverage.md` records the corrected status;
and `docs/audits/data/cpsv16-label-dispositions.tsv` maps the purification
presentation and repeated-copy labels to their Blueprint coverage. The
Theorem 4.14 rows in
`docs/audits/data/cpsv16-contained-result-anchors.tsv` remain unchanged because
they belong to the withdrawn item (v).
