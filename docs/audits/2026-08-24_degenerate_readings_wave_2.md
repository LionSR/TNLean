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
and `MPSTensor.mixedTransferMap₂_comp_self_eq_smul_of_transferMap_comp_self_eq_smul`
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

## Readings retired

**(i) A bond space with a hidden nilpotent sector is not a canonical form.**
CPSV16 reduces any tensor to a canonical form before stating results about it:
lines 205–222 iterate the invariant-subspace projection until no non-trivial
invariant subspace remains, giving $A^i=\bigoplus_k\mu_kA_k^i$ with normal
blocks and $\sum_kD_k\le D$, and the proposition at line 249 records that
after blocking every tensor has such a representative generating the same
family.
Two purification witnesses were built on representatives that fail this: the
zero tensor at $d=D=1$, and the constant one-letter tensor with sole entry
$Q=\bigl(\begin{smallmatrix}1&0&0\\0&0&1\\0&0&0\end{smallmatrix}\bigr)$, whose
closed operator is the scalar $1$ at every positive length while $Q^2$ loses
the $(2,3)$ entry. The canonical representative of $Q$ is the $1\times1$ block
$(1)$, for which every clause of Theorem 4.4 holds. Neither witness says
anything about the printed theorem; what they show is that the *unrestricted*
positive-length predicate does not pin the one-site tensor, and that is a
missing hypothesis, recorded now as an open gap rather than as a refutation.

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

**(v) Empty product sectors do not occur in the fusion clause.**
`MPOTensor.BNTFusionTensorClause` carries `multiplicity_pos` and `weight_pos`
as fields, both cited to Proposition 4.13. The printed-status node objected
that the displayed fusion clause "is not well-defined on empty product
sectors"; under the convention there are none, and
`MPOTensor.isRFPViaTS_iff_hasBNTFusionTensorClause` is the second equivalence
of Theorem 4.14. The coisometry orientation remains a recorded local
correction.

## Removed declarations

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.exists_isPRFP_not_isSourceZCL` | None; the zero tensor is not a canonical form. |
| `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isSourceZCL` | None; the nilpotent bond sector is not a canonical form. |
| `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isPhysicalTraceIdempotent` | None; it was a corollary of the same witness. |
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

The private helpers of `LocalPurificationRFP.lean` that only the removed
witnesses used (`nilpotentTransfer`, `supportProjection`,
`nilpotentGlobalPRFP`, `scalarPurifier` and their lemmas) went with them.
`MPOTensor.IsLocalPurificationRFP` and every theorem about it are unchanged.

## Deleted modules

| Module | Disposition |
|---|---|
| `TNLean/MPS/MPU/SourceVCounterexample.lean` | Deleted; its own `not_hasFullSupport` theorem proved the witness outside the canonical-form-II hypotheses of the statement it was aimed at. |
| `TNLean/MPS/MPDO/BiCFDerivation/Counterexample.lean` | Deleted; two identical blocks are not a basis of normal tensors. The field-independence observation survives as prose in the paper-gap note. |
| `TNLean/MPS/RFP/PhaseMultiplicityCounterexample.lean` | Deleted; `scalarUnitTensor_isNormalTensor` relocated first. |

## Blueprint nodes deleted

`thm:cpsv_theorem44_printed_status`, `thm:global_prfp_not_source_zcl`,
`thm:nonzero_global_prfp_not_source_zcl`,
`thm:nonzero_global_prfp_not_physical_trace_idempotence`
(`ch21_mpdo_rfp_foundations.tex`); `thm:cpsv_theorem414_printed_status`
(`ch21_mpdo_rfp_fusion_isometries_product_laws.tex`);
`def:mpu_source_v_gram_counterexample_data`,
`thm:mpu_source_v_gram_identification_counterexample` (`ch28_mpu.tex`);
`thm:duplicate_scalar_blocks_counterexample`
(`ch20_mpdo_canonical_forms_intro_finite_separation.tex`);
`thm:phase_flip_tensor_not_rfp`
(`ch26_mps_rfp_direct_sums_residual_isometries.tex`).

## Markers and prose removed

`thm:mpdo_cpsv_bnt_rfp_equivalence` loses the `(iii_act)` subscript and the
`**Scope restriction (active product BNT)**` stamp: condition (iii) is the
printed condition, and the positivity fields of the fusion clause are the
source's own. `thm:cpsv_charact_mps_status` loses the sentence deriving a
false converse from the fixed-letter virtual-block reading; the rest of that
node, which records the missing physical-routing data, is unchanged. In
`LocalPurificationRFP.lean` the `**Scope restriction (normalization)**` stamp
on `isSourceZCL_of_isLocalPurificationRFP` becomes plain prose: the hypothesis
$\mathcal T_M\ne0$ is the source's normalization, and the zero tensor that
justified the stamp is convention-excluded.

## Paper-gap note reclassified

`docs/paper-gaps/cpsv16_purification_rfp_definition.tex` moves from
`false-source` (resolved) to `open-gap` (open). The printed Theorem 4.4 is not
refuted; what is missing is a Definition 4.1 purification-RFP predicate
carrying the source's standing canonical-form clause. Until one exists, the
forward implication is formalized only on the local purification identity.

`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` and
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex` keep their verdicts; the
sections that cited the removed Lean declarations were rewritten to state why
the witness is out of scope.

## Records left as historical

Dated audit records naming the removed declarations were not rewritten:
`docs/audits/2026-08-20_mpo_rfp_statement_integrity.md`,
`docs/audits/2026-08-10-cpsv16-every-label-audit.md`,
`docs/audits/2026-08-15_mpdo_dead_proof_cleanup.md`,
`docs/audits/2026-06-18_mathlib_4_31_replacement_audit.md`, and
`docs/audits/2026-04-24_issue822_biCF_finite_length.md`. This note supersedes
them where they disagree. The living registries were updated:
`docs/counterexamples.md`, `docs/audits/2026-05-08-mps-ft-paper-coverage.md`,
`docs/audits/data/cpsv16-label-dispositions.tsv`, and the boundary patterns of
`docs/audits/data/cpsv16-contained-result-anchors.tsv`.
