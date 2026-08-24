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

That reading excludes the source's own examples. Example 4.12, normalized as
Definition 4.1 requires, has canonical-form weights $1/\sqrt2, 1/\sqrt2$; the
dimer $R$ of `RescalingStableLengthDependentRFP` has weight $\sqrt{337/512}$.
Both have non-nilpotent physical-trace transfers and both are simple in the
source's sense, and neither carries a unit weight. The tension between the
line-246 normalization and the scale that Definition 4.1 pins is real, and it
stays recorded in
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
