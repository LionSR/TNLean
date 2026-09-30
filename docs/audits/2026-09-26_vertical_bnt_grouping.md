# Common hypotheses for the vertical BNT construction

This note records the consolidation requested in issue #7897, under the
CPSV16 continuation tracker #7480. The source is
`Papers/1606.00608/MPDO-22-12-17-2.tex`, Proposition 4.13, lines 1863–1921,
and Appendix C.4, lines 1951–2029.

## Mathematical content

The construction of a vertical basis of normal tensors uses phase-class
grouping with physical isometries and the comparison of Gram matrices of
positive corners. These are the two fields of
`MPOTensor.HasVerticalBNTGroupingInputs`. The theorem
`MPOTensor.HasVerticalBNTGroupingInputs.exists_cpsvVerticalDecomposition`
now proves the construction once from those properties.

The product construction also needs grouping and Gram comparison for the
two-site tensor, closure under invariant projectors, absence of nontrivial
periodic vectors, and detection of nonzero corners by sector compression.
`MPOTensor.HasVerticalBNTProductInputs` records these properties. Both literal
CPSV canonical form and normalized BNT-refined horizontal form imply them,
using their existing theorems independently. No implication between those two
canonical forms is introduced. The source-facing fusion conclusions retain
their original assumptions.

The retained-space coisometry and the possibility of an empty active family
for a fixed pair are unchanged. Their existing paper-gap notes remain
applicable. This consolidation does not resolve the separate specification
questions concerning the PEPS boundary construction or strict tensor-factor
non-decomposition of the twisted dimer.

## Removed declarations and replacements

The following declarations are replaced by
`MPOTensor.HasVerticalBNTGroupingInputs.exists_cpsvVerticalDecomposition`:

- `MPOTensor.IsHorizontalCF.exists_cpsvVerticalDecomposition`;
- `MPSTensor.IsCPSVCanonicalForm.exists_cpsvVerticalDecomposition`;
- `MPSTensor.IsCPSVCanonicalForm.exists_cpsvVerticalDecomposition_blockTwo`;
- `MPSTensor.IsCPSVCanonicalForm.exists_cpsvVerticalDecomposition_pair`.

For the two-site specialization, supply the grouping properties of the
blocked tensor. The paired conclusion follows by choosing the two
decompositions independently. The duplicate module
`TNLean/MPS/MPDO/CPSVVerticalDecomposition.lean` is removed; consumers call
the common theorem directly. The blueprint has one corresponding theorem,
with the one-site and two-site specializations explained immediately after it.

The product spectral-family theorems
`MPOTensor.exists_retainedProductSpectralFamily` and
`MPSTensor.IsCPSVCanonicalForm.exists_retainedProductSpectralFamily` are
replaced by
`MPOTensor.HasVerticalBNTProductInputs.exists_retainedProductSpectralFamily`.
The positive fusion-decomposition theorems
`MPOTensor.exists_positiveFusionDecomposition_of_unitaryBlockEquiv` and
`MPOTensor.exists_positiveFusionDecomposition_of_unitaryBlockEquiv_of_cpsvCanonicalForm`
are replaced by
`MPOTensor.HasVerticalBNTProductInputs.exists_positiveFusionDecomposition_of_unitaryBlockEquiv`.
The declarations
`MPOTensor.RetainedProductSpectralFamily.FlatBlockedBNTComparison.activeCoefficient_mul_phase_pos_of_cpsvCanonicalForm`
and
`MPOTensor.RetainedProductSpectralFamily.FlatBlockedBNTComparison.exists_unitaryNormalization_of_cpsvCanonicalForm`
are replaced by `activeCoefficient_mul_phase_pos` and
`exists_unitaryNormalization` in the same namespace, now taking the common
product assumptions. The BNT
fusion tensor clause is proved once by
`MPOTensor.HasBNTFusionTensorClause.of_isRFPViaTS_of_productInputs`; its two
canonical-form consequences supply the common assumptions separately.

The CPSV product spectral-family, corner-positivity, product-fusion, and BNT
fusion tensor clause modules are removed after migration of their consumers.
No deprecated aliases are retained for the deleted internal declarations.

## Continuation tracker boundary

The GitHub subissues of #7480 were inspected on September 26, 2026. The initially open concrete child was #7897 (this consolidation), alongside
#7611 (the twisted-dimer construction). A subsequent inspection found the
new notation correction #8155. Its residual-blocking entry now uses the
chapter's superscript word notation, separates statement dependencies from
proof dependencies, and displays both residual matrix factors before taking
the trace. The already-merged lemma from #8138 was incorporated because it
was absent from this checkout. The latter retains #7751 as an explicit specification question
about the allowed tensor-factor equivalences. Its coefficient, channel,
positivity, and fusion constructions are already complete; those results do
not prove the unspecified stronger non-factorization assertion.

Issue #7371 is closed as not planned, rather than proved. Its final disposition
records that no authoritative algebraic specification of the claimed PEPS
boundary construction was available. The note
`docs/paper-gaps/cpsv16_peps_boundary_rfp_specification.tex` and the unready
blueprint entries remain the mathematical record. The analogous repeated-copy
physical-isometry question is retained in the disposition of #7298. None of
these dispositions is evidence for the corresponding printed theorem.

## Verification

The locked Lake build
`scripts/lake_build_locked.sh TNLean.MPS.MPDO.BNTFusionTensorClauseFromRFP`
completed successfully (9,179 jobs), compiling the grouping module, retained
product spectra, corner comparison and positivity, product fusion, RFP positive
fusion, and the BNT fusion endpoint with the package Lean options. The pinned
Lean compiler also elaborated the multiplicity-spectrum consumer and the two
CPSV theorem-equivalence and physical-Gibbs consumers against temporary
artifacts of their changed dependencies. Repository build artifacts were not
modified by these temporary checks. Elaboration with the package Lean options
passed for the new grouping assumptions, the BNT fusion endpoint, and each of
the three changed consumers without linter warnings.

The neutral BNT fusion theorem and both canonical-form consequences were
checked with `#print axioms`; each depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The blueprint declaration scan, including
duplicate tags, passed after the merged entries were synchronized. A second
locked Lake build of `BNTAlgebraTensorClauseSpectrum`,
`CPSVBNTTheoremEquivalence`, and `CPSVTopologicalPhysicalGibbs` completed
successfully (9,317 jobs), compiling all three changed consumers and their
changed dependencies. These targeted builds do not assert a complete
repository-wide build.

The residual-blocking module incorporated from #8138 also passes its scoped
locked build (3,216 jobs). The correction for #8155 retains both the prefix
and suffix matrix products in the displayed factorization. Its blueprint
environment and label now use `theorem` and `thm:` to match the existing
Lean declaration.


The subsequent child #8194 is addressed by the theorem
`thm:mpo_eval_word_block` in the MPO foundations chapter, linked to
`MPOTensor.evalWord_blockTensor_ofFn`. It states the separate flattening of
ket and bra words, including zero blocking length and the empty chain. The
residual-blocking proof now cites this MPO theorem instead of the MPS-only
word-blocking lemma. The proof follows the existing induction on word length;
no new algebraic assumption or Lean declaration is introduced.

The subsequent full locked repository build passes (10,872 jobs). A direct
Lean environment check, importing `TNLean`, resolves all 9,940 names in
`blueprint/lean_decls`, including the newly added entries. This repeats the
declaration-membership test used by the upstream checker. The usual
`leanblueprint checkdecls` executable still terminates with exit 133 on
this macOS installation; no successful run of that executable is claimed.

A further read-only audit of the live continuation tracker found exactly
three open children: #7897, #8194, and #7611. The first two have the local
implementations described above. The remaining child of #7611, #7751,
asks which tensor-factor equivalences are permitted in the proposed
non-decoration assertion. This assertion is not a theorem of CPSV16. The
construction notes establish a one-generator exclusion and explicitly leave
multiblock factors untreated. The existing positive-length operator-family
factorization uses a unitary crossing site boundaries, so it does not decide
factorization under only on-site unitary transformations and virtual gauge
transformations. Until that equivalence class is specified, this is a
statement-selection question rather than a missing proof of a source theorem.

The final repository verification passes the locked full build (10,879 jobs)
and the generated-import check (62 aggregators, 1,472 production modules).
Blueprint synchronization passes. A direct check in the imported `TNLean`
environment resolves all 9,982 entries in `blueprint/lean_decls`. This is
the declaration-membership test used by the upstream checker; the native
`leanblueprint checkdecls` executable remains unavailable because it exits
with status 133 on this installation. Changes remain local.
