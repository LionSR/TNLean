# Common hypotheses for the vertical BNT construction

This note records the consolidation of the hypotheses of the vertical BNT
construction for CPSV16. The source is
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

## Verification

The change was ported onto current `main` from a local snapshot of
2026-09-26. Every module that imported a removed file, and every module whose
source changed, was rebuilt with `scripts/lake_build_locked.sh`:
`VerticalBNTGrouping`, `VerticalProductSpectralFamily`,
`VerticalProductCornerPositivity`, `VerticalProductFusionDecomposition`,
`RFPPositiveFusionDecomposition`, `BNTFusionTensorClauseFromRFP`,
`BNTAlgebraTensorClauseSpectrum`, `CPSVBNTTheoremEquivalence`,
`CPSVTopologicalPhysicalGibbs`, and the `TNLean.MPS.MPDO` aggregator.
Blueprint `\lean{}` tags that named removed declarations were retargeted to
the common theorems, and `scripts/blueprint_lean_sync.py --ci` passes.
