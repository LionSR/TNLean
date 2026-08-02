/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseReflectedTarget
import TNLean.MPS.MPDO.CPSVBNTFusionTensorClauseFromRFP

/-!
# The BNT form of the general MPDO renormalization fixed-point theorem

This file proves the source-faithful equivalence between conditions (i) and
(ii) of Theorem 4.14.  It also proves the corrected active-support
equivalence corresponding to conditions (i) and (iii), for an MPDO in literal
CPSV canonical form.

## Main results

* `isRFPViaTS_iff_hasBNTAlgebraTensorClause`
* `isRFPViaTS_iff_hasBNTFusionTensorClause`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and Appendix C.4
-/

noncomputable section

namespace MPOTensor

/-- **Theorem 4.14(i) if and only if (ii).** For an MPDO in literal CPSV
canonical form, the renormalization fixed-point condition is equivalent to
the tensor-attached BNT algebra clause.

**Local fix (mixed one-site/two-site prefix):** The omitted marked comparison
in the reverse implication is supplied as documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

**Local fix (zero-sector complement):** The physical maps in the reverse
implication are completed on the discarded complements as documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Theorem 4.14(i)--(ii), lines 972--985, and
Appendix C.4, lines 1929--2085. -/
theorem isRFPViaTS_iff_hasBNTAlgebraTensorClause
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) :
    IsRFPViaTS M ↔ HasBNTAlgebraTensorClause M := by
  constructor
  · intro hRFP
    exact (HasBNTFusionTensorClause.of_isRFPViaTS
      M hCanonical hM hRFP).to_hasBNTAlgebraTensorClause
  · intro hAlgebra
    exact hAlgebra.isRFPViaTS hCanonical hM

/-- **Corrected active-support form of Theorem 4.14(i) if and only if (iii).**
For an MPDO in literal CPSV canonical form, the renormalization fixed-point
condition is equivalent to the active-support BNT fusion clause.  This is the
active-support variant rather than the unrestricted printed statement (iii).

**Scope restriction (active product BNT):** Only nonzero product corners are
retained in the fusion clause.  A label absent from a fixed product pair has
zero fusion multiplicity.  Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support and coisometry):** A fixed pair may
have empty active support, and the retained-row fusion map is a coisometry.
Documented in `docs/paper-gaps/cpsv16_figure11_per_pair_support.tex` and
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

**Local fix (mixed one-site/two-site prefix):** The reverse implication uses
the marked comparison documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

**Local fix (zero-sector complement):** The physical maps in the reverse
implication are completed on the discarded complements as documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Theorem 4.14(i),(iii), lines 972--993, and
Appendix C.4, lines 1929--2085. -/
theorem isRFPViaTS_iff_hasBNTFusionTensorClause
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) :
    IsRFPViaTS M ↔ HasBNTFusionTensorClause M := by
  constructor
  · exact HasBNTFusionTensorClause.of_isRFPViaTS M hCanonical hM
  · intro hFusion
    exact hFusion.to_hasBNTAlgebraTensorClause.isRFPViaTS hCanonical hM

end MPOTensor
