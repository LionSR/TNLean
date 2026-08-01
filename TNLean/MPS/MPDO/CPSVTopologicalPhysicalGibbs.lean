/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVBNTFusionTensorClauseFromRFP
import TNLean.MPS.MPDO.TopologicalPhysicalGibbs

/-!
# Literal CPSV RFP tensors have a physical commuting Gibbs decomposition

This file selects the BNT fusion tensor clause furnished by the literal CPSV
canonical-form theorem and applies the physical-coordinate Gibbs construction.

## Main definitions

* `MPOTensor.cpsvRFPBNTFusionTensorClause`

## Main result

* `MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorems 4.14 and 4.15 and Appendix C.4
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-- A BNT fusion tensor clause selected from the literal CPSV canonical-form
and renormalization fixed-point hypotheses.

Source: CPSV16, Theorem 4.14(i),(iii), lines 972--993, and Appendix C.4,
lines 1929--2046 of `Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (active product BNT):** Only nonzero product corners occur;
an absent output sector has zero multiplicity. See
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** For a fixed input pair, the active
output family may be empty. See
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The retained-row fusion map is a
coisometry onto the active output sectors and satisfies exact adjoint
reconstruction; no full-space isometry is asserted. See
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
noncomputable def cpsvRFPBNTFusionTensorClause (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M) :
    BNTFusionTensorClause M :=
  Classical.choice
    (HasBNTFusionTensorClause.of_isRFPViaTS M hCanonical hM hRFP)

/-- **Physical-coordinate commuting Gibbs decomposition for a literal CPSV
RFP MPDO above one site.**

For a tensor in literal CPSV canonical form which generates MPDOs and satisfies
the renormalization fixed-point condition, select its BNT fusion tensor clause.
If the associated coefficient family is independent of the chain length, then
the selected clause gives the physical-coordinate commuting Gibbs
decomposition on every chain of length `N + 2`.

Source: CPSV16, Theorem 4.14(i),(iii), lines 972--993, Theorem 4.15,
lines 1013--1016, and Appendix C.4, lines 1929--2046 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (active product BNT):** Only nonzero product corners occur;
an absent output sector has zero multiplicity. See
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** For a fixed input pair, the active
output family may be empty. See
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The retained-row fusion map is a
coisometry onto the active output sectors and satisfies exact adjoint
reconstruction; no full-space isometry is asserted. See
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

**Local fix (physical complement):** The retained energy is extended by zero
on the orthogonal physical complement, and the retained projectors are
transported through the adjoint sitewise coisometry. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.

**Scope restriction (positive chains of length at least two):** Definition 4.8
does not specify a length-one two-site convention. This theorem covers exactly
the source-defined lengths `N + 2`; see
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. -/
theorem physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M)
    (hLI : (BNTLabelCoefficientFamily.ofChi
      (cpsvRFPBNTFusionTensorClause M hCanonical hM hRFP).chi).LengthIndependent) :
    let H := cpsvRFPBNTFusionTensorClause M hCanonical hM hRFP
    H.HasPhysicalTopologicalGibbsDecomposition hM := by
  dsimp only
  exact
    BNTFusionTensorClause.hasPhysicalTopologicalGibbsDecomposition
      (cpsvRFPBNTFusionTensorClause M hCanonical hM hRFP) hM hLI

end MPOTensor
