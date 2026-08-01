/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFusionTensorClauseFromRFP
import TNLean.MPS.MPDO.CPSVVerticalDecomposition
import TNLean.MPS.MPDO.CPSVVerticalProductFusionDecomposition

/-!
# Literal CPSV RFP tensors satisfy the BNT fusion clause

This file proves the source-faithful implication from the literal CPSV
canonical-form and renormalization fixed-point hypotheses to the active-sector
BNT fusion tensor clause.

## Main result

* `MPOTensor.HasBNTFusionTensorClause.of_isRFPViaTS`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and Appendix C.4
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

namespace HasBNTFusionTensorClause

/-- **Corrected active-support formulation of Theorem 4.14(i) implies (iii).**
An MPDO in literal CPSV canonical form that satisfies the Definition 4.1
renormalization fixed-point condition has the active-support BNT fusion clause.

**Scope restriction (active product BNT):** Only active product corners are
retained. A one-site BNT label absent from a fixed product pair has zero fusion
multiplicity. Documented in
`docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

**Local fix (Figure-11 fixed-pair support):** A fixed pair may have an empty
active family; no unsupported corner is inserted. Documented in
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`.

**Local fix (Figure-11 fusion coisometry):** The fusion map has retained-row
orientation and is a coisometry onto the active direct sum. Its adjoint gives
the exact reconstruction. Documented in
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

Source: CPSV16, Theorem 4.14(i),(iii), lines 972--993, and Appendix C.4,
lines 1929--2046 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem of_isRFPViaTS (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M) :
    HasBNTFusionTensorClause M := by
  classical
  obtain ⟨D₁⟩ := hCanonical.exists_cpsvVerticalDecomposition M hM
  obtain ⟨D₂⟩ := hCanonical.exists_cpsvVerticalDecomposition_blockTwo M hM
  obtain ⟨Smap, T, hSCPTP, hTCPTP, hSphys, hTphys⟩ := hRFP
  obtain ⟨sigma, hDim, V, _hContract, hLetter⟩ :=
    transportedVerticalSector_exists_unitaryBlockEquiv_coefficient_eq
      D₁.bondDim D₁.multiplicity D₁.weight
      D₂.bondDim D₂.multiplicity D₂.weight
      D₁.multiplicity_pos D₁.weight_pos
      D₂.multiplicity_pos D₂.weight_pos
      M D₁.tensor D₂.tensor D₁.isCPSVBNT D₂.isCPSVBNT
      D₁.verticalCoisometry D₂.verticalCoisometry
      D₁.coisometry D₂.coisometry T Smap hTCPTP hSCPTP
      D₁.forward D₁.reconstruction D₂.forward D₂.reconstruction
      hTphys hSphys
  obtain ⟨chi, U, hChiPos, hU, hFusion, hFusionReconstruction⟩ :=
    exists_positiveFusionDecomposition_of_unitaryBlockEquiv_of_cpsvCanonicalForm
      D₁.bondDim D₁.multiplicity D₁.weight
      D₂.bondDim D₂.multiplicity D₂.weight
      D₁.multiplicity_pos D₁.weight_pos
      D₂.multiplicity_pos D₂.weight_pos
      M D₁.tensor D₂.tensor D₂.isCPSVBNT
      D₁.verticalCoisometry D₂.verticalCoisometry
      D₁.coisometry D₂.coisometry D₁.reconstruction D₂.reconstruction
      sigma hDim V hLetter hCanonical hM
  exact of_verticalDecompositions_of_unitaryBlockEquiv
    D₁ D₂ sigma hDim V hLetter chi U hChiPos hU hFusion
      hFusionReconstruction

end HasBNTFusionTensorClause

end MPOTensor
