/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RescalingStableExplicitVerticalBNT
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPViaTS

/-!
# Length-dependent BNT coefficients for a renormalization fixed point

This file assembles the established properties of the dimer tensor `R` into
an explicit positive answer to the question after Theorem 4.14 of CPSV16.

## Main result

* `exists_isRFPViaTS_not_lengthIndependent_bntCoefficients_R` exhibits `R` in
  literal CPSV canonical form as an MPDO renormalization fixed point whose
  displayed tensor-attached BNT coefficient family depends on chain length.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and the question at lines 995--997.
-/

open scoped ComplexOrder

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The dimer tensor `R` is an MPDO renormalization fixed point in literal CPSV
canonical form, and its explicit one-label tensor-attached BNT presentation has
coefficients that depend on the positive chain length.

This answers the existential question in arXiv:1606.00608, lines 995--997, for
the displayed vertical presentation. It does not assert presentation
independence. The source's standing unit-weight convention is not part of this
statement. -/
theorem exists_isRFPViaTS_not_lengthIndependent_bntCoefficients_R :
    ∃ (M : MPOTensor 4 4) (H : BNTAlgebraTensorClause M),
      MPSTensor.IsCPSVCanonicalForm M.toMPSTensor ∧
        IsMPDO M ∧ IsRFPViaTS M ∧ ¬ H.coeffs.LengthIndependent := by
  refine ⟨R, R_oneLabelBNTAlgebraTensorClause,
    R_toMPSTensor_isCPSVCanonicalForm, R_isMPDO, isRFPViaTS_R, ?_⟩
  simpa using oneLabelCoeffs_not_lengthIndependent

end MPOTensor.RescalingStableLengthDependentRFP
