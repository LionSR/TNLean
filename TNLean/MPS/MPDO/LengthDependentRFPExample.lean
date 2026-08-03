/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseReflectedTarget
import TNLean.MPS.MPDO.BondTwoSingletonBaseModel
import TNLean.MPS.MPDO.LengthIndependentCoefficients

/-!
# An RFP MPDO with length-dependent BNT coefficients

This file gives a positive answer to the open question after Theorem 4.14 in
arXiv:1606.00608, lines 995--997.  The bond-two singleton base model is an
MPDO in literal CPSV canonical form and carries a tensor-attached BNT algebra
clause whose unique displayed coefficient is
$c^{(L)} = (\sqrt{1/2})^L$.  The completed reverse implication of Theorem 4.14
therefore makes the model an RFP, while $c^{(1)} \ne c^{(2)}$.

The result is existential for this explicit tensor-attached BNT presentation.
It does not assert that length dependence is invariant under every possible
BNT presentation of the same tensor.

## Main results

* `normalizedSingletonCoeffs_coeff_one_ne_coeff_two`
* `normalizedSingletonCoeffs_not_lengthIndependent`
* `exists_isRFPViaTS_not_lengthIndependent_bntCoefficients`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and lines 995--1010
-/

open scoped ComplexOrder

namespace MPOTensor.BondTwoSingletonBaseModel

/-- The one-label BNT coefficient of the singleton model differs between
lengths one and two.

Source: arXiv:1606.00608, lines 995--997 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem normalizedSingletonCoeffs_coeff_one_ne_coeff_two :
    normalizedSingletonCoeffs.coeff 1 0 0 0 ≠
      normalizedSingletonCoeffs.coeff 2 0 0 0 := by
  rw [normalizedSingletonCoeffs_coeff, normalizedSingletonCoeffs_coeff]
  intro h
  have hReal' : singletonScale ^ 1 = singletonScale ^ 2 := by
    exact_mod_cast h
  have hReal : singletonScale = singletonScale ^ 2 := by
    simpa using hReal'
  have hsq : singletonScale ^ 2 = (1 / 2 : ℝ) := by
    simp [singletonScale]
  have hsqrt_sq : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [Real.sq_sqrt]
    norm_num
  rw [singletonScale] at hReal
  nlinarith

/-- The coefficient family in the singleton tensor-attached BNT clause is not
independent of the positive chain length.

Source: arXiv:1606.00608, lines 995--997 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem normalizedSingletonCoeffs_not_lengthIndependent :
    ¬ normalizedSingletonCoeffs.LengthIndependent := by
  intro h
  exact normalizedSingletonCoeffs_coeff_one_ne_coeff_two
    (h.coeff_eq one_pos (by norm_num) 0 0 0)

/-- There exists an RFP MPDO in literal CPSV canonical form with a
tensor-attached BNT presentation whose structure coefficients depend on the
chain length.

This answers the existential open question in arXiv:1606.00608, lines
995--997.  The conclusion concerns the exhibited BNT presentation; it does not
claim presentation independence. -/
theorem exists_isRFPViaTS_not_lengthIndependent_bntCoefficients :
    ∃ (M : MPOTensor 2 4) (H : BNTAlgebraTensorClause M),
      MPSTensor.IsCPSVCanonicalForm M.toMPSTensor ∧
        IsMPDO M ∧ IsRFPViaTS M ∧ ¬ H.coeffs.LengthIndependent := by
  refine ⟨baseMPO, baseMPOBNTAlgebraTensorClause,
    baseMPO_toMPSTensor_isCPSVCanonicalForm, baseMPO_isMPDO, ?_, ?_⟩
  · exact baseMPOBNTAlgebraTensorClause.isRFPViaTS
      baseMPO_toMPSTensor_isCPSVCanonicalForm baseMPO_isMPDO
  · exact normalizedSingletonCoeffs_not_lengthIndependent

end MPOTensor.BondTwoSingletonBaseModel
