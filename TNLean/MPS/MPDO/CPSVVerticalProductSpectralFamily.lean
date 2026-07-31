/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVBlocking
import TNLean.MPS.MPDO.CPSVPeriodicExclusion
import TNLean.MPS.MPDO.VerticalProductSpectralFamily

/-!
# Retained vertical product sectors from literal CPSV canonical form

Literal CPSV canonical form passes to two-site physical blocking. Proposition
4.13 supplies invariant-projector closure and excludes periodic vectors for
the blocked vertical tensor. The form-neutral retained-product construction
then gives simultaneous normal decompositions of all retained copy pairs.

## Main result

* `MPSTensor.IsCPSVCanonicalForm.exists_retainedProductSpectralFamily`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1873--1893, and Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPSTensor.IsCPSVCanonicalForm

open MPOTensor

/-- Literal CPSV canonical form and MPDO positivity give simultaneous normal
decompositions of all retained vertical copy-pair tensors. Empty active
families are preserved.

The one-site coisometric reconstruction is squared exactly. Literal canonical
form and positivity supply projector closure and absence of periodic vectors
for the blocked vertical tensor, and these properties descend to every
retained copy pair.

Source: CPSV16, Proposition 4.13, lines 1873--1893, and Appendix C.4,
lines 2020--2029. -/
theorem exists_retainedProductSpectralFamily
    {g d D : ℕ} {M : MPOTensor d D}
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (B : (α : Fin g) → MPSTensor (D * D) (dim α))
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab =
      Uᴴ * verticalAssembledTensor dim mult weight B ab * U)
    (hM : IsMPDO M) :
    Nonempty (RetainedProductSpectralFamily dim mult weight B) := by
  have hCanonicalTwo :=
    MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTwo hCanonical
  have hMTwo := hM.blockTwo
  exact MPOTensor.exists_retainedProductSpectralFamily_of_blockTwo
    dim mult weight B M U hU hReconstruct
    (hCanonicalTwo.hasInvariantProjectorClosure_verticalTensor (blockTwo M) hMTwo)
    (MPOTensor.hasNoPeriodicVectors_verticalTensor_of_cpsvCanonicalForm
      (blockTwo M) hMTwo hCanonicalTwo)

end MPSTensor.IsCPSVCanonicalForm
