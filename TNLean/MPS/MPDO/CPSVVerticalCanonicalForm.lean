/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVFigureEight
import TNLean.MPS.MPDO.CPSVVerticalBNT
import TNLean.MPS.MPDO.VerticalCanonicalFormConstruction

/-!
# Vertical canonical form from literal CPSV canonical form

The literal CPSV canonical-form decomposition groups the normal vertical
corners by matrix-product-vector phase class.  The grouped Figure 8 identity
normalizes their internal gauges, after which the orthogonal physical sector
maps assemble into the coisometry of the vertical canonical form.

## Main result

* `MPOTensor.verticalCF_of_cpsvCanonicalForm`: every matrix product density
  operator in literal CPSV canonical form is in vertical canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in literal CPSV canonical form is also
in vertical canonical form.

The literal grouped decomposition supplies a basis of normal representatives
and positive grouped coefficients.  Gram normalization gives orthogonal
isometric physical sector maps.  Their block row is the required coisometry,
with orientation $U U^\dagger=I$, and the two direct-sum identities follow from
the exact letterwise reconstruction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_cpsvCanonicalForm (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M) :
    IsVerticalCF M := by
  apply verticalCF_of_grouping_and_gramDressing M
  · exact hCanonical.exists_verticalBNTGrouping_with_isometry M hM
  · intro n A VX VY X Y cX cY hcX hcY hcornerX hcornerY
    exact hCanonical.gramDressing_eq_of_two_grouped_corners M hM
      A VX VY X Y cX cY hcX hcY hcornerX hcornerY

end MPOTensor
