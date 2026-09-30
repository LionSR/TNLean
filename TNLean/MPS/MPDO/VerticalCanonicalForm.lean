/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBNTGrouping

/-!
# Vertical canonical form of matrix product density operators

The grouped vertical decomposition of a matrix product density operator in
normalized BNT-refined horizontal form supplies a basis of normal tensors and
normalized physical sector maps. The resulting positive weights and sector
maps give the coisometry and the two exact block-diagonal identities of the
vertical canonical form.

## Main result

* `MPOTensor.verticalCF_of_horizontalCF`: every matrix product density operator
  in normalized BNT-refined horizontal form is in vertical canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A matrix product density operator in normalized BNT-refined horizontal form
is also in vertical canonical form.

The same grouped vertical decomposition supplies both the algebraic basis of
normal tensors and the normalized physical sector maps.  Their positive
weights, orthogonal isometric ranges, intertwinings, and exact reconstruction
then combine to give the vertical coisometry.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M :=
  (hHorizontal.hasVerticalBNTGroupingInputs M hM).verticalCF

end MPOTensor
