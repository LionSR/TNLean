/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.VerticalBNT
import TNLean.MPS.MPDO.VerticalCanonicalFormAssembly

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

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form assumed by Proposition 4.13.
The source-faithful literal implication is proved independently by
`verticalCF_of_cpsvCanonicalForm`; the theorem below retains the stronger
horizontal hypothesis for arguments that already assume it. This scope
restriction is documented in
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem verticalCF_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    IsVerticalCF M := by
  apply verticalCF_of_grouping_and_gramDressing M
  · exact hHorizontal.exists_verticalBNTGrouping_with_isometry M hM
  · intro n A VX VY X Y cX cY hcX hcY hcornerX hcornerY
    exact hHorizontal.gramDressing_eq_of_two_grouped_corners M hM
      A VX VY X Y cX cY hcX hcY hcornerX hcornerY

end MPOTensor
