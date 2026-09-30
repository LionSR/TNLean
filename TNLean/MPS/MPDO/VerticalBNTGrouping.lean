/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVFigureEight
import TNLean.MPS.MPDO.CPSVVerticalBNT
import TNLean.MPS.MPDO.VerticalCanonicalFormConstruction

/-!
# Inputs of the grouped vertical decomposition

The grouped vertical construction of Proposition 4.13 consumes exactly two
properties of a matrix product density operator: the phase-class grouping of
its normal vertical sectors with their physical isometries, and the pairwise
Figure 8 comparison of two positive corners of a common representative. This
file names that pair of inputs and records that both literal CPSV canonical
form and normalized BNT-refined horizontal form supply it.

The two canonical-form predicates stay independent: each one proves the two
inputs from its own grouping and Figure 8 theorems, and no implication
between them is used or asserted.

## Main definitions

* `MPOTensor.HasVerticalBNTGroupingInputs`: the grouping and the
  grouped-corner Gram dressing of a matrix product density operator.

## Main results

* `MPOTensor.IsHorizontalCF.hasVerticalBNTGroupingInputs` and
  `MPSTensor.IsCPSVCanonicalForm.hasVerticalBNTGroupingInputs`: each
  canonical form supplies both inputs.
* `MPOTensor.HasVerticalBNTGroupingInputs.verticalCF`: the two inputs give
  vertical canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The two canonical-form-specific inputs of the grouped vertical
construction.

The first field groups the normal vertical sectors by matrix-product-vector
phase class while retaining their physical reducing isometries. The second
field compares the Gram dressings of any two positive vertical corners of a
common representative.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
structure HasVerticalBNTGroupingInputs (M : MPOTensor d D) : Prop where
  /-- The phase-class grouping with physical reducing isometries. -/
  grouping : HasVerticalBNTGroupingWithIsometry M
  /-- The pairwise Figure 8 comparison of two positive vertical corners. -/
  gramDressing : HasGroupedCornerGramDressing M

/-- Both inputs of the grouped vertical construction give vertical canonical
form.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem HasVerticalBNTGroupingInputs.verticalCF {M : MPOTensor d D}
    (h : HasVerticalBNTGroupingInputs M) : IsVerticalCF M :=
  verticalCF_of_grouping_and_gramDressing M h.grouping h.gramDressing

/-- Normalized BNT-refined horizontal form compares the Gram dressings of two
positive vertical corners of a common representative.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem IsHorizontalCF.hasGroupedCornerGramDressing (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    HasGroupedCornerGramDressing M := by
  intro n A VX VY X Y cX cY hcX hcY hcornerX hcornerY
  exact hHorizontal.gramDressing_eq_of_two_grouped_corners M hM
    A VX VY X Y cX cY hcX hcY hcornerX hcornerY

/-- A matrix product density operator in normalized BNT-refined horizontal
form supplies both inputs of the grouped vertical construction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1895--1919. -/
theorem IsHorizontalCF.hasVerticalBNTGroupingInputs (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    HasVerticalBNTGroupingInputs M :=
  ⟨hHorizontal.exists_verticalBNTGrouping_with_isometry M hM,
    hHorizontal.hasGroupedCornerGramDressing M hM⟩

end MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}

/-- Literal CPSV canonical form compares the Gram dressings of two positive
vertical corners of a common representative.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem hasGroupedCornerGramDressing (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : MPOTensor.IsMPDO M) :
    MPOTensor.HasGroupedCornerGramDressing M := by
  intro n A VX VY X Y cX cY hcX hcY hcornerX hcornerY
  exact hCanonical.gramDressing_eq_of_two_grouped_corners M hM
    A VX VY X Y cX cY hcX hcY hcornerX hcornerY

/-- A matrix product density operator in literal CPSV canonical form supplies
both inputs of the grouped vertical construction.

Source: arXiv:1606.00608, Proposition 4.13, lines 1895--1919. -/
theorem hasVerticalBNTGroupingInputs (M : MPOTensor d D)
    (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : MPOTensor.IsMPDO M) :
    MPOTensor.HasVerticalBNTGroupingInputs M :=
  ⟨hCanonical.exists_verticalBNTGrouping_with_isometry M hM,
    hCanonical.hasGroupedCornerGramDressing M hM⟩

end MPSTensor.IsCPSVCanonicalForm
