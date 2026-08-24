/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Core.TensorProductSpan

/-!
# Independent tensor products of left-canonical normal blocks

This module packages the algebraic tensor-product argument for the retained
normal blocks of the canonical-form decomposition.  The product is
left-canonical by a direct Kronecker calculation, algebraically normal by the
common homogeneous word-span length, and hence a CPSV normal tensor by the
established left-canonical bridge.

The result is project infrastructure for the tensoring clause in
arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845; it is not a
separately stated theorem of that paper.  The retained-normal-block terminology
comes from arXiv:1606.00608, equation `II_CF1`, lines 214--245.  The two
left-canonical identities are explicit project hypotheses, not an additional
claim attributed to that passage.

## Main statement

* `MPSTensor.IsNormalTensor.tensor_product_of_left_canonical` preserves CPSV
  normality for two left-canonical normal blocks;
  `MPSTensor.left_canonical_tensor_product`
  supplies the accompanying left-canonical conclusion.

## References

* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Unitaries:
  Structure, Symmetries, and Topological Invariants*, arXiv:1703.09188.
* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608.
-/

namespace MPSTensor

variable {d D e E : ℕ}

/-- The independent tensor product of two left-canonical CPSV normal blocks is
again a CPSV normal tensor.  Its left-canonicality is the conclusion of
`MPSTensor.left_canonical_tensor_product`.

For normal blocks `A` and `B`, algebraic normality follows at the common
homogeneous word length `N_A N_B`, while the two identities
\[
  \sum_i (A^i)^\dagger A^i=\mathbf 1_D,
  \qquad
  \sum_k (B^k)^\dagger B^k=\mathbf 1_E
\]
give left-canonicality of `A \boxtimes B`.  The theorem then applies
`MPSTensor.isNormalTensor_of_isNormal_leftCanonical`.

This is infrastructure for arXiv:1703.09188, proof of Theorem `IndexTh` (ii),
lines 824--845, not a separate result asserted there.  The normal-block and
left-canonical hypotheses are the project inputs for the retained
canonical-form blocks described around arXiv:1606.00608, equation `II_CF1`,
lines 214--245; the passage itself is not cited as asserting left-canonicality.
-/
theorem IsNormalTensor.tensor_product_of_left_canonical {A : MPSTensor d D}
    (hA : IsNormalTensor A)
    {B : MPSTensor e E} (hB : IsNormalTensor B)
    (hLeftA : IsLeftCanonical A) (hLeftB : IsLeftCanonical B) :
    IsNormalTensor (MPSTensor.tensorProduct A B) := by
  let _ : NeZero (D * E) :=
    ⟨Nat.mul_ne_zero hA.bondDim_ne_zero hB.bondDim_ne_zero⟩
  exact isNormalTensor_of_isNormal_leftCanonical (MPSTensor.tensorProduct A B)
    (is_normal_tensor_product A B hA.isNormal hB.isNormal)
    (left_canonical_tensor_product A B hLeftA hLeftB)

end MPSTensor
