/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FixedBondProductTensor
import TNLean.MPS.MPDO.InverseMapActiveSectorRecurrence
import TNLean.MPS.MPDO.PhysicalSupportBondTransport

/-!
# Normal representative for the SAL-selected commuting-bond product

The positive physical-sector factorization of an injective tensor satisfying
the strong area law selects a particular commuting bond. The tensor itself
represents the products of this bond exactly, with scalar one. If its
doubled-index tensor is normal, it is therefore already a normal representative
of the selected product family.

This is the forward construction in Proposition C.8. It does not assert that
an arbitrary proportional commuting-bond presentation, or an arbitrary
matrix-product representation of its products, has a normal rescaling.

## Main declarations

* `PhysicalSectorFactorization.fixedProductTensorData`
* `MPOTensor.exists_normal_fixedProductTensorData_of_isSAL`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemma C.4 and Proposition C.8, lines 1435--1450 and
  1570--1593
-/

open scoped ComplexOrder

namespace MPOTensor

namespace PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The bond selected by a positive physical-sector factorization is represented
exactly by the source tensor itself.

Unlike an arbitrary finite-state representation of the same closed operators,
this representation has no additional virtual summand: its tensor is the
original `K`. The coefficient in the periodic bond-product identity is one at
every length at least two.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
C.8 (`3to4`), lines 1581--1593. -/
noncomputable def fixedProductTensorData
    (F : PhysicalSectorFactorization K)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hD : 0 < D) :
    TranslationInvariantBondData.FixedProductTensorData
      (F.translationInvariantBondData hη) where
  bondDim := D
  bondDim_pos := hD
  tensor := K
  mpo_eq_product := by
    intro N hN
    change mpo K N =
      (List.ofFn fun i : Fin N ↦
        embedLocalOperator (d := d) 2 N hN i F.physicalBond).prod
    exact F.mpo_eq_product_physicalBond hN

end PhysicalSectorFactorization

/-- An injective normal MPO tensor satisfying SAL is itself a normal
matrix-product representative of the commuting-bond product selected in the
proof of Proposition C.8. The local scalar is one; no assertion is made about
an arbitrary proportional commuting-bond presentation.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1570--1593. The positive physical-sector factorization is constructed in
Lemma C.4 (`propSN`), lines 1406--1450. -/
theorem exists_normal_fixedProductTensorData_of_isSAL
    {d D : ℕ} (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K)
    (hNormal : MPSTensor.IsNormalTensor K.toMPSTensor) :
    ∃ (F : PhysicalSectorFactorization K)
      (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef),
      let repr := F.fixedProductTensorData hη (bondDim_pos_of_isSAL K hSAL)
      MPSTensor.IsNormalTensor repr.tensor.toMPSTensor ∧
        ∀ (N : ℕ) (hN : 2 ≤ N),
          mpo K N =
            ((F.translationInvariantBondData hη).toCommutingFormData hN).product := by
  obtain ⟨F, hη⟩ := exists_positive_physicalSectorFactorization_of_isSAL K hK hSAL
  let repr := F.fixedProductTensorData hη (bondDim_pos_of_isSAL K hSAL)
  refine ⟨F, hη, ?_, ?_⟩
  · exact hNormal
  · intro N hN
    exact repr.mpo_eq_product N hN

end MPOTensor
