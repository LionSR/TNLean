/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingFormBridge
import TNLean.MPS.MPDO.CyclicEdgeWeightTensor
import TNLean.MPS.MPDO.VerticalCF

/-!
# Fixed matrix-product representations of commuting-bond products

This file records the exact interface required to compare a fixed
translation-invariant commuting bond with a normal matrix-product tensor.  It
also constructs the representation whenever the bond product is already
written as a cyclic nearest-neighbor scalar weight, and transports the source
positive realization from lengths at least two to eventual nonzero MPV
proportionality.

Normality is deliberately not included in the representation datum.  The
passage from this finite tensor to a normal representative is a separate
canonical-form problem; it is not asserted in Proposition C.8 of the source.

## Main declarations

* `MPOTensor.TranslationInvariantBondData.FixedProductTensorData`
* `MPOTensor.TranslationInvariantBondData.CyclicEdgeWeightForm`
* `MPOTensor.TranslationInvariantBondData.CyclicEdgeWeightForm.toFixedProductTensorData`
* `MPOTensor.EtaLocalStructureData.eventuallyNonzeroProportionalMPV₂_fixedProductTensor`

## References

* arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
  1570--1593.
-/

open scoped BigOperators Matrix

namespace MPOTensor

variable {d D : ℕ}

namespace TranslationInvariantBondData

/-- A chain-independent matrix-product tensor whose closed operator family is
exactly the product of all translates of one fixed commuting bond.

The positive bond dimension is part of the datum.  No normality is assumed.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1570--1593. -/
structure FixedProductTensorData (data : TranslationInvariantBondData d) where
  /-- Bond dimension of the representing tensor. -/
  bondDim : ℕ
  /-- The representing bond space is nonzero. -/
  bondDim_pos : 0 < bondDim
  /-- The chain-independent matrix-product tensor. -/
  tensor : MPOTensor d bondDim
  /-- Exact entrywise realization of every finite-chain bond product in the
  source range. -/
  mpo_eq_product :
    ∀ (N : ℕ) (hN : 2 ≤ N),
      mpo tensor N = (data.toCommutingFormData hN).product

/-- A fixed bond product written entrywise as one cyclic nearest-neighbor
scalar weight in the current one-site coordinates.

This is the scalar form of the right-hand side of equation `sigmaNK2`.  The
same weight is used at every site and every chain length.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
structure CyclicEdgeWeightForm (data : TranslationInvariantBondData d) where
  /-- The chain-independent weight on two consecutive ket--bra pairs. -/
  weight : Fin d → Fin d → Fin d → Fin d → ℂ
  /-- Entrywise cyclic product formula at every length in the source range. -/
  product_apply :
    ∀ (N : ℕ) (hN : 2 ≤ N),
      letI : NeZero N := ⟨by omega⟩
      ∀ (sigma tau : Fin N → Fin d),
        (data.toCommutingFormData hN).product sigma tau =
          ∏ n : Fin N,
            weight (sigma n) (tau n) (sigma (n + 1)) (tau (n + 1))

/-- A cyclic nearest-neighbor scalar weight gives a fixed matrix-product
representation of bond dimension `d * d`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
noncomputable def CyclicEdgeWeightForm.toFixedProductTensorData
    [NeZero d] {data : TranslationInvariantBondData d}
    (form : CyclicEdgeWeightForm data) : FixedProductTensorData data where
  bondDim := d * d
  bondDim_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  tensor := cyclicEdgeWeightTensor form.weight
  mpo_eq_product := by
    intro N hN
    letI : NeZero N := ⟨by omega⟩
    ext sigma tau
    rw [mpo_cyclicEdgeWeightTensor]
    exact (form.product_apply N hN sigma tau).symm

end TranslationInvariantBondData

namespace EtaLocalStructureData

variable {M : MPOTensor d D}

/-- A fixed tensor representation of the commuting-bond product converts the
positive source realization, which begins at length two, into eventual
nonzero proportionality of the doubled-index matrix-product vectors.

No length-one realization is assumed.  No normality or geometric law for the
length-dependent scalar is asserted.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), lines
1570--1593. -/
theorem eventuallyNonzeroProportionalMPV₂_fixedProductTensor
    (data : EtaLocalStructureData M)
    (repr : TranslationInvariantBondData.FixedProductTensorData data.bondData) :
    MPSTensor.EventuallyNonzeroProportionalMPV₂
      M.toMPSTensor repr.tensor.toMPSTensor := by
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  obtain ⟨c, hc, hreal⟩ := data.realizes_mpo N hN
  refine ⟨(c : ℂ), ?_, ?_⟩
  · exact_mod_cast ne_of_gt hc
  · intro rho
    let sigma : Fin N → Fin d := fun n ↦ (rho n).divNat
    let tau : Fin N → Fin d := fun n ↦ (rho n).modNat
    have hrho : (fun n ↦ finProdFinEquiv (sigma n, tau n)) = rho := by
      funext n
      simpa [sigma, tau] using (finProdFinEquiv.apply_symm_apply (rho n))
    rw [← hrho]
    rw [MPSTensor.mpv_toMPSTensor_pairConfig,
      MPSTensor.mpv_toMPSTensor_pairConfig]
    rw [hreal, repr.mpo_eq_product N hN]
    rfl

end EtaLocalStructureData

end MPOTensor
