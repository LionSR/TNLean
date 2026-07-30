/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# Literal CPSV canonical form and MPO physical blocking

This module specializes the MPS-level literal CPSV blocking theorem to MPO
tensors through the doubled-index MPS tensor.

## Main results

* `MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTensor`
* `MPOTensor.IsCPSVCanonicalForm_toMPSTensor_blockTwo`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Section 2.3 and
  Appendix C.4, lines 1951--1956.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form is preserved by arbitrary positive MPO physical
blocking after passing to the doubled-index MPS tensor. -/
theorem IsCPSVCanonicalForm_toMPSTensor_blockTensor {M : MPOTensor d D}
    (hM : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor) (p : ℕ) (hp : 0 < p) :
    MPSTensor.IsCPSVCanonicalForm (blockTensor M p).toMPSTensor := by
  rw [toMPSTensor_blockTensor]
  exact (hM.blockTensor p hp).reindexPhysical (blockedDoubledIndexEquiv d p)

/-- Literal CPSV canonical form is preserved by concrete two-site MPO
blocking after passing to the doubled-index MPS tensor. -/
theorem IsCPSVCanonicalForm_toMPSTensor_blockTwo {M : MPOTensor d D}
    (hM : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor) :
    MPSTensor.IsCPSVCanonicalForm (blockTwo M).toMPSTensor := by
  rw [toMPSTensor_blockTwo]
  exact (hM.blockTensor 2 (by norm_num)).reindexPhysical (twoSiteDoubledIndexEquiv d)

end MPOTensor
