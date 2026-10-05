/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SectorEncoder
import TNLean.MPS.ParentHamiltonian.CanonicalBoundedRangeGroundSpace

/-!
# Canonical sector encoders of parent-Hamiltonian ground spaces

The polar encoder has exactly the span of the original periodic representatives. The
canonical parent-kernel theorem identifies that span at a valid interaction range, including
the ring whose length equals that range. This identification makes no implicit gauge or
rescaling change to the chosen encoder columns.

## References

* Cirac, Perez-Garcia, Schuch, and Verstraete, arXiv:2011.12127,
  Section IV.C, block-injective intersection and periodic closure.
* De las Cuevas, Cirac, Schuch, and Perez-Garcia, arXiv:1606.00608,
  lines 317–345, the uniform blocking bound.
-/

namespace MPSTensor

/-- At interaction ranges at least `3 D^5`, the canonical encoder of the retained
representatives has exactly the parent kernel. Its raw columns are the actual periodic
representatives in the supplied data, and the encoder is their fixed polar factor. No separate
gauge substitution or sector matching is used. -/
theorem CPSVCanonicalFormData.range_sectorEncoder_eq_ker_parentHamiltonian
    {d D : ℕ} [NeZero d] [NeZero D] {A : MPSTensor d D}
    (data : CPSVCanonicalFormData A) {L N : ℕ} (hL : 3 * D ^ 5 ≤ L) (hLN : L ≤ N) :
    LinearMap.range
      (sectorEncoder (fun j => data.blocks (data.representativeIndex j)) N).mulVecLin =
      LinearMap.ker (parentHamiltonian A L N) := by
  rw [data.ker_parentHamiltonian_eq_of_three_bondDim_pow_five_le hL hLN, range_sectorEncoder]
  rfl

end MPSTensor
