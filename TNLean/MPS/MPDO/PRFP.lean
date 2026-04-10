/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.RFP.Defs

/-!
# Purification RFP for LPDO tensors

This file packages the local purification data used by `MPOTensor.IsLPDO` and
defines the mixed-state purification RFP condition from arXiv:1606.00608,
Definition 4.3.

## Main definitions

* `MPOTensor.IsLPDOWitness`: a packaged LPDO witness for a fixed purifying
  tensor family and bond-space equivalence.
* `MPOTensor.purifyingMPSTensor`: the doubled-index MPS tensor associated to
  a purifying family `A`.
* `MPOTensor.IsPRFP`: an MPO tensor admits an LPDO witness whose purifying MPS
  tensor is a pure-state RFP.

## References

* [CPGSV17] arXiv:1606.00608, §4.3
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- A packaged witness for the LPDO relation of `M` with a fixed purifying
family `A` and bond-space identification `e`. This isolates the witness data
from `IsLPDO` so it can be reused in purification-RFP statements. -/
def IsLPDOWitness {dK D' : ℕ} (M : MPOTensor d D)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') : Prop :=
  ∀ i j : Fin d, M i j = (∑ k : Fin dK,
    (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e

/-- The MPS tensor obtained by bundling the physical and ancilla indices of a
purifying family `A`. -/
def purifyingMPSTensor {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) : MPSTensor (d * dK) D' :=
  fun ik => A ik.divNat ik.modNat

@[simp] lemma purifyingMPSTensor_apply {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (ik : Fin (d * dK)) :
    purifyingMPSTensor A ik = A ik.divNat ik.modNat :=
  rfl

/-- Repackaging `IsLPDO` in terms of `IsLPDOWitness`. -/
theorem isLPDO_iff_exists_witness (M : MPOTensor d D) :
    IsLPDO M ↔
      ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
        (e : Fin D ≃ Fin D' × Fin D'),
        IsLPDOWitness M A e := by
  simp [IsLPDO, IsLPDOWitness]

/-- An LPDO has a **purification RFP** when it admits a local purification
whose purifying MPS tensor is a pure-state RFP.

See arXiv:1606.00608, Definition 4.3. -/
def IsPRFP (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    IsLPDOWitness M A e ∧ MPSTensor.IsRFP (purifyingMPSTensor A)

/-- A purification-RFP tensor is, in particular, an LPDO. -/
theorem IsPRFP.isLPDO {M : MPOTensor d D} (h : IsPRFP M) : IsLPDO M := by
  rcases h with ⟨dK, D', A, e, hWitness, _hRFP⟩
  exact ⟨dK, D', A, e, hWitness⟩

/-!
### Future work

`IsPRFP.isZCL`: for an LPDO, PRFP should imply MPO ZCL. The proof requires
formalizing the transfer-map correspondence between an LPDO witness
`IsLPDOWitness M A e` and the MPO transfer map of `M`, then transporting
`MPSTensor.IsRFP (purifyingMPSTensor A)` across that correspondence. This
implication is intentionally not exported until the proof is completed, to
keep the development sound.
-/

end MPOTensor
