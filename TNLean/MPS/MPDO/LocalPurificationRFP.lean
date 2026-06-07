/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.RFP.Defs

/-!
# Local purification RFP condition for MPDO tensors

This file records a local tensor-level purification condition for MPDO tensors.
It is motivated by the purification tensor formula `Psipuri` in arXiv:1606.00608
(Cirac--Perez-Garcia--Schuch--Verstraete), line 747, but it is not the source
purification-RFP definition.

A tensor `M` generating MPDOs need not be a renormalization fixed point in the
transfer-map sense. Instead one writes `M` through a purifying MPS tensor `A`
whose physical leg carries a spin index together with an ancillary index, so that
`M` is the ancilla contraction of `A` with its conjugate (the `Psipuri` graphic,
line 747):

  `M^{ij} = ∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})`,

and imposes the local condition that such a purification exists with `A` a
pure-state renormalization fixed point (`MPSTensor.IsRFP`, arXiv:1606.00608,
Definition 3.2).

## Scope

The predicate below is a strictly weaker local condition, not the source
purification-RFP definition. The source PRFP definition includes the global
purification equation and its trace-preserving post-ancilla structure; these are
documented in `docs/paper-gaps/cpsv16_purification_rfp_definition.tex` and
remain open. This local condition is still useful because it pins the tensor
`M^{ij}` itself, not merely the family of density operators `M` generates.

`MPOTensor.IsLocalPurificationRFP` is exactly `MPOTensor.IsLPDO` (the local
purification structure) together with the requirement that the purifying tensor,
viewed as an MPS tensor on the combined spin-ancilla index `Fin (d * dK)`, is a
pure-state RFP.

## Main definitions

* `MPOTensor.IsLocalPurificationRFP`: the local purification condition with a
  pure-state RFP purifying tensor.

## Main results

* `MPOTensor.IsLocalPurificationRFP.isLPDO`: the local condition supplies an
  LPDO witness.
* `MPOTensor.IsLocalPurificationRFP.isMPDO`: the local condition generates
  matrix product density operators.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, `Psipuri`
  (line 747), pure-state RFP Definition 3.2.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- A tensor `M` satisfies the local purification-RFP condition when it is the
ancilla contraction of a pure-state renormalization fixed point: there are a
Kraus dimension `dK`, an inner bond dimension `D'`, a purifying family
`A^{(i,k)} ∈ M_{D'}(ℂ)`, and a bond-space identification
`e : Fin D ≃ Fin D' × Fin D'`
such that

  `M^{ij} = (∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})).submatrix e e`,

and the purifying tensor `A`, viewed as an MPS tensor on the combined
spin–ancilla index `Fin (d * dK)`, is a pure-state renormalization fixed point.

**Scope restriction:** This is a local tensor condition motivated by
arXiv:1606.00608, `Psipuri` (line 747), not the source PRFP definition itself.
The missing global purification and post-ancilla trace-preserving structure is
documented in `docs/paper-gaps/cpsv16_purification_rfp_definition.tex`. -/
def IsLocalPurificationRFP (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    (∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    ∧ MPSTensor.IsRFP (fun p : Fin (d * dK) => A p.divNat p.modNat)

/-- The local purification-RFP condition has the local purification structure:
its purifying data is an `IsLPDO` witness (the RFP condition on the purifying
tensor is dropped). -/
theorem IsLocalPurificationRFP.isLPDO {M : MPOTensor d D}
    (h : IsLocalPurificationRFP M) : IsLPDO M := by
  obtain ⟨dK, D', A, e, hM, _⟩ := h
  exact ⟨dK, D', A, e, hM⟩

/-- The local purification-RFP condition generates matrix product density
operators: tracing the ancilla of the purification yields a positive
semidefinite operator at every system size (via `IsLPDO.isMPDO`). -/
theorem IsLocalPurificationRFP.isMPDO {M : MPOTensor d D}
    (h : IsLocalPurificationRFP M) : IsMPDO M :=
  h.isLPDO.isMPDO

end MPOTensor
