/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.RFP.Defs

/-!
# Purification renormalization fixed point (PRFP)

This file formalizes the **purification renormalization fixed point** predicate
of arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Definition 4.4
(`def:Puri-RFP`, lines 758–760).

A tensor `M` generating MPDOs need not be a renormalization fixed point in the
transfer-map sense. Instead one writes `M` through a purifying MPS tensor `A`
whose physical leg carries a spin index together with an ancillary index, so that
`M` is the ancilla contraction of `A` with its conjugate (the `Psipuri` graphic,
line 747):

  `M^{ij} = ∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})`,

and `M` is a **PRFP** when such a purification exists with `A` a pure-state
renormalization fixed point (`MPSTensor.IsRFP`, arXiv:1606.00608, Definition 3.2).

## Faithfulness

This is the **tensor-level** reading of Definition 4.4: the predicate constrains
the tensor `M^{ij}` itself (it is the Kronecker ancilla contraction of a
pure-state RFP), not merely the family of density operators `M` generates. The
source builds `M` from `A` at the tensor level (line 744, "we write the tensor
`M` … in terms of another tensor `A`"); a state-level reading would be too weak
to support the source's equivalence with zero correlation length (Theorem
line 777), as documented in
`docs/paper-gaps/cpsv16_purification_rfp_definition.tex`.

`MPOTensor.IsPRFP` is exactly `MPOTensor.IsLPDO` (the local purification structure)
together with the requirement that the purifying tensor, viewed as an MPS tensor
on the combined spin–ancilla index `Fin (d * dK)`, is a pure-state RFP.

## Main definitions

* `MPOTensor.IsPRFP`: Definition 4.4, the purification renormalization fixed
  point predicate.

## Main results

* `MPOTensor.IsPRFP.isLPDO`: a PRFP tensor has the local purification
  structure (its purifying data is an LPDO witness).
* `MPOTensor.IsPRFP.isMPDO`: a PRFP tensor generates matrix product density
  operators.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.4 (`def:Puri-RFP`, lines 758–760), `Psipuri` (line 747),
  Theorem (line 777).
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- A tensor `M` is a **purification renormalization fixed point** (PRFP) when it
is the ancilla contraction of a pure-state renormalization fixed point: there are
a Kraus dimension `dK`, an inner bond dimension `D'`, a purifying family
`A^{(i,k)} ∈ M_{D'}(ℂ)`, and a bond-space identification `e : Fin D ≃ Fin D' × Fin D'`
such that

  `M^{ij} = (∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})).submatrix e e`,

and the purifying tensor `A`, viewed as an MPS tensor on the combined
spin–ancilla index `Fin (d * dK)`, is a pure-state renormalization fixed point.

Source: arXiv:1606.00608, Definition 4.4 (`def:Puri-RFP`, lines 758–760). -/
def IsPRFP (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    (∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    ∧ MPSTensor.IsRFP (fun p : Fin (d * dK) => A p.divNat p.modNat)

/-- A purification renormalization fixed point has the local purification
structure: its purifying data is an `IsLPDO` witness (the RFP condition on the
purifying tensor is dropped). -/
theorem IsPRFP.isLPDO {M : MPOTensor d D} (h : IsPRFP M) : IsLPDO M := by
  obtain ⟨dK, D', A, e, hM, _⟩ := h
  exact ⟨dK, D', A, e, hM⟩

/-- A purification renormalization fixed point generates matrix product density
operators. This is the provable faithfulness check on `IsPRFP`: tracing the
ancilla of the purification yields a positive semidefinite operator at every
system size (via `IsLPDO.isMPDO`). -/
theorem IsPRFP.isMPDO {M : MPOTensor d D} (h : IsPRFP M) : IsMPDO M :=
  h.isLPDO.isMPDO

end MPOTensor
