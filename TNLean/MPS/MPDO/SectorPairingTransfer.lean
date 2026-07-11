/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.SectorFactorization
import TNLean.MPS.Core.MultiBlock

/-!
# Closed sector tensors and the physical-trace transfer

This file identifies the closed-sector pairing operator of
arXiv:1606.00608, Appendix C.2, lines 1473--1493, with the
physical-trace transfer of the original tensor.  Consequently the source
zero-correlation-length condition gives the corresponding pairing operator
idempotence, up to the positive scalar allowed before canonical
normalization.

## Main results

* `physTraceTransfer_eq_sum_closedSector`: a sector factorization expresses
  the physical-trace transfer as a sum of outer products of closed tensors.
* `concrete_physTraceTransfer_eq_sum_closedSector`: the identity for the
  inverse-map sector tensors constructed from an injective simple tensor.
* `closedSector_operator_quasi_idempotent`: source zero correlation length
  gives quasi-idempotence of the closed-sector pairing operator.
* `closedSector_operator_normalized_idempotent`: after the source
  normalization, the pairing operator is idempotent.
* `closedSector_operator_idempotent_of_physTraceTransfer_sq`: for a
  canonically normalized representative, the raw pairing operator is
  idempotent.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1473--1493
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- A sector factorization expresses the physical-trace transfer as the sum
of the outer products of the closed left and right sector tensors:
\[
  \mathcal T_{\cal K}=\sum_k |l_k)(r_k|.
\]

This is the operator on the left-hand side of the zero-correlation-length
identity in arXiv:1606.00608, Appendix C.2, lines 1489--1493. -/
theorem physTraceTransfer_eq_sum_closedSector
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    (K : MPOTensor d D) (hη : EtaStructure ρ)
    (l : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dL q)) (Fin (hη.dL q)) ℂ)
    (r : (q : Fin hη.m) → Fin D →
      Matrix (Fin (hη.dR q)) (Fin (hη.dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex hη.decompB hη.decompB
          ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q ↦
            Matrix.kroneckerMap (· * ·) (l q β) (r q α)) :
    physTraceTransfer K =
      ∑ q, Matrix.vecMulVec (fun β ↦ (l q β).trace) (fun α ↦ (r q α).trace) := by
  classical
  ext β α
  simp only [physTraceTransfer, Matrix.sum_apply]
  change Matrix.trace (physicalSlice K β α) = _
  rw [← Matrix.trace_reindex hη.decompB]
  rw [show Matrix.trace (Matrix.reindex hη.decompB hη.decompB (physicalSlice K β α)) =
      Matrix.trace (Matrix.reindex hη.decompB hη.decompB
        ((hη.U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
          (hη.U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)) by
    rw [Matrix.trace_reindex, Matrix.trace_reindex, Matrix.trace_mul_cycle,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]]
  rw [hfactor, Matrix.trace_blockDiagonal']
  simp only [Matrix.trace_kronecker, Matrix.vecMulVec_apply]

section InverseMapSectorTensors

variable {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
variable (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
variable (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R ρ)
variable (α₁ β₃ : Fin D) (hm : R β₃ α₁ ≠ 0)

include hρ hm

/-- For the inverse-map sector tensors of an injective simple tensor,
\[
  \mathcal T_{\cal K}=\sum_k |l_k)(r_k|.
\]
This supplies the concrete closed-tensor operator used immediately before
Lemma C.5 in arXiv:1606.00608, Appendix C.2, lines 1473--1493. -/
theorem concrete_physTraceTransfer_eq_sum_closedSector
    : physTraceTransfer K =
      ∑ q, Matrix.vecMulVec
        (closedSectorL K hK hη R α₁ β₃ q)
        (closedSectorR K hK hη β₃ q) := by
  apply physTraceTransfer_eq_sum_closedSector K hη
      (sectorTensorL K hK hη R α₁ β₃)
      (sectorTensorR K hK hη β₃)
  exact physicalSlice_sector_factorization K hK R ρ hρ hη hm

/-- Source zero correlation length makes the concrete closed-sector pairing
operator quasi-idempotent:
\[
  S^2=\lambda S,\qquad \lambda>0,
  \qquad S=\sum_k |l_k)(r_k|.
\]
The scalar is present because `IsSourceZCL` is invariant under rescaling;
the paper uses the canonically normalized representative in the display at
arXiv:1606.00608, Appendix C.2, lines 1489--1493. -/
theorem closedSector_operator_quasi_idempotent
    (hZCL : IsSourceZCL K) :
    ∃ lam : ℝ, 0 < lam ∧
      let S := ∑ q, Matrix.vecMulVec
        (closedSectorL K hK hη R α₁ β₃ q)
        (closedSectorR K hK hη β₃ q)
      S * S = (lam : ℂ) • S := by
  obtain ⟨_, lam, hlam, hmul⟩ := hZCL
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  rw [← concrete_physTraceTransfer_eq_sum_closedSector K hK hη R hρ α₁ β₃ hm]
  exact hmul

/-- After the positive source normalization, the concrete closed-sector
pairing operator is idempotent.  This is the normalized form of the displayed
zero-correlation-length identity in arXiv:1606.00608, Appendix C.2,
lines 1489--1493. -/
theorem closedSector_operator_normalized_idempotent
    (hZCL : IsSourceZCL K) :
    ∃ lam : ℝ, 0 < lam ∧
      let S := ∑ q, Matrix.vecMulVec
        (closedSectorL K hK hη R α₁ β₃ q)
        (closedSectorR K hK hη β₃ q)
      IsIdempotentElem ((lam : ℂ)⁻¹ • S) := by
  obtain ⟨lam, hlam, hidem⟩ := hZCL.normalized_idempotent
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  rw [← concrete_physTraceTransfer_eq_sum_closedSector K hK hη R hρ α₁ β₃ hm]
  exact hidem

/-- For a canonically normalized representative whose physical-trace transfer
is literally idempotent, the raw closed-sector pairing operator satisfies
\[
  \left(\sum_k |l_k)(r_k|\right)^2=\sum_k |l_k)(r_k|.
\]
This is the displayed zero-correlation-length identity used in
arXiv:1606.00608, Appendix C.2, lines 1489--1493. -/
theorem closedSector_operator_idempotent_of_physTraceTransfer_sq
    (hT_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K) :
    let S := ∑ q, Matrix.vecMulVec
      (closedSectorL K hK hη R α₁ β₃ q)
      (closedSectorR K hK hη β₃ q)
    S * S = S := by
  dsimp only
  rw [← concrete_physTraceTransfer_eq_sum_closedSector K hK hη R hρ α₁ β₃ hm]
  exact hT_sq

end InverseMapSectorTensors

end MPOTensor
