/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SectorFactorization
import TNLean.MPS.Core.MultiBlock
import TNLean.Algebra.PerronFrobenius.RankOne

/-!
# Closed sector tensors and the physical-trace transfer

This file identifies the closed-sector pairing operator of
arXiv:1606.00608, Appendix C.2, lines 1473--1493, with the
physical-trace transfer of the original tensor.  Consequently the source
zero-correlation-length condition gives the corresponding pairing operator
idempotence, up to the positive scalar allowed before canonical
normalization.

## Main declarations

* `physTraceTransfer_eq_sum_closedSector`: a sector factorization expresses
  the physical-trace transfer as a sum of outer products of closed tensors.
* `concrete_physTraceTransfer_eq_sum_closedSector`: the identity for the
  inverse-map sector tensors constructed from an injective simple tensor.
* `closedSectorTraceMatrix`: the matrix of pairings between the concrete
  closed right and left sector tensors.
* `closedSector_operator_quasi_idempotent`: source zero correlation length
  gives quasi-idempotence of the closed-sector pairing operator.
* `closedSector_operator_normalized_idempotent`: after the source
  normalization, the pairing operator is idempotent.
* `closedSectorTraceMatrix_normalized_trace_pow_eq_trace`: source zero
  correlation length gives the positive-power trace identity of Lemma C.5.
* `closedSectorTraceMatrix_normalized_relations`: the square--cube and
  trace-power identities hold for one common source normalization.
* `closedSector_operator_idempotent_of_physTraceTransfer_sq`: for a
  canonically normalized representative, the raw pairing operator is
  idempotent.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1473--1493
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The pairing operator obtained by closing the physical legs of the left and
right tensors in each sector:
\[
  S=\sum_k |l_k)(r_k|.
\]
This is the operator displayed in arXiv:1606.00608, Appendix C.2,
lines 1473--1493. -/
noncomputable def closedSectorPairingOperator
    {m : ℕ} {dL dR : Fin m → ℕ}
    (l : (q : Fin m) → Fin D → Matrix (Fin (dL q)) (Fin (dL q)) ℂ)
    (r : (q : Fin m) → Fin D → Matrix (Fin (dR q)) (Fin (dR q)) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  ∑ q, Matrix.vecMulVec (fun β ↦ (l q β).trace) (fun α ↦ (r q α).trace)

/-- A sector factorization expresses the physical-trace transfer as the sum
of the outer products of the closed left and right sector tensors:
\[
  \mathcal T_{\cal K}=\sum_k |l_k)(r_k|.
\]

This is the operator on the left-hand side of the zero-correlation-length
identity in arXiv:1606.00608, Appendix C.2, lines 1489--1493. -/
theorem physTraceTransfer_eq_sum_closedSector
    {m : ℕ} {dL dR : Fin m → ℕ}
    (K : MPOTensor d D)
    (decompB : Fin d ≃ Σ q : Fin m, Fin (dL q) × Fin (dR q))
    (U_B : Matrix.unitaryGroup (Fin d) ℂ)
    (l : (q : Fin m) → Fin D → Matrix (Fin (dL q)) (Fin (dL q)) ℂ)
    (r : (q : Fin m) → Fin D → Matrix (Fin (dR q)) (Fin (dR q)) ℂ)
    (hfactor : ∀ β α,
      Matrix.reindex decompB decompB
          ((U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
            (U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        = Matrix.blockDiagonal' fun q ↦
            Matrix.kroneckerMap (· * ·) (l q β) (r q α)) :
    physTraceTransfer K = closedSectorPairingOperator l r := by
  classical
  ext β α
  simp only [physTraceTransfer, Matrix.sum_apply]
  change Matrix.trace (physicalSlice K β α) = _
  rw [← Matrix.trace_reindex decompB]
  rw [show Matrix.trace (Matrix.reindex decompB decompB (physicalSlice K β α)) =
      Matrix.trace (Matrix.reindex decompB decompB
        ((U_B : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K β α *
          (U_B : Matrix (Fin d) (Fin d) ℂ)ᴴ)) by
    rw [Matrix.trace_reindex, Matrix.trace_reindex, Matrix.trace_mul_cycle,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]]
  rw [hfactor, Matrix.trace_blockDiagonal']
  simp only [closedSectorPairingOperator, Matrix.sum_apply, Matrix.trace_kronecker,
    Matrix.vecMulVec_apply]

section InverseMapSectorTensors

variable {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
variable (K : MPOTensor d D) (hK : K.IsInjective) (hη : EtaStructure ρ)
variable (R : Matrix (Fin D) (Fin D) ℂ) (hρ : IsThreeSiteClosure K R ρ)
variable (α₁ β₃ : Fin D) (hm : R β₃ α₁ ≠ 0)

/-- **The concrete closed-sector trace matrix.** Its entries pair the closed
right sector tensor with the closed left sector tensor:
\[
  T_{k,h}=(r_k\mid l_h).
\]

Source: arXiv:1606.00608, Appendix C.2, equation `Tkn`, lines 1478--1481. -/
noncomputable def closedSectorTraceMatrix : Matrix (Fin hη.m) (Fin hη.m) ℂ :=
  fun k h ↦ closedSectorR K hK hη β₃ k ⬝ᵥ
    closedSectorL K hK hη R α₁ β₃ h

/-- The entries of the concrete closed-sector trace matrix are the traces of
the neighboring operators:
\[
  T_{k,h}=\operatorname{tr}(\eta_{k,h}).
\]

Source: arXiv:1606.00608, Appendix C.2, equations `etarl` and `Tkn`,
lines 1446--1455 and 1478--1481. -/
theorem closedSectorTraceMatrix_apply (k h : Fin hη.m) :
    closedSectorTraceMatrix K hK hη R α₁ β₃ k h =
      (sectorEta K hK hη R α₁ β₃ k h).trace := by
  rw [closedSectorTraceMatrix, trace_sectorEta]

include hρ hm

/-- For the inverse-map sector tensors of an injective simple tensor,
\[
  \mathcal T_{\cal K}=\sum_k |l_k)(r_k|.
\]
This supplies the concrete closed-tensor operator used immediately before
Lemma C.5 in arXiv:1606.00608, Appendix C.2, lines 1473--1493. -/
theorem concrete_physTraceTransfer_eq_sum_closedSector
    : physTraceTransfer K = closedSectorPairingOperator
        (sectorTensorL K hK hη R α₁ β₃)
        (sectorTensorR K hK hη β₃) := by
  apply physTraceTransfer_eq_sum_closedSector K hη.decompB hη.U_B
      (sectorTensorL K hK hη R α₁ β₃)
      (sectorTensorR K hK hη β₃)
  exact physicalSlice_sector_factorization K hK R ρ hρ hη hm

/-- The positive-real up-to-scalar physical-trace relation makes the concrete
closed-sector pairing operator quasi-idempotent:
\[
  S^2=\lambda S,\qquad \lambda>0,
  \qquad S=\sum_k |l_k)(r_k|.
\]
The scalar is present because this development's relation is invariant under
positive real rescaling. The paper's source zero-correlation-length display at
arXiv:1606.00608, Appendix C.2, lines 1489--1493, is instead the literal
`λ = 1` specialization. -/
theorem closedSector_operator_quasi_idempotent
    (hZCL : IsSourceZCL K) :
    ∃ lam : ℝ, 0 < lam ∧
      let S := closedSectorPairingOperator
        (sectorTensorL K hK hη R α₁ β₃)
        (sectorTensorR K hK hη β₃)
      S * S = (lam : ℂ) • S := by
  obtain ⟨_, lam, hlam, hmul⟩ := hZCL
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  rw [← concrete_physTraceTransfer_eq_sum_closedSector K hK hη R hρ α₁ β₃ hm]
  exact hmul

/-- After the positive physical-trace normalization allowed by the up-to-scalar
relation, the concrete closed-sector pairing operator is idempotent. The
paper's source zero-correlation-length identity at arXiv:1606.00608,
Appendix C.2, lines 1489--1493, is already the literal `λ = 1` specialization. -/
theorem closedSector_operator_normalized_idempotent
    (hZCL : IsSourceZCL K) :
    ∃ lam : ℝ, 0 < lam ∧
      let S := closedSectorPairingOperator
        (sectorTensorL K hK hη R α₁ β₃)
        (sectorTensorR K hK hη β₃)
      IsIdempotentElem ((lam : ℂ)⁻¹ • S) := by
  obtain ⟨lam, hlam, hidem⟩ := hZCL.normalized_idempotent
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  rw [← concrete_physTraceTransfer_eq_sum_closedSector K hK hη R hρ α₁ β₃ hm]
  exact hidem

/-- The positive-real up-to-scalar physical-trace relation supplies one
positive normalization for which the normalized concrete closed-sector trace
matrix satisfies both
\[
  \widehat T^2=\widehat T^3
\]
and, for every positive integer `N`,
\[
  \operatorname{tr}(\widehat T^N)=\operatorname{tr}(\widehat T).
\]
These are consequences of this development's broadened relation. The analogous
display in arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines 1490--1497,
uses the paper's literal source zero correlation length, namely the `λ = 1`
specialization. The conclusions do not assert that the trace matrix is
idempotent or has rank one. -/
theorem closedSectorTraceMatrix_normalized_relations
    (hZCL : IsSourceZCL K) :
    ∃ lam : ℝ, 0 < lam ∧
      let T := closedSectorTraceMatrix K hK hη R α₁ β₃
      (((lam : ℂ)⁻¹ • T) ^ 2 = ((lam : ℂ)⁻¹ • T) ^ 3) ∧
        ∀ N : ℕ, 0 < N →
          Matrix.trace (((lam : ℂ)⁻¹ • T) ^ N) =
            Matrix.trace ((lam : ℂ)⁻¹ • T) := by
  obtain ⟨lam, hlam, hidem⟩ :=
    closedSector_operator_normalized_idempotent K hK hη R hρ α₁ β₃ hm hZCL
  let L : Matrix (Fin D) (Fin hη.m) ℂ :=
    fun β h ↦ closedSectorL K hK hη R α₁ β₃ h β
  let Q : Matrix (Fin hη.m) (Fin D) ℂ :=
    fun k α ↦ closedSectorR K hK hη β₃ k α
  have hS : closedSectorPairingOperator
      (sectorTensorL K hK hη R α₁ β₃) (sectorTensorR K hK hη β₃) = L * Q := by
    ext β α
    simp [closedSectorPairingOperator, L, Q, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, closedSectorL, closedSectorR]
  have hT : closedSectorTraceMatrix K hK hη R α₁ β₃ = Q * L := by
    ext k h
    simp [closedSectorTraceMatrix, Q, L, Matrix.mul_apply, dotProduct]
  refine ⟨lam, hlam, ?_⟩
  dsimp only
  have hrect : IsIdempotentElem (((lam : ℂ)⁻¹ • L) * Q) := by
    simpa only [Matrix.smul_mul, ← hS] using hidem
  constructor
  · have hpow := Matrix.pow_two_eq_pow_three_of_rectangular_idempotent
      ((lam : ℂ)⁻¹ • L) Q hrect
    simpa only [Matrix.mul_smul, ← hT] using hpow
  · have htrace := Matrix.trace_pow_eq_trace_of_rectangular_idempotent
      ((lam : ℂ)⁻¹ • L) Q hrect
    simpa only [Matrix.mul_smul, ← hT] using htrace

/-- Source zero correlation length implies the positive-power trace identity
for the normalized concrete closed-sector trace matrix:
\[
  \operatorname{tr}(\widehat T^N)=\operatorname{tr}(\widehat T),
  \qquad \widehat T=\lambda^{-1}T,\quad N\geq 1.
\]
The conclusion is the valid display in arXiv:1606.00608, Appendix C.2,
Lemma `SALZCL`, lines 1490--1497. It does not assert that the trace matrix is
idempotent or has rank one. -/
theorem closedSectorTraceMatrix_normalized_trace_pow_eq_trace
    (hZCL : IsSourceZCL K) :
    ∃ lam : ℝ, 0 < lam ∧
      let T := closedSectorTraceMatrix K hK hη R α₁ β₃
      ∀ N : ℕ, 0 < N →
        Matrix.trace (((lam : ℂ)⁻¹ • T) ^ N) =
          Matrix.trace ((lam : ℂ)⁻¹ • T) := by
  obtain ⟨lam, hlam, _, htrace⟩ :=
    closedSectorTraceMatrix_normalized_relations K hK hη R hρ α₁ β₃ hm hZCL
  exact ⟨lam, hlam, htrace⟩

/-- For a canonically normalized representative whose physical-trace transfer
is literally idempotent, the raw closed-sector pairing operator satisfies
\[
  \left(\sum_k |l_k)(r_k|\right)^2=\sum_k |l_k)(r_k|.
\]
This is the displayed zero-correlation-length identity used in
arXiv:1606.00608, Appendix C.2, lines 1489--1493. -/
theorem closedSector_operator_idempotent_of_physTraceTransfer_sq
    (hT_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K) :
    let S := closedSectorPairingOperator
      (sectorTensorL K hK hη R α₁ β₃)
      (sectorTensorR K hK hη β₃)
    S * S = S := by
  dsimp only
  rw [← concrete_physTraceTransfer_eq_sum_closedSector K hK hη R hρ α₁ β₃ hm]
  exact hT_sq

end InverseMapSectorTensors

end MPOTensor
