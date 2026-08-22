/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixCyclicTracePower
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.PhysicalSectorTraceMatrix
import TNLean.MPS.MPDO.SectorPairingTransfer
import TNLean.MPS.MPDO.SectorTrace

/-!
# Unit closure traces from a neighboring trace factorization

This file records a necessary condition on any physical-sector factorization
carrying positive neighboring operators with normalized rank-one trace
coefficients, as in condition (iv) of Theorem 4.9 of arXiv:1606.00608:
closing the physical legs writes the physical-trace transfer as the
rectangular product of the two closed sector-trace matrices, and the
opposite product is exactly the rank-one coefficient matrix
$(a_kb_h)_{k,h}$.  Cyclic invariance of the trace then forces every positive
power of the physical-trace transfer, and hence every nonempty closed chain,
to have unit trace.

For a tensor carrying only the factorization data, the normalization
$\operatorname{tr}(T)=1$ invoked at line 1498 of the source is therefore not
a convention but a genuine constraint: a tensor whose closed chains do not
all have unit trace admits no factorization of the required form.  The
ambient normalization of the density operators constrains only the weighted sum
over the representatives of a basis of normal tensors (arXiv:1606.00608, lines 1755--1759), not each
representative separately, so the per-representative assertion of
Theorem 4.9 carries this unit-trace normalization as an implicit hypothesis
on each absorbed representative.

## Main results

* `PhysicalSectorFactorization.physTraceTransfer_eq_leftTraceMatrix_mul_rightTraceMatrix`:
  the physical-trace transfer is the rectangular product of the closed
  sector-trace matrices.
* `NeighboringTraceFactorization.trace_physTraceTransfer_pow_eq_one`: a
  neighboring trace factorization forces every positive power of the
  physical-trace transfer to have unit trace.
* `NeighboringTraceFactorization.trace_mpo_eq_one`: a neighboring trace
  factorization forces every nonempty closed chain to have unit trace.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9, lines 862--892; Appendix C.2, equation `Tkn` and the
  normalization step, lines 1473--1498; the ambient normalization at lines
  1755--1759.
* `docs/paper-gaps/cpgsv17_pf_rank_one.tex`, the unit-closure-trace
  necessary condition.
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The closed left sector-trace matrix
$L_{\beta,k}=\operatorname{tr}((l_k)_\beta)$, the coefficient rectangle of
the closed-sector expansion of the physical-trace transfer.

Source: arXiv:1606.00608, Appendix C.2, lines 1473--1493. -/
noncomputable def leftTraceMatrix (F : PhysicalSectorFactorization K) :
    Matrix (Fin D) (Fin F.sectorCount) ℂ :=
  Matrix.of fun beta k ↦ (F.leftTensor k beta).trace

/-- The closed right sector-trace matrix
$Q_{k,\alpha}=\operatorname{tr}((r_k)_\alpha)$, the functional rectangle of
the closed-sector expansion of the physical-trace transfer.

Source: arXiv:1606.00608, Appendix C.2, lines 1473--1493. -/
noncomputable def rightTraceMatrix (F : PhysicalSectorFactorization K) :
    Matrix (Fin F.sectorCount) (Fin D) ℂ :=
  Matrix.of fun k alpha ↦ (F.rightTensor k alpha).trace

/-- The trace of a neighboring operator is the contraction of the closed
right and left sector tensors over the shared physical index:
\[
  \operatorname{tr}(\eta_{k,h})
    =\sum_\alpha\operatorname{tr}((r_k)_\alpha)\operatorname{tr}((l_h)_\alpha).
\]

Source: arXiv:1606.00608, Appendix C.2, equation `Tkn`, lines 1478--1481. -/
theorem trace_neighboringOperator_eq_sum_trace_mul_trace
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    (F.neighboringOperator k h).trace =
      ∑ alpha : Fin D,
        (F.rightTensor k alpha).trace * (F.leftTensor h alpha).trace := by
  calc (F.neighboringOperator k h).trace
      = ∑ x : NeighborIndex F k h, ∑ alpha : Fin D,
          F.rightTensor k alpha x.1 x.1 * F.leftTensor h alpha x.2 x.2 := by
        simp [Matrix.trace, Matrix.diag]
    _ = ∑ alpha : Fin D, ∑ x : NeighborIndex F k h,
          F.rightTensor k alpha x.1 x.1 * F.leftTensor h alpha x.2 x.2 :=
        Finset.sum_comm
    _ = ∑ alpha : Fin D,
          (F.rightTensor k alpha).trace * (F.leftTensor h alpha).trace := by
        refine Finset.sum_congr rfl fun alpha _ ↦ ?_
        rw [Matrix.trace, Matrix.trace, Finset.sum_mul_sum, Fintype.sum_prod_type]
        simp [Matrix.diag]

/-- Closing the physical legs of the factorized slices writes the
physical-trace transfer as the rectangular product of the closed
sector-trace matrices:
\[
  \mathcal T_K=LQ.
\]

Source: arXiv:1606.00608, Appendix C.2, lines 1489--1493. -/
theorem physTraceTransfer_eq_leftTraceMatrix_mul_rightTraceMatrix
    (F : PhysicalSectorFactorization K) :
    physTraceTransfer K = F.leftTraceMatrix * F.rightTraceMatrix := by
  classical
  let U : Matrix.unitaryGroup (Fin d) ℂ := ⟨F.physicalIsometry, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact F.physicalIsometry_isometry⟩
  have hfactor : ∀ beta alpha,
      Matrix.reindex F.sectorEquiv F.sectorEquiv
          ((U : Matrix (Fin d) (Fin d) ℂ) * MPOTensor.physicalSlice K beta alpha *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        Matrix.blockDiagonal' fun q ↦
          Matrix.kroneckerMap (· * ·) (F.leftTensor q beta) (F.rightTensor q alpha) := by
    simpa [U] using F.factorization
  rw [MPOTensor.physTraceTransfer_eq_sum_closedSector K F.sectorEquiv U
    F.leftTensor F.rightTensor hfactor]
  ext beta alpha
  simp [MPOTensor.closedSectorPairingOperator, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Matrix.mul_apply, leftTraceMatrix, rightTraceMatrix]

/-- The opposite rectangular product has the neighboring-operator traces as
entries:
\[
  (QL)_{k,h}=\operatorname{tr}(\eta_{k,h}).
\]

Source: arXiv:1606.00608, Appendix C.2, equation `Tkn`, lines 1478--1481. -/
theorem rightTraceMatrix_mul_leftTraceMatrix_apply
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    (F.rightTraceMatrix * F.leftTraceMatrix) k h =
      (F.neighboringOperator k h).trace := by
  rw [trace_neighboringOperator_eq_sum_trace_mul_trace]
  simp [Matrix.mul_apply, rightTraceMatrix, leftTraceMatrix]

namespace NeighboringTraceFactorization

variable {F : PhysicalSectorFactorization K}

/-- Under a neighboring trace factorization, the opposite rectangular
product of the closed sector-trace matrices is the complexified rank-one
coefficient matrix $(a_kb_h)_{k,h}$.

Source: arXiv:1606.00608, Appendix C.2, lines 1478--1498. -/
theorem rightTraceMatrix_mul_leftTraceMatrix_eq_vecMulVec
    (H : NeighboringTraceFactorization F) :
    F.rightTraceMatrix * F.leftTraceMatrix =
      Matrix.vecMulVec (fun k ↦ ((H.a k : ℝ) : ℂ)) (fun k ↦ ((H.b k : ℝ) : ℂ)) := by
  ext k h
  rw [rightTraceMatrix_mul_leftTraceMatrix_apply, H.trace_neighboringOperator,
    Matrix.vecMulVec_apply]
  push_cast
  ring

/-- **Unit closure traces at every positive power.**  A neighboring trace
factorization forces every positive power of the physical-trace transfer to
have unit trace:
\[
  \operatorname{tr}(\mathcal T_K^{\,N})=1,\qquad N\geq1.
\]

This is a necessary condition on the tensor: the normalization
$\operatorname{tr}(T)=1$ invoked at line 1498 of the source is available
for a factorization of the required form only when the physical-trace
transfer itself has unit trace.

Source: arXiv:1606.00608, Appendix C.2, lines 1473--1498. -/
theorem trace_physTraceTransfer_pow_eq_one
    (H : NeighboringTraceFactorization F) {N : ℕ} (hN : 0 < N) :
    Matrix.trace (physTraceTransfer K ^ N) = 1 := by
  rw [F.physTraceTransfer_eq_leftTraceMatrix_mul_rightTraceMatrix,
    Matrix.trace_pow_mul_comm _ _ hN,
    H.rightTraceMatrix_mul_leftTraceMatrix_eq_vecMulVec]
  have hdot : (fun k ↦ ((H.b k : ℝ) : ℂ)) ⬝ᵥ (fun k ↦ ((H.a k : ℝ) : ℂ)) = 1 := by
    simp only [dotProduct]
    calc ∑ k, ((H.b k : ℝ) : ℂ) * ((H.a k : ℝ) : ℂ)
        = ((∑ k, H.a k * H.b k : ℝ) : ℂ) := by
          push_cast
          exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
      _ = 1 := by rw [H.sum_mul, Complex.ofReal_one]
  have hpow : ∀ M : ℕ,
      (Matrix.vecMulVec (fun k ↦ ((H.a k : ℝ) : ℂ))
        (fun k ↦ ((H.b k : ℝ) : ℂ))) ^ (M + 1) =
        Matrix.vecMulVec (fun k ↦ ((H.a k : ℝ) : ℂ))
          (fun k ↦ ((H.b k : ℝ) : ℂ)) := by
    intro M
    induction M with
    | zero => rw [pow_one]
    | succ M ih =>
      rw [pow_succ, ih, Matrix.vecMulVec_mul_vecMulVec, hdot, one_smul]
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [hpow M, Matrix.trace_vecMulVec]
  simp only [dotProduct]
  calc ∑ k, ((H.a k : ℝ) : ℂ) * ((H.b k : ℝ) : ℂ)
      = ((∑ k, H.a k * H.b k : ℝ) : ℂ) := by push_cast; rfl
    _ = 1 := by rw [H.sum_mul, Complex.ofReal_one]

/-- **Unit trace of the physical-trace transfer.**  A neighboring trace
factorization forces the physical-trace transfer to have unit trace.  In
particular, under literal zero correlation length the physical-trace
transfer is an idempotent of unit trace.

Source: arXiv:1606.00608, Appendix C.2, the normalization step at line
1498. -/
theorem trace_physTraceTransfer_eq_one
    (H : NeighboringTraceFactorization F) :
    Matrix.trace (physTraceTransfer K) = 1 := by
  simpa using H.trace_physTraceTransfer_pow_eq_one Nat.one_pos

/-- **Unit closure traces at every positive length.**  A neighboring trace
factorization forces every nonempty closed chain of the tensor to have unit
trace:
\[
  \operatorname{tr}\rho^{(N)}=1,\qquad N\geq1.
\]

The ambient normalization of the density operators constrains only the
weighted sum over basis-of-normal-tensors representatives
(arXiv:1606.00608, lines 1755--1759), so for each absorbed representative
this unit-trace condition is an implicit constraint carried by the
per-representative assertion of Theorem 4.9, condition (iv), lines
862--892. -/
theorem trace_mpo_eq_one (H : NeighboringTraceFactorization F)
    {N : ℕ} (hN : 0 < N) :
    Matrix.trace (mpo K N) = 1 := by
  rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer]
  exact H.trace_physTraceTransfer_pow_eq_one hN

end NeighboringTraceFactorization

end MPOTensor.PhysicalSectorFactorization
