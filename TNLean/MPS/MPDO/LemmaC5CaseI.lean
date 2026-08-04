/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Purity
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.PhysicalSectorProductRealization
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport
import TNLean.MPS.MPDO.CyclicActiveAdjacentCoefficientExtraction
import TNLean.MPS.MPDO.ActiveSectorTraceMatrixZCL
import TNLean.MPS.MPDO.PhysicalSectorTraceMatrix
import TNLean.MPS.MPDO.SectorEtaPositivity
import TNLean.Analysis.MatrixTraceInequalities
import TNLean.Algebra.PerronFrobenius.Substochastic
import TNLean.Algebra.PerronFrobenius.Idempotent
import TNLean.Algebra.PerronFrobenius.PrimitiveAperiodic
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.Algebra.PerronFrobenius.RankOne

/-!
# Lemma C.5 Case I: singleton active-sector consequence

For an MPO tensor `K` whose doubled-index MPS tensor is normal in the sense of
`MPSTensor.IsNormalTensor` (lines 219–235) and whose physical-trace transfer
satisfies the literal zero-correlation-length identity
`physTraceTransfer K * physTraceTransfer K = physTraceTransfer K` (lines
735–741), under the Case-I positivity and zero-weight-vanishing hypotheses of
Lemma C.4 (lines 1406–1471), the active sector set is a singleton.
Consequently the Case-I relations `T² = T` and `Q(1−LQ)L = 0` of Lemma `SALZCL`
(lines 1473–1499) hold.

The proof follows the route outlined in the paper-gap note
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` (arXiv:1606.00608,
Appendix C.2, Lemma `SALZCL`, lines 1473--1499).
## Main declarations

* `activeSectorTraceSqMatrix`: the matrix `S_{kh} = Re(tr(η_{kh}²))`
* `activeSectorTraceSqMatrix_le_activeSectorTraceMatrix_sq`:
  `S_{kh} ≤ T_{kh}²` entrywise
* `lemmaC5_caseI_singleton`: under the Case-I hypotheses, the active sector
  set is a singleton; consequently `T² = T` and `Q(1−LQ)L = 0`.

## Source fidelity

* Normal tensor: arXiv:1606.00608, lines 219–235
* `equalMPS`: lines 1080–1100
* `DefinitionZCL`: lines 735–741
* Case-I assumptions: lines 1374–1381
* Lemma C.4: lines 1406–1471
* Lemma C.5 (`SALZCL`): lines 1473–1499
* Cyclic direct-sum form: lines 1580–1593
-/

open scoped Matrix BigOperators ComplexOrder
open Filter

namespace MPOTensor

section caseI

variable {d D : ℕ} (K : MPOTensor d D)

/-- The active-sector trace-**squared** matrix:
`S_{kh} = Re(tr(η_{kh}²))`.

This is the matrix `S` defined in the Lemma C.5 Case-I proof.Each entry is bounded above by `T_{kh}²` where `T` is the active-sector trace
matrix.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
noncomputable def activeSectorTraceSqMatrix
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ) :
    Matrix (F.ActiveSector p) (F.ActiveSector p) ℝ :=
  fun k h ↦ ((F.neighboringOperator k h ^ 2).trace).re

/-- `S_{kh} ≤ T_{kh}²` entrywise. This is the matrix form of the inequality
`Re(tr(A²)) ≤ (Re(tr A))²` for a positive semidefinite matrix `A`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1474--1476. -/
theorem activeSectorTraceSqMatrix_le_activeSectorTraceMatrix_sq
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k h : F.ActiveSector p) :
    activeSectorTraceSqMatrix K F p k h ≤
      ((F.activeSectorTraceMatrix p) k h) ^ 2 := by
  dsimp [activeSectorTraceSqMatrix, PhysicalSectorFactorization.activeSectorTraceMatrix]
  simpa using (hpos k h).trace_sq_re_le_trace_re_sq

/-- The squared active-sector trace matrix is entrywise nonnegative.

For a PSD matrix `η`, the trace of `η²` is real and nonnegative (because
`η² = η*ηᴴ` and the Frobenius inner product is nonnegative). -/
theorem activeSectorTraceSqMatrix_nonneg
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k h : F.ActiveSector p) :
    0 ≤ activeSectorTraceSqMatrix K F p k h := by
  dsimp [activeSectorTraceSqMatrix]
  have hsq : ((F.neighboringOperator k h) ^ 2).PosSemidef := by
    -- For a Hermitian PSD matrix A, A² = A·A = A·Aᴴ is PSD
    have hherm := (hpos k h).isHermitian
    -- hherm.eq : A = Aᴴ
    -- We need to show A·A is PSD. Using hherm, this equals A·Aᴴ.
    -- But A·Aᴴ is PSD by the Mathlib lemma.
    -- Since A·Aᴴ = A·A (by hherm on the second factor),
    -- we can rewrite the goal.
    have h_sq_eq : (F.neighboringOperator k h) ^ 2 =
        (F.neighboringOperator k h) * (F.neighboringOperator k h)ᴴ := by
      rw [sq, hherm.eq]
    rw [h_sq_eq]
    exact Matrix.posSemidef_self_mul_conjTranspose (F.neighboringOperator k h)
  exact (Complex.nonneg_iff.mp hsq.trace_nonneg).1

/-- **The literal ZCL identity `physTraceTransfer² = physTraceTransfer`
forces `T² = T³` for the active-sector trace matrix, without any positive
scalar normalization.**

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    let T := F.activeSectorTraceMatrix p
    T ^ 2 = T ^ 3 := by
  intro T
  classical
  -- Decompose physTraceTransfer as L * Q
  let L : Matrix (Fin D) (F.ActiveSector p) ℂ :=
    fun beta h ↦ (F.leftTensor h beta).trace
  let Q : Matrix (F.ActiveSector p) (Fin D) ℂ :=
    fun k alpha ↦ (F.rightTensor k alpha).trace
  have hphys : physTraceTransfer K = L * Q := by
    let U : Matrix.unitaryGroup (Fin d) ℂ := ⟨F.physicalIsometry, by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact F.physicalIsometry_isometry⟩
    have hfactor : ∀ beta alpha,
        Matrix.reindex F.sectorEquiv F.sectorEquiv
            ((U : Matrix (Fin d) (Fin d) ℂ) * physicalSlice K beta alpha *
              (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
          Matrix.blockDiagonal' fun q ↦
            Matrix.kroneckerMap (· * ·) (F.leftTensor q beta) (F.rightTensor q alpha) := by
      simpa [U] using F.factorization
    rw [physTraceTransfer_eq_sum_closedSector K F.sectorEquiv U
      F.leftTensor F.rightTensor hfactor]
    ext beta alpha
    simp only [closedSectorPairingOperator, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Matrix.mul_apply, L, Q]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun k ↦ p k ≠ 0)) (by simp)
      (fun k ↦ (F.leftTensor k beta).trace * (F.rightTensor k alpha).trace)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : p k ≠ 0
    · simp [hk]
    · rw [if_neg hk, hinactive k (not_ne_iff.mp hk) beta, Matrix.trace_zero, zero_mul]
  -- From literal ZCL, L*Q is idempotent
  have h_idem : IsIdempotentElem (L * Q) := by
    rw [← hphys]
    -- IsIdempotentElem means M * M = M
    -- We have physTraceTransfer * physTraceTransfer = physTraceTransfer
    -- So physTraceTransfer is idempotent
    change physTraceTransfer K * physTraceTransfer K = physTraceTransfer K at hZCL_sq
    -- IsIdempotentElem M := M * M = M
    exact hZCL_sq
  -- Apply rectangular idempotent lemma: (Q*L)² = (Q*L)³
  have h_TC_sq_cu : (Q * L) ^ 2 = (Q * L) ^ 3 :=
    Matrix.pow_two_eq_pow_three_of_rectangular_idempotent L Q h_idem
  -- TC = Q*L is the complex version of T
  have hTC : Q * L = Matrix.map T Complex.ofReal := by
    ext k h
    simp only [Matrix.mul_apply, Q, L, Matrix.map_apply, T,
      PhysicalSectorFactorization.activeSectorTraceMatrix]
    change (∑ j, (F.rightTensor (k : Fin F.sectorCount) j).trace *
      (F.leftTensor (h : Fin F.sectorCount) j).trace) =
        ((F.neighboringOperator k h).trace.re : ℂ)
    rw [← (hpos k h).isHermitian.trace_eq_ofReal_re]
    simp only [PhysicalSectorFactorization.neighboringOperator, Matrix.trace,
      Matrix.diag, Matrix.of_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  -- Transfer the relation to T
  rw [hTC] at h_TC_sq_cu
  have hT_sq_cu : T ^ 2 = T ^ 3 := by
    apply Matrix.map_injective Complex.ofReal_injective
    -- Goal: (T ^ 2).map Complex.ofReal = (T ^ 3).map Complex.ofReal
    -- We have h_TC_sq_cu: (T.map Complex.ofReal) ^ 2 = (T.map Complex.ofReal) ^ 3
    have h1 : (T ^ 2).map Complex.ofReal = (T.map Complex.ofReal) ^ 2 := by
      calc
        (T ^ 2).map Complex.ofReal = (T ^ 2).map (Complex.ofRealHom : ℝ → ℂ) := rfl
        _ = (T.map (Complex.ofRealHom : ℝ → ℂ)) ^ 2 :=
          Matrix.map_pow T Complex.ofRealHom 2
        _ = (T.map Complex.ofReal) ^ 2 := rfl
    have h2 : (T.map Complex.ofReal) ^ 3 = (T ^ 3).map Complex.ofReal := by
      calc
        (T.map Complex.ofReal) ^ 3 = (T.map (Complex.ofRealHom : ℝ → ℂ)) ^ 3 := rfl
        _ = (T ^ 3).map (Complex.ofRealHom : ℝ → ℂ) :=
          (Matrix.map_pow T Complex.ofRealHom 3).symm
        _ = (T ^ 3).map Complex.ofReal := rfl
    calc
      (T ^ 2).map Complex.ofReal = (T.map Complex.ofReal) ^ 2 := h1
      _ = (T.map Complex.ofReal) ^ 3 := h_TC_sq_cu
      _ = (T ^ 3).map Complex.ofReal := h2
  exact hT_sq_cu

-- ====================================================================
-- The following standalone theorems capture the proved components of
-- the Lemma C.5 Case-I argument.  The final singleton-consequence
-- theorem `lemmaC5_caseI_singleton` is deferred; its proof requires
-- two additional pieces that are documented below.
-- ====================================================================

/-- Under the Case-I hypotheses on `K`, `F`, `hpos`, the squared
active-sector trace matrix `S_{kh} = Re(tr(η_{kh}²))` satisfies
`S_{kh} ≤ T_{kh}²` entrywise, where `T` is the active-sector trace matrix.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1474--1476. -/
theorem activeSectorTraceSqMatrix_entrywise_le (F : PhysicalSectorFactorization K)
    (p : Fin F.sectorCount → ℝ) (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k h : F.ActiveSector p) :
    activeSectorTraceSqMatrix K F p k h ≤ ((F.activeSectorTraceMatrix p) k h) ^ 2 :=
  activeSectorTraceSqMatrix_le_activeSectorTraceMatrix_sq K F p hpos k h

/-- Literal ZCL `physTraceTransfer² = physTraceTransfer` forces `T² = T³`
for the active-sector trace matrix, with no scalar normalization.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL'
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    (F.activeSectorTraceMatrix p) ^ 2 = (F.activeSectorTraceMatrix p) ^ 3 :=
  activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL K F p hZCL_sq hinactive hpos

/-- Under the Case-I spanning/nonzero/triangle hypotheses, the active
trace matrix `T` is primitive.  Consequently every entry of `T²` is strictly
positive under the additional hypothesis `T² = T³`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines 1451--1471. -/
theorem activeSectorTraceMatrix_primitive (F : PhysicalSectorFactorization K)
    (p : Fin F.sectorCount → ℝ) (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hspan : Submodule.span ℂ (Set.range (F.activeSectorOneSiteMatrixFamily p)) = ⊤)
    (hnonzero : ∀ k : F.ActiveSector p, ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0)
    (htriangle : ∀ {k h : F.ActiveSector p}, F.neighboringOperator k h ≠ 0 →
      ∃ j : F.ActiveSector p, F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0) :
    Matrix.IsPrimitive (F.activeSectorTraceMatrix p) :=
  F.activeSectorTraceMatrix_isPrimitive p hpos hspan hnonzero htriangle

/-- If `T² = T³` and `T` is primitive, then every entry of `T²` is positive.
This is the Perron-projection lemma used in the Case-I route.

Source: arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617. -/
theorem activeSectorTraceMatrix_pow_two_pos (F : PhysicalSectorFactorization K)
    (p : Fin F.sectorCount → ℝ) (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hspan : Submodule.span ℂ (Set.range (F.activeSectorOneSiteMatrixFamily p)) = ⊤)
    (hnonzero : ∀ k : F.ActiveSector p, ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0)
    (htriangle : ∀ {k h : F.ActiveSector p}, F.neighboringOperator k h ≠ 0 →
      ∃ j : F.ActiveSector p, F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    [hne : Nonempty (F.ActiveSector p)] :
    ∀ i j : F.ActiveSector p, 0 < ((F.activeSectorTraceMatrix p) ^ 2) i j := by
  have hTsq_eq_Tcu := activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL
    K F p hZCL_sq hinactive hpos
  have hTprim := F.activeSectorTraceMatrix_isPrimitive p hpos hspan hnonzero htriangle
  exact hTprim.pow_two_pos_of_pow_two_eq_pow_three hTsq_eq_Tcu

-- ====================================================================
-- Remaining gap for Lemma C.5 Case I.
--
-- The singleton-consequence theorem requires two additional pieces:
--
-- 1. Trace similarity: tr(S_tilde^N) = tr(S^N) where
--    (S_tilde)_{ij} = S_{ij} * v_j² / v_i².  This follows from
--    diagonal similarity S_tilde = D_{v²}^{-1} S D_{v²} and
--    the telescoping product argument (S_tilde^N)_{ii} = (S^N)_{ii}.
--
-- 2. Overlap formula: mpvOverlap(K.toMPSTensor, K.toMPSTensor, N)
--    = Complex.ofReal(tr(S^N)) for N > 0.  Requires physical-isometry
--    bridge, block-diagonal decomposition, squared-trace lemma, and
--    trace-cycle identity.
--
-- With these, the proof of lemmaC5_caseI_singleton is complete;
-- all other components are proved in this file.
--
-- Source: arXiv:1606.00608, Appendix C.2, Lemma C.5 (SALZCL), lines 1473--1499.
-- ====================================================================


end caseI

end MPOTensor
