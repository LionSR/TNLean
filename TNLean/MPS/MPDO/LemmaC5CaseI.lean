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

The proof follows the refined route of issue #5404.

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

This is the matrix `S` of step 2 of the Lemma C.5 Case-I route (issue #5404).
Each entry is bounded above by `T_{kh}²` where `T` is the active-sector trace
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

/-- **Lemma C.5 Case I: singleton active-sector consequence.**

Let `K` be an MPO tensor whose doubled-index MPS tensor is normal
(`MPSTensor.IsNormalTensor K.toMPSTensor`).  Assume the literal
zero-correlation-length identity
`physTraceTransfer K * physTraceTransfer K = physTraceTransfer K`
with nonzero physical-trace transfer.  Let `F` be a physical-sector
factorization of `K` with positive neighboring operators and vanishing
zero-weight sectors.  Then the active sector set for the weight vector `p`
is a singleton.  Consequently `T² = T` and `Q(1−LQ)L = 0`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5 (`SALZCL`), lines
1473--1499. -/
theorem lemmaC5_caseI_singleton
    (hNT : MPSTensor.IsNormalTensor K.toMPSTensor)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hZCL_ne : physTraceTransfer K ≠ 0)
    (F : PhysicalSectorFactorization K)
    (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hspan : Submodule.span ℂ
      (Set.range (F.activeSectorOneSiteMatrixFamily p)) = ⊤)
    (hnonzero : ∀ k : F.ActiveSector p,
      ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0)
    (htriangle : ∀ {k h : F.ActiveSector p},
      F.neighboringOperator k h ≠ 0 →
        ∃ j : F.ActiveSector p,
          F.neighboringOperator h j ≠ 0 ∧
            F.neighboringOperator j k ≠ 0)
    [hne : Nonempty (F.ActiveSector p)] :
    Fintype.card (F.ActiveSector p) = 1 := by
  -- ====================================================================
  -- Step 1: From literal ZCL, T² = T³ (without scalar normalization)
  -- ====================================================================
  let T : Matrix (F.ActiveSector p) (F.ActiveSector p) ℝ :=
    F.activeSectorTraceMatrix p
  have hTsq_eq_Tcu : T ^ 2 = T ^ 3 :=
    activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL
      K F p hZCL_sq hinactive hpos
  -- ====================================================================
  -- Step 2: T is primitive (from Case-I spanning/nonzero/triangle)
  -- ====================================================================
  have hTprim : Matrix.IsPrimitive T :=
    F.activeSectorTraceMatrix_isPrimitive p hpos hspan hnonzero htriangle
  -- ====================================================================
  -- Step 3: Every entry of T² is positive
  -- ====================================================================
  have hTtwo_pos : ∀ i j : F.ActiveSector p, 0 < (T ^ 2) i j :=
    hTprim.pow_two_pos_of_pow_two_eq_pow_three hTsq_eq_Tcu

  -- ====================================================================
  -- Step 4: Construct Perron vector v and row-stochastic P = D_v⁻¹ T D_v
  -- ====================================================================
  obtain ⟨j₀⟩ := hne
  let v : F.ActiveSector p → ℝ := fun i ↦ (T ^ 2) i j₀
  have hv_pos : ∀ i, 0 < v i := fun i ↦ hTtwo_pos i j₀
  have h_T_mul_Tsq_eq_Tcu : T * (T ^ 2) = T ^ 3 := by
    calc
      T * (T ^ 2) = T * (T * T) := by rw [pow_two]
      _ = (T * T) * T := by rw [Matrix.mul_assoc]
      _ = T ^ 2 * T := by rw [pow_two]
      _ = T ^ 3 := by rw [← pow_succ]
  have hTv_eq_v : T.mulVec v = v := by
    ext i
    dsimp [v]
    rw [Matrix.mulVec_apply]
    calc
      (∑ j : F.ActiveSector p, T i j * (T ^ 2) j j₀)
          = (T * (T ^ 2)) i j₀ := by rw [Matrix.mul_apply]
      _ = (T ^ 3) i j₀ := by
        rw [show (T * (T ^ 2)) i j₀ = (T ^ 3) i j₀ from by rw [h_T_mul_Tsq_eq_Tcu]]
      _ = (T ^ 2) i j₀ := by
        rw [show (T ^ 3) i j₀ = (T ^ 2) i j₀ from by rw [hTsq_eq_Tcu]]
    -- ================================================================
    -- Step 5: Construct P = D_v^{-1} T D_v (row-stochastic and primitive)
  -- ================================================================
  -- Step 5: Construct P = D_v^{-1} T D_v and prove primitive row-stochastic
  -- ================================================================
  let P : Matrix (F.ActiveSector p) (F.ActiveSector p) ℝ :=
    fun i j ↦ T i j * v j / v i
  have hP_nonneg : ∀ i j, 0 ≤ P i j := by
    intro i j; dsimp [P]
    have hT_nonneg : 0 ≤ T i j := hTprim.nonneg i j
    have hvj_nonneg : 0 ≤ v j := le_of_lt (hv_pos j)
    have hvi_pos : 0 < v i := hv_pos i
    exact div_nonneg (mul_nonneg hT_nonneg hvj_nonneg) (le_of_lt hvi_pos)
  have hP_row_stoch : P ∈ Matrix.rowStochastic ℝ (F.ActiveSector p) := by
    rw [Matrix.mem_rowStochastic_iff_sum]
    refine ⟨hP_nonneg, fun i => ?_⟩
    dsimp [P]
    calc
      (∑ j : F.ActiveSector p, T i j * v j / v i) = ((∑ j : F.ActiveSector p, T i j * v j) / v i) := by
        rw [Finset.sum_div]
      _ = ((T.mulVec v) i / v i) := by
        rw [Matrix.mulVec_apply_eq_sum]
      _ = (v i / v i) := by rw [hTv_eq_v]
      _ = 1 := div_self (ne_of_gt (hv_pos i))
  have hP_prim : P.IsPrimitive := by
    obtain ⟨k, hk_pos, hk_all⟩ := hTprim.exists_pos_pow
    -- P = D_v^{-1} * T * D_v, hence P^k = D_v^{-1} * T^k * D_v
    -- Entrywise: P^k_{ij} = T^k_{ij} * v_j / v_i
    have hP_pow_entry (n : ℕ) (i j) : (P ^ n) i j = (T ^ n) i j * v j / v i := by
      induction n generalizing i j with
      | zero =>
        -- P^0 = 1, T^0 = 1: 1_{ij} = 1_{ij} * v_j / v_i
        simp [Matrix.one_apply, pow_zero]
        split_ifs with hij
        · subst hij
          field_simp [ne_of_gt (hv_pos i)]
        · simp
      | succ n ih =>
        rw [pow_succ, Matrix.mul_apply]
        rw [ih i l, P]
        -- Goal: Σ_l (T^n_{il} * v_l / v_i) * (T_{lj} * v_j / v_l) = T^{n+1}_{ij} * v_j / v_i
        -- Prove by direct calculation
        calc
          (∑ l : F.ActiveSector p, ((T ^ n) i l * v l / v i) * (T l j * v j / v l)) =
              (∑ l : F.ActiveSector p, ((T ^ n) i l * T l j) * (v j / v_i)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            have hvl_ne : v l ≠ 0 := (hv_pos l).ne'
            field_simp [hvl_ne]
            ring
          _ = (∑ l : F.ActiveSector p, (T ^ n) i l * T l j) * (v j / v_i) := by
            rw [Finset.sum_mul]
          _ = ((T ^ n * T) i j) * (v j / v_i) := by rw [Matrix.mul_apply]
          _ = (T ^ n * T) i j * v j / v_i := by ring
          _ = (T ^ (n + 1)) i j * v j / v_i := by rw [pow_succ]
    refine ⟨hP_nonneg, k, hk_pos, fun i j => ?_⟩
    rw [hP_pow_entry k i j]
    have hTk_pos : 0 < (T ^ k) i j := hk_all i j
    have hvj_pos : 0 < v j := hv_pos j
    have hvi_pos : 0 < v i := hv_pos i
    positivity

  -- ================================================================
  -- Step 6: S, Ŝ, bounds, trace similarity
  -- ================================================================
  let S : Matrix (F.ActiveSector p) (F.ActiveSector p) ℝ := activeSectorTraceSqMatrix K F p
  have hS_nonneg : ∀ i j, 0 ≤ S i j := activeSectorTraceSqMatrix_nonneg K F p hpos
  have hS_le_Tsq : ∀ i j, S i j ≤ (T i j) ^ 2 := by
    intro i j; simpa [S, T] using activeSectorTraceSqMatrix_le_activeSectorTraceMatrix_sq K F p hpos i j
  let Ŝ : Matrix (F.ActiveSector p) (F.ActiveSector p) ℝ := fun i j ↦ S i j * (v j ^ 2) / (v i ^ 2)
  have hŜ_nonneg : ∀ i j, 0 ≤ Ŝ i j := by
    intro i j; dsimp [Ŝ]
    exact div_nonneg (mul_nonneg (hS_nonneg i j) (sq_nonneg (v j))) (sq_nonneg (v i))
  have hŜ_le_Phadamard : ∀ i j, Ŝ i j ≤ (P ⊙ P) i j := by
    intro i j; dsimp [Ŝ, P, Matrix.hadamard]
    have hS_le : S i j ≤ (T i j) ^ 2 := hS_le_Tsq i j
    -- Target: S_ij * v_j² / v_i² ≤ (T_ij * v_j / v_i) * (T_ij * v_j / v_i)
    -- RHS = (T_ij * v_j / v_i)^2 = T_ij^2 * (v_j^2 / v_i^2)
    rw [← sq]
    have h_frac : (T i j * v j / v i) ^ 2 = (T i j) ^ 2 * (v j ^ 2 / v i ^ 2) := by ring
    rw [h_frac]
    have h_div_nonneg : 0 ≤ v j ^ 2 / v i ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    -- Need: S_ij * (v_j² / v_i²) ≤ (T_ij)² * (v_j² / v_i²)
    -- Since S_ij ≤ (T_ij)² and (v_j² / v_i²) ≥ 0, multiply both sides
    have h_ineq : S i j * (v j ^ 2 / v i ^ 2) ≤ (T i j) ^ 2 * (v j ^ 2 / v i ^ 2) :=
      mul_le_mul_of_nonneg_right hS_le h_div_nonneg
    -- Target: S_ij * v_j² / v_i² ≤ (T_ij)² * (v_j² / v_i²)
    -- Note: S_ij * v_j² / v_i² = S_ij * (v_j² / v_i²)
    -- So the target is exactly h_ineq
    simpa [div_eq_mul_inv, mul_assoc] using h_ineq
  have h_trace_sim (N : ℕ) : Matrix.trace (Ŝ ^ N) = Matrix.trace (S ^ N) := by
    have h_pow_entry (n : ℕ) (i j) : (Ŝ ^ n) i j = (S ^ n) i j * (v j ^ 2) / (v i ^ 2) := by
      induction n generalizing i j with
      | zero =>
        simp [Ŝ, Matrix.one_apply, pow_zero]
        split_ifs with hij
        · subst hij; field_simp [ne_of_gt (hv_pos i)]
        · simp
      | succ n ih =>
        rw [pow_succ, Matrix.mul_apply]
        dsimp [Ŝ]
        rw [ih i l]
        calc
          (∑ l : F.ActiveSector p, ((S ^ n) i l * (v l ^ 2) / (v i ^ 2)) * (S l j * (v j ^ 2) / (v l ^ 2))) =
              (∑ l : F.ActiveSector p, ((S ^ n) i l * S l j) * (v j ^ 2) / (v i ^ 2)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            have hvl_sq_pos : v l ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (hv_pos l))
            field_simp [hvl_sq_pos]
            ring
          _ = (∑ l : F.ActiveSector p, (S ^ n) i l * S l j) * (v j ^ 2) / (v i ^ 2) := by
            simp [Finset.sum_div, Finset.mul_sum]
          _ = ((S ^ n * S) i j) * (v j ^ 2) / (v i ^ 2) := by simp [Matrix.mul_apply]
          _ = (S ^ (n + 1)) i j * (v j ^ 2) / (v i ^ 2) := by rw [pow_succ]
    rw [Matrix.trace]; simp only [Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h_pow_entry N i i]
    have hvi_sq_pos : v i ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (hv_pos i))
    field_simp [hvi_sq_pos]
    ring
  -- ================================================================
  -- Step 7: Overlap formula (requires physical-isometry bridge, documented gap)
  -- ================================================================
  have h_overlap_formula (N : ℕ) [NeZero N] :
      MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N = (Matrix.trace (S ^ N) : ℂ) := by
    have hMPDO : IsMPDO K := F.isMPDO_of_neighboringOperator_pos hpos
    have hNpos : 0 < N := NeZero.pos N
    rw [mpvOverlap_toMPSTensor_self_eq_trace_sq K hMPDO hNpos]
    -- Remaining gap: tr(mpo(K,N)²) = (tr(S^N) : ℂ)
    -- Requires: unitary invariance under physicalIsometry, block-diagonal
    -- decomposition via reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal,
    -- trace_cyclicNeighboringProduct_sq_eq_prod_trace_sq, and the
    -- trace-cycle identity tr(S^N) = Σ_c Π_n S_{c_n,c_{n+1}}.
    sorry
  -- ================================================================
  -- Step 8: Cardinality contradiction
  -- ================================================================
  by_cases hcard_gt_one : 1 < Fintype.card (F.ActiveSector p)
  · haveI : Nontrivial (F.ActiveSector p) := Fintype.one_lt_card_iff_nontrivial.mp hcard_gt_one
    have h_tendsto_zero : Tendsto (fun N : ℕ ↦ Matrix.trace (Ŝ ^ N)) atTop (nhds (0 : ℝ)) :=
      Matrix.trace_pow_tendsto_zero_of_nonneg_le_hadamard_self
        hP_row_stoch hP_prim hŜ_nonneg hŜ_le_Phadamard
    have h_tendsto_zero' : Tendsto (fun N : ℕ ↦ Matrix.trace (S ^ N)) atTop (nhds (0 : ℝ)) :=
      h_tendsto_zero.congr h_trace_sim
    have h_self_one : Tendsto (fun N : ℕ ↦ MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N)
        atTop (nhds (1 : ℂ)) := hNT.selfOverlap_tendsto_one
    have h_tendsto_one : Tendsto (fun N : ℕ ↦ Matrix.trace (S ^ N)) atTop (nhds (1 : ℝ)) := by
      have h_self_one_re : Tendsto (fun N : ℕ ↦ (MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N).re)
          atTop (nhds (1 : ℝ)) := by
        simpa [Complex.one_re] using h_self_one.re
      have h_eventually_pos : ∀ᶠ (N : ℕ) in atTop, 0 < N := by
        refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
        omega
      refine h_self_one_re.congr ?_
      filter_upwards [h_eventually_pos] with n hn
      haveI : NeZero n := ⟨hn.ne'⟩
      rw [h_overlap_formula n, Complex.ofReal_re]
    have h_contra : (0 : ℝ) = 1 := tendsto_nhds_unique h_tendsto_zero' h_tendsto_one
    linarith
  · have hpos_card : 0 < Fintype.card (F.ActiveSector p) :=
      Fintype.card_pos_iff.mpr ⟨by infer_instance⟩
    omega

end caseI

end MPOTensor
