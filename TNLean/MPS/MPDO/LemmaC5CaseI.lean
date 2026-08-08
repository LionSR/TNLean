/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.PhysicalSectorProductRealization
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport
import TNLean.MPS.MPDO.CyclicActiveAdjacentCoefficientExtraction
import TNLean.MPS.MPDO.ActiveSectorTraceMatrixZCL
import TNLean.MPS.MPDO.PhysicalSectorTraceMatrix
import TNLean.MPS.MPDO.Purity
import TNLean.MPS.MPDO.CyclicActiveTraceProductIdentities
import TNLean.MPS.MPDO.SectorEtaPositivity
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.Analysis.MatrixTraceInequalities
import TNLean.Algebra.PerronFrobenius.Idempotent
import TNLean.Algebra.PerronFrobenius.PerronVector
import TNLean.Algebra.PerronFrobenius.PrimitiveAperiodic
import TNLean.Algebra.PerronFrobenius.RankOne
import TNLean.Algebra.PerronFrobenius.Substochastic
import TNLean.Algebra.TraceReindex

/-!
# Lemma C.5 Case I: active-sector trace matrix components

This file provides the matrix-algebra components of the Case-I argument in
the proof of Lemma `SALZCL` (arXiv:1606.00608, Appendix C.2, lines
1473–1499), which states that a zero-correlation-length (ZCL) source yields
a structured active-level (SAL) decomposition for simple MPO tensors.  The
Case-I content carried here is the C.4–C.5 argument that the active-sector
trace matrix `T` satisfies `T² = T³`, is primitive, and every entry of `T²`
is positive.

The Case-I argument that the active sector set reduces to a singleton
(`card(ActiveSector p) = 1`), from which the Case-I relation `T² = T`
follows, is now proved.  These are the Case-I input to the proof of Lemma
`SALZCL` (arXiv:1606.00608, Appendix C.2, lines 1473--1499), not the
lemma's headline statement.

* trace similarity `tr(S_hat^N) = tr(S^N)` under diagonal scaling
  (`trace_pow_similarity_diagonal`),
* the overlap formula `mpvOverlap = Complex.ofReal(tr(S^N))`
  (`mpvOverlap_toMPSTensor_self_eq_ofReal_trace_activeSectorTraceSqMatrix_pow`),
* the active sector is unique
  (`card_activeSector_eq_one_of_literal_ZCL`),
* the Case-I relation `T² = T`
  (`activeSectorTraceMatrix_pow_two_eq_of_literal_ZCL`).

The overlap formula combines the doubled-index self-overlap identity
(`Purity`) with the physical-sector product realization
(`PhysicalSectorProductRealization`) via a physical basis change with
`Uᴴ * U = 1` (`trace_mpo_conjugatePhysical_mul_self`), the cyclic trace factorization
(`CyclicActiveTraceProductIdentities`), the reduction from the full sector
index to the active sector (`sum_prod_traceSq_eq_sum_active`), and the
cyclic-product expansion of `tr(S^N)` (`trace_pow_eq_sum_cyclic_product`).

The singleton-sector argument is a proof by contradiction (the source-faithful
route recorded in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`): the overlap formula and normality
(`MPSTensor.IsNormalTensor.selfOverlap_tendsto_one`, the `equalMPS`
self-overlap limit) give `tr(S^N) → 1`; conjugating the primitive `T` by
its Perron vector (`TNLean/Algebra/PerronFrobenius/PerronVector.lean`)
to a stochastic matrix `P` bounds `S`, after the matching squared
conjugation, entrywise by `P ⊙ P`; if more than one sector were active,
`P` would be irreducible substochastic on a nontrivial index set, forcing
`tr(S^N) → 0` (`Matrix.trace_pow_tendsto_zero_of_nonneg_le_hadamard_self`),
a contradiction.

The rectangular Case-I relation `Q(1−LQ)L = 0` is proved as the
project-derived rectangular form of `T² = T`, using the same factors
`T = QL` as in the proof of
`activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL`.  The factors
come from the tensors $l_h$ and $r_k$ of CPSV16, Appendix C.2, Lemma C.5,
lines 1473--1499; `L` and `Q` are project notation, and the paper does not
print the rectangular identity as a separate displayed theorem.

## Main declarations

* `activeSectorTraceSqMatrix`: the matrix `S_{kh} = Re(tr(η_{kh}²))`
* `activeSectorTraceSqMatrix_le_activeSectorTraceMatrix_sq`:
  `S_{kh} ≤ T_{kh}²` entrywise
* `activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL`:
  literal ZCL `physTraceTransfer² = physTraceTransfer` forces `T² = T³`
* `activeSectorTraceMatrix_pow_two_pos`:
  every entry of `T²` is strictly positive (derived from
  `activeSectorTraceMatrix_isPrimitive` in `PhysicalSectorTraceMatrix`)
* `pow_apply_eq_sum_path_indicator`: a matrix power's `(a, b)` entry as a
  sum over indicator-weighted length-`N` walks from `a` to `b`
* `trace_pow_eq_sum_cyclic_product`: `tr(S^N)` as a sum over cyclic
  products indexed by labelings `k : Fin N → n`
* `sum_prod_traceSq_eq_sum_active`: the full-sector cyclic-product sum
  reduces to the active-sector sum
* `mpvOverlap_toMPSTensor_self_eq_ofReal_trace_activeSectorTraceSqMatrix_pow`:
  **the overlap formula** `mpvOverlap = Complex.ofReal(tr(S^N))`
* `card_activeSector_eq_one_of_literal_ZCL`:
  **the active sector is unique**
* `activeSectorTraceMatrix_pow_two_eq_of_literal_ZCL`:
  **the Case-I relation** `T² = T`
* `caseI_rectangular_remainder_eq_zero_of_literal_ZCL`:
  **the rectangular Case-I relation** `Q(1−LQ)L = 0`

## Source fidelity

* Lemma C.4 (`propSN`): arXiv:1606.00608, Appendix C.2, lines 1406–1471
* Lemma C.5 (`SALZCL`): lines 1473–1499
* Cyclic direct-sum form: lines 1580–1593
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

section caseI

variable {d D : ℕ} (K : MPOTensor d D)

/-- The active-sector trace-**squared** matrix:
`S_{kh} = Re(tr(η_{kh}²))`.

This is the matrix `S` defined in the Lemma C.5 Case-I proof.
Each entry is bounded above by `T_{kh}²`, where `T` is the
active-sector trace matrix.

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

/-- The product of the theorem-local Case-I trace factors is the complexification of
`activeSectorTraceMatrix`.  In the project's rectangular notation this is `QL = T`,
built from the tensors $l_h$ and $r_k$ of CPSV16, Appendix C.2, Lemma C.5,
lines 1473--1499. -/
private theorem trace_rightTensor_mul_trace_leftTensor_eq_map_activeSectorTraceMatrix
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    let Q : Matrix (F.ActiveSector p) (Fin D) ℂ :=
      fun k alpha ↦ (F.rightTensor k alpha).trace
    let L : Matrix (Fin D) (F.ActiveSector p) ℂ :=
      fun beta h ↦ (F.leftTensor h beta).trace
    Q * L = Matrix.map (F.activeSectorTraceMatrix p) Complex.ofReal := by
  dsimp only
  ext k h
  simp only [Matrix.mul_apply, Matrix.map_apply,
    PhysicalSectorFactorization.activeSectorTraceMatrix]
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
    exact hZCL_sq
  -- Apply rectangular idempotent lemma: (Q*L)² = (Q*L)³
  have h_TC_sq_cu : (Q * L) ^ 2 = (Q * L) ^ 3 :=
    Matrix.pow_two_eq_pow_three_of_rectangular_idempotent L Q h_idem
  -- TC = Q*L is the complex version of T
  have hTC : Q * L = Matrix.map T Complex.ofReal := by
    simpa only [Q, L, T] using
      trace_rightTensor_mul_trace_leftTensor_eq_map_activeSectorTraceMatrix K F p hpos
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

/-! ## Proved components

The following theorems capture the proved matrix-algebra components of the
Lemma C.5 Case-I argument.  The final singleton-consequence theorem
`lemmaC5_caseI_singleton` is deferred (see the remaining-gap section
below for the two missing pieces).
-/


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

/-! ## Lemma C.5 Case I — remaining theorems

The matrix-algebra components above give `S ≤ T²` entrywise, `T² = T³` from
literal ZCL, primitivity of `T`, and `T² > 0` entrywise.  Four further
theorems complete the Case-I argument:

1. **Trace similarity** `tr(S_hat ^ N) = tr(S^N)` where `S_hat` is the diagonal
   similarity transform of `S` by the squared Perron weights.
2. **Overlap formula** `mpvOverlap = Complex.ofReal(tr(S^N))` expressing
   the doubled-index self-overlap in terms of the active-sector
   trace-squared matrix.
3. **Singleton assembly** Prove `card(ActiveSector p) = 1`, which forces
   `T² = T`.
4. **Rectangular form** Rewrite `T² = T` through `T = QL` as
   `Q(1−LQ)L = 0`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5 (`SALZCL`), lines
1473--1499; Case-I assumptions at lines 1374--1381; self-overlap limit at
lines 1080--1100.
-/

open Matrix

section traceSimilarity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace similarity under diagonal conjugation.** For any real square matrix
`S` and a diagonal matrix with nonzero entries, the trace of every power is
preserved under the diagonal similarity `M = D⁻¹ * S * D`:
`tr(M^N) = tr(S^N)` for all `N ≥ 0`.

This is the telescoping used in the Lemma C.5 Case-I route
(arXiv:1606.00608, Appendix C.2, lines 1473--1499): conjugate `S` by the
squared Perron-weight diagonal matrix `D_{v²}`, and the trace of every power
is unchanged.

The proof expands `(D⁻¹·S·D)^N = D⁻¹·S^N·D` by the diagonal similarity
telescoping, then applies trace cyclicity `tr(D⁻¹·T·D) = tr(T)`. -/
theorem trace_pow_similarity_diagonal (S : Matrix n n ℝ) (d : n → ℝ) (hd : ∀ i, d i ≠ 0)
    (N : ℕ) :
    Matrix.trace (((Matrix.diagonal d)⁻¹ * S * Matrix.diagonal d) ^ N) =
      Matrix.trace (S ^ N) := by
  have h_det : IsUnit ((Matrix.diagonal d).det) := by
    rw [Matrix.det_diagonal]
    exact (IsUnit.prod_univ_iff.mpr fun i => (hd i).isUnit)
  have h_mul : (Matrix.diagonal d)⁻¹ * (Matrix.diagonal d) = 1 :=
    Matrix.nonsing_inv_mul (Matrix.diagonal d) h_det
  have h_mul' : (Matrix.diagonal d) * (Matrix.diagonal d)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (Matrix.diagonal d) h_det
  have h_pow : ((Matrix.diagonal d)⁻¹ * S * Matrix.diagonal d) ^ N =
      (Matrix.diagonal d)⁻¹ * (S ^ N) * Matrix.diagonal d := by
    induction' N with k ih
    · simp [h_mul]
    · rw [pow_succ, pow_succ, ih]
      calc
        ((Matrix.diagonal d)⁻¹ * (S ^ k) * Matrix.diagonal d) *
            ((Matrix.diagonal d)⁻¹ * S * Matrix.diagonal d) =
          (Matrix.diagonal d)⁻¹ * (S ^ k) *
            (Matrix.diagonal d * (Matrix.diagonal d)⁻¹) * S * Matrix.diagonal d := by
          simp [Matrix.mul_assoc]
        _ = (Matrix.diagonal d)⁻¹ * (S ^ k) * 1 * S * Matrix.diagonal d := by
          rw [h_mul']
        _ = (Matrix.diagonal d)⁻¹ * (S ^ (k + 1)) * Matrix.diagonal d := by
          simp [pow_succ, Matrix.mul_assoc]
  calc
    Matrix.trace (((Matrix.diagonal d)⁻¹ * S * Matrix.diagonal d) ^ N) =
        Matrix.trace ((Matrix.diagonal d)⁻¹ * (S ^ N) * Matrix.diagonal d) := by
      rw [h_pow]
    _ = Matrix.trace ((Matrix.diagonal d) * ((Matrix.diagonal d)⁻¹ * (S ^ N))) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (((Matrix.diagonal d) * (Matrix.diagonal d)⁻¹) * (S ^ N)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (1 * (S ^ N)) := by rw [h_mul']
    _ = Matrix.trace (S ^ N) := by simp

/-- `trace_pow_similarity_diagonal` specialized to the squared Perron-weight
diagonal used in the Lemma C.5 Case-I route.  For a positive vector `v`
(e.g. the right Perron vector of the active-sector trace matrix `T`), set
`S_hat = D_{v²}⁻¹ * S * D_{v²}`.  Then `tr(S_hat ^ N) = tr(S^N)` for all `N`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem trace_pow_similarity_squared_diagonal (S : Matrix n n ℝ) (v : n → ℝ) (hv : ∀ i, 0 < v i)
    (N : ℕ) :
    Matrix.trace (((Matrix.diagonal fun i => (v i)^2)⁻¹ * S *
        Matrix.diagonal fun i => (v i)^2) ^ N) =
      Matrix.trace (S ^ N) :=
  trace_pow_similarity_diagonal S (fun i => (v i)^2) (fun i => pow_ne_zero 2 (hv i).ne') N

end traceSimilarity

section cyclicTrace

/-! These two lemmas are generic `CommSemiring`-valued matrix combinatorics with no
dependency on the MPDO/MPO development; they stay in this file, rather than moving to
`TNLean.Algebra`, because this Case-I route is their only call site so far. -/

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommSemiring R]

/-- **Indicator-path expansion of a matrix power.** The `(a, b)` entry of `S ^ N` is the sum,
over length-`N` walks `v : Fin (N + 1) → n` from `a` to `b`, of the product of the matrix
entries along the walk.

This is the elementary combinatorial expansion of matrix powers used to derive the
cyclic-product form of `tr(S^N)` in the Lemma C.5 Case-I route.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem pow_apply_eq_sum_path_indicator (S : Matrix n n R) :
    ∀ (N : ℕ) (a b : n), (S ^ N) a b =
      ∑ v : Fin (N + 1) → n, if v 0 = a ∧ v (Fin.last N) = b
        then ∏ i : Fin N, S (v i.castSucc) (v i.succ) else 0 := by
  intro N
  induction N with
  | zero =>
    intro a b
    rw [pow_zero, Matrix.one_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) n)
      (fun v : Fin 1 → n => if v 0 = a ∧ v (Fin.last 0) = b then
        (∏ i : Fin 0, S (v i.castSucc) (v i.succ) : R) else 0)
      (fun c : n => if c = a ∧ c = b then (1 : R) else 0)
      (fun v => by simp [Equiv.funUnique_apply])]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : ∀ c : n, ¬(c = a ∧ c = b) := fun c ⟨h1, h2⟩ => hab (h1.symm.trans h2)
      simp [hab, hne]
  | succ N ih =>
    intro a b
    have hprod : ∀ (v : Fin (N + 1) → n) (x : n),
        ∏ i : Fin (N + 1), S ((Fin.snoc v x : Fin (N + 2) → n) i.castSucc)
            ((Fin.snoc v x : Fin (N + 2) → n) i.succ) =
          (∏ i : Fin N, S (v i.castSucc) (v i.succ)) * S (v (Fin.last N)) x := by
      intro v x
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        have h1 : (Fin.snoc v x : Fin (N + 2) → n) (i.castSucc).castSucc = v i.castSucc := by
          rw [Fin.snoc_castSucc]
        have h2 : (Fin.snoc v x : Fin (N + 2) → n) (i.castSucc).succ = v i.succ := by
          rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
        rw [h1, h2]
      · have h1 : (Fin.snoc v x : Fin (N + 2) → n) (Fin.last N).castSucc = v (Fin.last N) := by
          rw [Fin.snoc_castSucc]
        have h2 : (Fin.snoc v x : Fin (N + 2) → n) (Fin.last N).succ = x := by
          rw [Fin.succ_last, Fin.snoc_last]
        rw [h1, h2]
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (v : Fin (N + 1) → n) (c : n),
        (if v 0 = a ∧ v (Fin.last N) = c then
          (∏ i : Fin N, S (v i.castSucc) (v i.succ)) * S c b else 0) =
        (if v 0 = a then (if v (Fin.last N) = c then
          (∏ i : Fin N, S (v i.castSucc) (v i.succ)) * S c b else 0) else 0) from
      fun v c => by by_cases h : v 0 = a <;> simp [h]]
    conv_lhs => simp only [Fintype.sum_ite_eq]
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (N + 2) => n))]
    rw [Fintype.sum_prod_type]
    conv_rhs =>
      simp only [Fin.snocEquiv_apply]
      simp only [hprod]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [Finset.sum_comm]
    congr 1
    ext v
    by_cases hv0 : v 0 = a
    · simp [hv0]
    · simp [hv0]

/-- **Trace of a matrix power as a sum over cyclic products.** `tr(S^N)` is the sum, over all
labelings `k : Fin N → n` of the `N` cyclic positions, of the product of matrix entries
`S (k i) (k (i + 1))` along the cycle (indices mod `N`).

This is the cyclic-product identity used in the Lemma C.5 Case-I route to express the
doubled-index self-overlap `mpvOverlap(K.toMPSTensor, K.toMPSTensor, N)` in terms of
`tr(S^N)`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem trace_pow_eq_sum_cyclic_product (S : Matrix n n R) {N : ℕ} [NeZero N] :
    Matrix.trace (S ^ N) = ∑ k : Fin N → n, ∏ i : Fin N, S (k i) (k (i + 1)) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have htrace : Matrix.trace (S ^ (M + 1)) = ∑ a : n, (S ^ (M + 1)) a a := by
    simp [Matrix.trace, Matrix.diag]
  rw [htrace]
  simp_rw [pow_apply_eq_sum_path_indicator S (M + 1)]
  rw [Finset.sum_comm]
  have hcollapseA : ∀ v : Fin (M + 2) → n,
      (∑ a : n, if v 0 = a ∧ v (Fin.last (M + 1)) = a then
        (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else 0) =
      if v 0 = v (Fin.last (M + 1)) then
        (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else 0 := by
    intro v
    by_cases h : v 0 = v (Fin.last (M + 1))
    · rw [if_pos h]
      have hswap : (fun a => if v 0 = a ∧ v (Fin.last (M + 1)) = a then
          (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else (0 : R)) =
        (fun a => if v 0 = a then (if v (Fin.last (M + 1)) = a then
          (∏ i : Fin (M + 1), S (v i.castSucc) (v i.succ)) else 0) else 0) :=
        funext (fun a => by by_cases ha : v 0 = a <;> simp [ha])
      rw [hswap]
      simp [h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      rintro ⟨ha1, ha2⟩
      exact h (ha1.trans ha2.symm)
  simp_rw [hcollapseA]
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun v : Fin (M + 2) → n => Fin.init v)
    (fun k : Fin (M + 1) → n => Fin.snoc k (k 0))
  · intro v _
    exact Finset.mem_univ _
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (Fin.snoc k (k 0) : Fin (M + 2) → n) 0 =
      (Fin.snoc k (k 0) : Fin (M + 2) → n) (Fin.last (M + 1))
    rw [Fin.snoc_last]
    have hz : (0 : Fin (M + 2)) = (Fin.castSucc (0 : Fin (M + 1))) := (Fin.castSucc_zero).symm
    rw [hz, Fin.snoc_castSucc]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    change (Fin.snoc (Fin.init v) ((Fin.init v) 0) : Fin (M + 2) → n) = v
    rw [show (Fin.init v) 0 = v (Fin.last (M + 1)) from by
      change v ((0 : Fin (M + 1)).castSucc) = v (Fin.last (M + 1))
      rw [Fin.castSucc_zero]
      exact hv]
    exact Fin.snoc_init_self v
  · intro k _
    funext i
    change (Fin.snoc k (k 0) : Fin (M + 2) → n) i.castSucc = k i
    simp only [Fin.snoc_castSucc]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    apply Finset.prod_congr rfl
    intro i _
    have hi1 : v i.castSucc = (Fin.init v) i := rfl
    have hi2 : (Fin.init v) (i + 1) = v (i + 1).castSucc := rfl
    rw [hi1, hi2]
    congr 1
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, Fin.last_add_one]
      have hz : (Fin.castSucc (0 : Fin (M + 1)) : Fin (M + 2)) = (0 : Fin (M + 2)) :=
        Fin.castSucc_zero
      rw [hz]
      exact hv.symm
    | cast j =>
      rw [Fin.coeSucc_eq_succ]
      exact congrArg v (Fin.castSucc_succ j).symm

end cyclicTrace

section overlapFormula

/-- The **sitewise product matrix** `W σ σ' = ∏ n, U (σ n) (σ' n)` used to
congruence-conjugate the MPO family in `mpo_conjugatePhysical_eq` satisfies `Wᴴ * W = 1`
whenever `Uᴴ * U = 1`.

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1448 (the basis change defining
`σ_tilde`). -/
theorem sitewise_prod_conjTranspose_mul_self {N : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) :
    (Matrix.of (fun σ σ' : Fin N → Fin d => ∏ n, U (σ n) (σ' n)))ᴴ *
      (Matrix.of (fun σ σ' : Fin N → Fin d => ∏ n, U (σ n) (σ' n))) = 1 := by
  ext σ τ
  change (∑ σ' : Fin N → Fin d,
      star (∏ n, U (σ' n) (σ n)) * (∏ n, U (σ' n) (τ n))) = (1 : Matrix _ _ ℂ) σ τ
  have hstep1 : ∀ σ' : Fin N → Fin d,
      star (∏ n, U (σ' n) (σ n)) * (∏ n, U (σ' n) (τ n)) =
        ∏ n, (star (U (σ' n) (σ n)) * U (σ' n) (τ n)) := by
    intro σ'
    rw [star_prod, Finset.prod_mul_distrib]
  simp_rw [hstep1]
  rw [show (∑ σ' : Fin N → Fin d, ∏ n : Fin N,
      (star (U (σ' n) (σ n)) * U (σ' n) (τ n))) =
    ∏ n : Fin N, ∑ x : Fin d, (star (U x (σ n)) * U x (τ n)) from ?_]
  · have hinner : ∀ n : Fin N, (∑ x : Fin d, star (U x (σ n)) * U x (τ n)) =
        if σ n = τ n then (1 : ℂ) else 0 := by
      intro n
      have : (∑ x : Fin d, star (U x (σ n)) * U x (τ n)) = (Uᴴ * U) (σ n) (τ n) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [this, hU, Matrix.one_apply]
    simp_rw [hinner]
    by_cases hστ : σ = τ
    · simp [hστ, Matrix.one_apply]
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hστ
      rw [Finset.prod_eq_zero (Finset.mem_univ n) (if_neg hn), Matrix.one_apply, if_neg hστ]
  · rw [Finset.prod_univ_sum (fun _ : Fin N => (Finset.univ : Finset (Fin d)))
      (fun n x => star (U x (σ n)) * U x (τ n))]
    simp only [Fintype.piFinset_univ]

/-- The trace of the doubled MPO is invariant under a physical basis change `U` with
`Uᴴ * U = 1` (an isometry; a unitary in the square case, e.g. `F.physicalIsometry`).

Source: arXiv:1606.00608, Appendix C.2, lines 1434--1448. -/
theorem trace_mpo_conjugatePhysical_mul_self
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) {N : ℕ} [NeZero N] :
    Matrix.trace (mpo (conjugatePhysical K U) N * mpo (conjugatePhysical K U) N) =
      Matrix.trace (mpo K N * mpo K N) := by
  set W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    Matrix.of (fun σ σ' : Fin N → Fin d => ∏ n, U (σ n) (σ' n)) with hWdef
  have hW : Wᴴ * W = 1 := sitewise_prod_conjTranspose_mul_self U hU
  rw [mpo_conjugatePhysical_eq]
  rw [← hWdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W (mpo K N * Wᴴ), hW, Matrix.one_mul]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hW, Matrix.mul_one]

/-- A neighboring operator vanishes whenever its target sector is inactive, since the
left sector tensor of an inactive sector vanishes identically.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem neighboringOperator_eq_zero_of_inactive_right
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (k h : Fin F.sectorCount) (hh : p h = 0) :
    F.neighboringOperator k h = 0 := by
  ext x y
  simp [PhysicalSectorFactorization.neighboringOperator, hinactive h hh]

/-- The cyclic product of neighboring-operator trace-squares vanishes as soon as one
sector along the cycle is inactive: that sector is the target of some edge in the cycle,
whose neighboring operator (and hence trace-square) vanishes by
`neighboringOperator_eq_zero_of_inactive_right`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem prod_traceSq_eq_zero_of_not_forall_active
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    {N : ℕ} [NeZero N] (k : Fin N → Fin F.sectorCount)
    (hk : ¬ ∀ i, p (k i) ≠ 0) :
    ∏ i : Fin N, Matrix.trace ((F.neighboringOperator (k i) (k (i + 1))) ^ 2) = 0 := by
  rw [not_forall] at hk
  obtain ⟨j, hj⟩ := hk
  rw [not_ne_iff] at hj
  apply Finset.prod_eq_zero (Finset.mem_univ (j - 1))
  rw [sub_add_cancel j 1,
    neighboringOperator_eq_zero_of_inactive_right K F p hinactive (k (j - 1)) (k j) hj]
  simp

/-- **Reduction to the active sector.** The full-sector sum of cyclic trace-square
products equals the sum restricted to cyclic labelings by the active sector, since every
term with an inactive label vanishes.

This is the reconciliation between the active-sector-restricted index type
`F.ActiveSector p` and the full-sector index type `Fin F.sectorCount` needed to
assemble the overlap formula.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem sum_prod_traceSq_eq_sum_active
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    {N : ℕ} [NeZero N] :
    (∑ k : Fin N → Fin F.sectorCount, ∏ i : Fin N,
        Matrix.trace ((F.neighboringOperator (k i) (k (i + 1))) ^ 2)) =
      ∑ k : Fin N → F.ActiveSector p, ∏ i : Fin N,
        Matrix.trace ((F.neighboringOperator (k i : Fin F.sectorCount)
          (k (i + 1) : Fin F.sectorCount)) ^ 2) := by
  rw [show (∑ k : Fin N → Fin F.sectorCount, ∏ i : Fin N,
      Matrix.trace ((F.neighboringOperator (k i) (k (i + 1))) ^ 2)) =
    ∑ k ∈ Finset.univ.filter (fun k : Fin N → Fin F.sectorCount => ∀ i, p (k i) ≠ 0),
      ∏ i : Fin N, Matrix.trace ((F.neighboringOperator (k i) (k (i + 1))) ^ 2) from ?_]
  · refine Finset.sum_bij'
      (fun k hk i => (⟨k i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hk i⟩ : F.ActiveSector p))
      (fun k' _ i => (k' i : Fin F.sectorCount))
      ?hi ?hj ?left_inv ?right_inv ?h
    case hi => intro k _; exact Finset.mem_univ _
    case hj =>
      intro k' _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i => (k' i).2
    case left_inv => intro k _; rfl
    case right_inv => intro k' _; rfl
    case h => intro k _; rfl
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : ∀ i, p (k i) ≠ 0
    · simp [hk]
    · rw [if_neg hk, prod_traceSq_eq_zero_of_not_forall_active K F p hinactive k hk]

/-- **The overlap formula.** The doubled-index MPS self-overlap equals the real cast of
`tr(S^N)`, where `S` is the active-sector trace-squared matrix.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499; the self-overlap
formulation `<V_alpha|V_alpha> = tr(E_alpha^N)` is in Appendix A, proof of Lemma
`equalMPS`, line 1099. -/
theorem mpvOverlap_toMPSTensor_self_eq_ofReal_trace_activeSectorTraceSqMatrix_pow
    (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    {N : ℕ} [NeZero N] :
    MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N =
      Complex.ofReal (Matrix.trace ((activeSectorTraceSqMatrix K F p) ^ N)) := by
  have hK : IsMPDO K := F.isMPDO_of_neighboringOperator_pos hpos
  rw [mpvOverlap_toMPSTensor_self_eq_trace_sq K hK (NeZero.pos N)]
  rw [← trace_mpo_conjugatePhysical_mul_self K F.physicalIsometry
    F.physicalIsometry_isometry (N := N)]
  rw [← Matrix.trace_mul_self_eq_of_reindex_eq (F.physicalConfigEquiv N) _ _
    (F.mpo_sectorCoordinateTensor_eq_reindex_conjugatePhysical N).symm]
  rw [← Matrix.trace_mul_self_eq_of_reindex_eq (F.sectorCoordinateChainEquiv N) _ _
    (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal (N := N))]
  rw [show Matrix.blockDiagonal' (fun k => F.cyclicNeighboringProduct k) *
      Matrix.blockDiagonal' (fun k => F.cyclicNeighboringProduct k) =
      Matrix.blockDiagonal' (fun k => (F.cyclicNeighboringProduct k) ^ 2) from ?_]
  · rw [Matrix.trace_blockDiagonal']
    simp_rw [F.trace_cyclicNeighboringProduct_sq_eq_prod_trace_sq]
    rw [sum_prod_traceSq_eq_sum_active K F p hinactive]
    have hcast : ∀ k : Fin N → F.ActiveSector p, (∏ i : Fin N,
        Matrix.trace ((F.neighboringOperator (k i : Fin F.sectorCount)
          (k (i + 1) : Fin F.sectorCount)) ^ 2)) =
        ((∏ i : Fin N, activeSectorTraceSqMatrix K F p (k i) (k (i + 1)) : ℝ) : ℂ) := by
      intro k
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro i _
      have hsq : ((F.neighboringOperator (k i : Fin F.sectorCount)
          (k (i + 1) : Fin F.sectorCount)) ^ 2).PosSemidef := by
        have hherm := (hpos (k i) (k (i + 1))).isHermitian
        have h_sq_eq : (F.neighboringOperator (k i : Fin F.sectorCount)
            (k (i + 1) : Fin F.sectorCount)) ^ 2 =
            (F.neighboringOperator (k i : Fin F.sectorCount) (k (i + 1) : Fin F.sectorCount)) *
              (F.neighboringOperator (k i : Fin F.sectorCount)
                (k (i + 1) : Fin F.sectorCount))ᴴ := by
          rw [sq, hherm.eq]
        rw [h_sq_eq]
        exact Matrix.posSemidef_self_mul_conjTranspose _
      rw [hsq.isHermitian.trace_eq_ofReal_re]
      rfl
    simp_rw [hcast]
    rw [← Complex.ofReal_sum]
    congr 1
    exact (trace_pow_eq_sum_cyclic_product (activeSectorTraceSqMatrix K F p)).symm
  · rw [← Matrix.blockDiagonal'_mul]
    simp [sq]

end overlapFormula

section singletonSector

/-- **The active sector is unique.** Under literal ZCL, if the neighboring operators are
positive semidefinite, the active-sector trace matrix is primitive, and the tensor is
normal (in the paper's spectral-radius-one sense), then the active sector set has exactly
one element.

The proof is by contradiction from the source-faithful route recorded in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`: the overlap
formula and normality give `tr(S^N) → 1`; positivity bounds `S` entrywise by the Hadamard
square of the primitive stochastic conjugate `P` of `T`; if there were more than one active
sector, `P` would be irreducible substochastic on a nontrivial index set, forcing
`tr(S^N) → 0`, a contradiction. Prerequisite Perron-vector infrastructure:
`TNLean/Algebra/PerronFrobenius/PerronVector.lean`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499; normal-tensor
self-overlap limit (`equalMPS`) at lines 1080--1100. -/
theorem card_activeSector_eq_one_of_literal_ZCL
    [NeZero D] (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hspan : Submodule.span ℂ (Set.range (F.activeSectorOneSiteMatrixFamily p)) = ⊤)
    (hnonzero : ∀ k : F.ActiveSector p,
      ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0)
    (htriangle : ∀ {k h : F.ActiveSector p}, F.neighboringOperator k h ≠ 0 →
      ∃ j : F.ActiveSector p, F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hK_normal : MPSTensor.IsNormalTensor K.toMPSTensor)
    [hne : Nonempty (F.ActiveSector p)] :
    Fintype.card (F.ActiveSector p) = 1 := by
  by_contra hcard
  have hcard1 : 1 < Fintype.card (F.ActiveSector p) := by
    have h1 : 1 ≤ Fintype.card (F.ActiveSector p) := Fintype.card_pos
    omega
  haveI : Nontrivial (F.ActiveSector p) := Fintype.one_lt_card_iff_nontrivial.mp hcard1
  set T := F.activeSectorTraceMatrix p with hTdef
  have hTsq : T ^ 2 = T ^ 3 :=
    activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL K F p hZCL_sq hinactive hpos
  have hTprim : T.IsPrimitive :=
    F.activeSectorTraceMatrix_isPrimitive p hpos hspan hnonzero htriangle
  obtain ⟨v, hv, hPstoch, hPprim⟩ :=
    hTprim.exists_rowStochastic_diagonal_conj_of_pow_two_eq_pow_three hTsq
  set P := (Matrix.diagonal v)⁻¹ * T * Matrix.diagonal v with hPdef
  set S := activeSectorTraceSqMatrix K F p with hSdef
  have hPapply : ∀ i j, P i j = (v i)⁻¹ * T i j * v j :=
    fun i j => Matrix.diagonal_inv_mul_mul_diagonal_apply (fun i => (hv i).ne') T i j
  have hSnn : ∀ k h, 0 ≤ S k h := fun k h => activeSectorTraceSqMatrix_nonneg K F p hpos k h
  have hSbound : ∀ k h, S k h ≤ (T k h) ^ 2 :=
    fun k h => activeSectorTraceSqMatrix_le_activeSectorTraceMatrix_sq K F p hpos k h
  set Shat := (Matrix.diagonal (fun i => (v i) ^ 2))⁻¹ * S *
    Matrix.diagonal (fun i => (v i) ^ 2) with hShatdef
  have hShat_trace : ∀ N, Matrix.trace (Shat ^ N) = Matrix.trace (S ^ N) :=
    fun N => trace_pow_similarity_squared_diagonal S v hv N
  have hShatapply : ∀ i j, Shat i j = ((v i) ^ 2)⁻¹ * S i j * (v j) ^ 2 :=
    fun i j => Matrix.diagonal_inv_mul_mul_diagonal_apply (fun i => (pow_pos (hv i) 2).ne') S i j
  have hShat_nn : ∀ i j, 0 ≤ Shat i j := by
    intro i j
    rw [hShatapply]
    exact mul_nonneg (mul_nonneg (inv_pos.mpr (pow_pos (hv i) 2)).le (hSnn i j))
      (pow_pos (hv j) 2).le
  have hShat_le : ∀ i j, Shat i j ≤ (P ⊙ P) i j := by
    intro i j
    rw [hShatapply, Matrix.hadamard_apply, hPapply]
    have : ((v i) ^ 2)⁻¹ * S i j * (v j) ^ 2 ≤ ((v i) ^ 2)⁻¹ * (T i j) ^ 2 * (v j) ^ 2 := by
      gcongr
      exact hSbound i j
    calc ((v i) ^ 2)⁻¹ * S i j * (v j) ^ 2 ≤ ((v i) ^ 2)⁻¹ * (T i j) ^ 2 * (v j) ^ 2 := this
      _ = ((v i)⁻¹ * T i j * v j) * ((v i)⁻¹ * T i j * v j) := by ring
  have htendsto_zero : Filter.Tendsto (fun N => Matrix.trace (S ^ N)) Filter.atTop (nhds 0) := by
    have := Matrix.trace_pow_tendsto_zero_of_nonneg_le_hadamard_self hPstoch hPprim hShat_nn
      hShat_le
    simpa only [hShat_trace] using this
  have htendsto_one : Filter.Tendsto (fun N => Matrix.trace (S ^ N)) Filter.atTop (nhds 1) := by
    have hoverlap : Filter.Tendsto (fun N => MPSTensor.mpvOverlap K.toMPSTensor K.toMPSTensor N)
        Filter.atTop (nhds (1 : ℂ)) := hK_normal.selfOverlap_tendsto_one
    have hcongr : Filter.Tendsto (fun N => ((Matrix.trace (S ^ N) : ℝ) : ℂ))
        Filter.atTop (nhds (1 : ℂ)) := by
      apply hoverlap.congr'
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      haveI : NeZero N := ⟨hN.ne'⟩
      exact mpvOverlap_toMPSTensor_self_eq_ofReal_trace_activeSectorTraceSqMatrix_pow
        K F p hpos hinactive
    exact Filter.tendsto_ofReal_iff.mp hcongr
  have := tendsto_nhds_unique htendsto_zero htendsto_one
  norm_num at this

/-- **The Case-I relation `T² = T`.** A direct corollary of the active sector being unique
(`card_activeSector_eq_one_of_literal_ZCL`): on a singleton active-sector set the primitive
matrix `T` collapses to a scalar `t` with `t² = t³` and `t² > 0`, forcing `t = 1`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem activeSectorTraceMatrix_pow_two_eq_of_literal_ZCL
    [NeZero D] (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hspan : Submodule.span ℂ (Set.range (F.activeSectorOneSiteMatrixFamily p)) = ⊤)
    (hnonzero : ∀ k : F.ActiveSector p,
      ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0)
    (htriangle : ∀ {k h : F.ActiveSector p}, F.neighboringOperator k h ≠ 0 →
      ∃ j : F.ActiveSector p, F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hK_normal : MPSTensor.IsNormalTensor K.toMPSTensor)
    [hne : Nonempty (F.ActiveSector p)] :
    (F.activeSectorTraceMatrix p) ^ 2 = F.activeSectorTraceMatrix p := by
  have hcard := card_activeSector_eq_one_of_literal_ZCL K F p hpos hspan hnonzero htriangle
    hZCL_sq hinactive hK_normal
  haveI : Subsingleton (F.ActiveSector p) := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  set T := F.activeSectorTraceMatrix p with hTdef
  have hTsq3 : T ^ 2 = T ^ 3 :=
    activeSectorTraceMatrix_pow_two_eq_pow_three_of_literal_ZCL K F p hZCL_sq hinactive hpos
  have hTsqpos := activeSectorTraceMatrix_pow_two_pos K F p hpos hspan hnonzero htriangle
    hZCL_sq hinactive
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  have hcollapse2 : (T ^ 2) i i = T i i * T i i := by
    rw [sq, Matrix.mul_apply, Fintype.sum_eq_single i]
    intro k hk
    exact absurd (Subsingleton.elim k i) hk
  have hcollapse3 : (T ^ 3) i i = (T ^ 2) i i * T i i := by
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_eq_single i]
    intro k hk
    exact absurd (Subsingleton.elim k i) hk
  have heq : (T ^ 2) i i = (T ^ 2) i i * T i i := by rw [← hcollapse3, ← hTsq3]
  have hTii : T i i = 1 := (mul_left_cancel₀ (hTsqpos i i).ne' (by rw [mul_one]; exact heq)).symm
  rw [hcollapse2, hTii, mul_one]

/-- **The rectangular Case-I relation `Q(1−LQ)L = 0`.**  Here
`L β h = tr(F.leftTensor h β)` and `Q k α = tr(F.rightTensor k α)` are the Case-I
factors, and `QL` is the complexification of the active-sector trace matrix `T`.
Thus this identity is the algebraic form of
`activeSectorTraceMatrix_pow_two_eq_of_literal_ZCL`, namely `T² = T`.

**Local fix (`docs/paper-gaps/cpgsv17_pf_rank_one.tex`):** this is a project-derived
rectangular form, in project notation, of the factors built from $l_h$ and $r_k$ in
CPSV16, Appendix C.2, Lemma C.5, lines 1473--1499; the paper does not state it as a
separate displayed theorem. -/
theorem caseI_rectangular_remainder_eq_zero_of_literal_ZCL
    [NeZero D] (F : PhysicalSectorFactorization K) (p : Fin F.sectorCount → ℝ)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hspan : Submodule.span ℂ (Set.range (F.activeSectorOneSiteMatrixFamily p)) = ⊤)
    (hnonzero : ∀ k : F.ActiveSector p,
      ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0)
    (htriangle : ∀ {k h : F.ActiveSector p}, F.neighboringOperator k h ≠ 0 →
      ∃ j : F.ActiveSector p, F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0)
    (hZCL_sq : physTraceTransfer K * physTraceTransfer K = physTraceTransfer K)
    (hinactive : ∀ k, p k = 0 → ∀ beta, F.leftTensor k beta = 0)
    (hK_normal : MPSTensor.IsNormalTensor K.toMPSTensor)
    [hne : Nonempty (F.ActiveSector p)] :
    let L : Matrix (Fin D) (F.ActiveSector p) ℂ :=
      fun beta h ↦ (F.leftTensor h beta).trace
    let Q : Matrix (F.ActiveSector p) (Fin D) ℂ :=
      fun k alpha ↦ (F.rightTensor k alpha).trace
    Q * (1 - L * Q) * L = 0 := by
  intro L Q
  let T := F.activeSectorTraceMatrix p
  have hT : T ^ 2 = T :=
    activeSectorTraceMatrix_pow_two_eq_of_literal_ZCL K F p hpos hspan hnonzero htriangle
      hZCL_sq hinactive hK_normal
  have hQL : Q * L = Matrix.map T Complex.ofReal := by
    simpa only [Q, L, T] using
      trace_rightTensor_mul_trace_leftTensor_eq_map_activeSectorTraceMatrix K F p hpos
  have hmap : (Matrix.map T Complex.ofReal) ^ 2 = Matrix.map T Complex.ofReal := by
    calc
      (Matrix.map T Complex.ofReal) ^ 2 = Matrix.map (T ^ 2) Complex.ofReal := by
        exact (Matrix.map_pow T Complex.ofRealHom 2).symm
      _ = Matrix.map T Complex.ofReal := congrArg (fun M ↦ Matrix.map M Complex.ofReal) hT
  calc
    Q * (1 - L * Q) * L = Q * L - (Q * L) ^ 2 := by
      simp [Matrix.mul_sub, Matrix.sub_mul, pow_two, Matrix.mul_assoc]
    _ = Matrix.map T Complex.ofReal - (Matrix.map T Complex.ofReal) ^ 2 := by rw [hQL]
    _ = 0 := sub_eq_zero.mpr hmap.symm

end singletonSector

end caseI

end MPOTensor
