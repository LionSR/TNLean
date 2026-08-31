/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNormContractivity
import TNLean.MPS.MPDO.NonCartesianActiveSectorCandidate
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# A blocking-channel counterexample for CPSV16 Proposition C.15

This module studies the four-letter tensor of
`NonCartesianActiveSectorCandidate` at the lengths used in CPSV16,
Appendix C.2.  For one explicit virtual boundary, the trace norms of the
three- and four-site closures are strictly larger than that of the two-site
closure.  Consequently no trace-preserving completely positive map can send
every \(\mathcal K_2(X)\) to \(\mathcal K_3(X)\) or to \(\mathcal K_4(X)\).

The source assertion being tested is arXiv:1606.00608, Appendix C.2,
Proposition `prop2to5`, lines 1810--1817, under the standing hypotheses at
lines 1628--1665.  The twice-applied blocking conclusion occurs at lines
1821--1825.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace MPOTensor.CPSVBlockingChannelCounterexample

open NonCartesianActiveSectorCandidate

/-- The virtual boundary that separates the two- and three-site trace norms. -/
private def obstructionBoundary : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1, 2 / 5; -5, 0]

/-- The endpoint pairing
\(D_{ik}=r_k X\ell_i\) for `obstructionBoundary`. -/
private def endpointPairing : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1 / 10, -1 / 5, -3 / 10;
     1 / 10, 0, -1 / 10, -1 / 5;
     -4 / 5, -9 / 10, -1, -11 / 10;
     3 / 10, 1 / 5, 1 / 10, 0]

/-- The displayed endpoint pairing is the transpose of \(R X L\). -/
private lemma endpointPairing_eq :
    (rightPairing * obstructionBoundary * leftPairing)ᵀ =
      Matrix.map endpointPairing Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightPairing, obstructionBoundary, leftPairing, endpointPairing,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The rank-one matrix \(\lvert l_i)(r_k\rvert\) joining two sector labels. -/
private def leftRightMatrix (i k : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (fun beta ↦ leftPairing beta i)
    (fun alpha ↦ rightPairing k alpha)

/-- Multiplication of the paper's rank-one matrices inserts the neighboring
coefficient \(T_{jk}=(r_j\mathbin|l_k)\). -/
private lemma leftRightMatrix_mul_leftRightMatrix (i j k l : Fin 4) :
    leftRightMatrix i j * leftRightMatrix k l =
      (traceMatrix j k : ℂ) • leftRightMatrix i l := by
  simp only [leftRightMatrix]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  have hcoeff := congrFun (congrFun rightPairing_mul_leftPairing j) k
  congr 1

/-- Closing \(\lvert l_i)(r_k\rvert\) against the chosen virtual boundary
gives the endpoint coefficient \((r_k|X|l_i)\). -/
private lemma trace_leftRightMatrix_mul_obstructionBoundary (i k : Fin 4) :
    Matrix.trace (leftRightMatrix i k * obstructionBoundary) =
      (endpointPairing i k : ℂ) := by
  rw [Matrix.trace_mul_comm, leftRightMatrix, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]
  have hEndpoint := congrFun (congrFun endpointPairing_eq i) k
  rw [Matrix.mul_assoc] at hEndpoint
  simpa [dotProduct, Matrix.mulVec, Matrix.mul_apply] using hEndpoint

/-- The closed product of two sector matrices has the coefficient
\(T_{ik}(r_k|X|l_i)\). -/
private lemma trace_two_sectorMatrices (i k : Fin 4) :
    Matrix.trace
        (sectorMatrix i * sectorMatrix k * obstructionBoundary) =
      ((traceMatrix i k * endpointPairing i k : ℝ) : ℂ) := by
  change Matrix.trace
      (leftRightMatrix i i * leftRightMatrix k k * obstructionBoundary) = _
  rw [leftRightMatrix_mul_leftRightMatrix, Matrix.smul_mul,
    Matrix.trace_smul, trace_leftRightMatrix_mul_obstructionBoundary]
  simp only [smul_eq_mul]
  norm_cast

/-- The closed product of three sector matrices has the coefficient
\(T_{ij}T_{jk}(r_k|X|l_i)\). -/
private lemma trace_three_sectorMatrices (i j k : Fin 4) :
    Matrix.trace
        (sectorMatrix i * sectorMatrix j * sectorMatrix k *
          obstructionBoundary) =
      ((traceMatrix i j * traceMatrix j k * endpointPairing i k : ℝ) : ℂ) := by
  change Matrix.trace
      (leftRightMatrix i i * leftRightMatrix j j * leftRightMatrix k k *
        obstructionBoundary) = _
  rw [leftRightMatrix_mul_leftRightMatrix, Matrix.smul_mul,
    leftRightMatrix_mul_leftRightMatrix, smul_smul, Matrix.smul_mul,
    Matrix.trace_smul, trace_leftRightMatrix_mul_obstructionBoundary]
  simp only [smul_eq_mul]
  norm_cast

/-- The closed product of four sector matrices has the coefficient
\(T_{ij}T_{jk}T_{kl}(r_l|X|l_i)\). -/
private lemma trace_four_sectorMatrices (i j k l : Fin 4) :
    Matrix.trace
        (sectorMatrix i * sectorMatrix j * sectorMatrix k * sectorMatrix l *
          obstructionBoundary) =
      ((traceMatrix i j * traceMatrix j k * traceMatrix k l *
        endpointPairing i l : ℝ) : ℂ) := by
  change Matrix.trace
      (leftRightMatrix i i * leftRightMatrix j j * leftRightMatrix k k *
        leftRightMatrix l l * obstructionBoundary) = _
  rw [leftRightMatrix_mul_leftRightMatrix, Matrix.smul_mul,
    leftRightMatrix_mul_leftRightMatrix, smul_smul, Matrix.smul_mul,
    leftRightMatrix_mul_leftRightMatrix, smul_smul, Matrix.smul_mul,
    Matrix.trace_smul, trace_leftRightMatrix_mul_obstructionBoundary]
  simp only [smul_eq_mul]
  norm_cast

/-- The two-site closure is diagonal, with one transition coefficient and one
endpoint pairing. -/
private lemma physClose2_obstructionBoundary :
    physClose2 tensor obstructionBoundary =
      Matrix.diagonal (fun p : Fin 4 × Fin 4 ↦
        ((traceMatrix p.1 p.2 * endpointPairing p.1 p.2 : ℝ) : ℂ)) := by
  ext p q
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      simpa [physClose2_apply, tensor, Matrix.diagonal_apply] using
        trace_two_sectorMatrices i k
    · simp [physClose2_apply, tensor, hkl]
  · simp [physClose2_apply, tensor, hij]

/-- The three-site closure is diagonal, with two transition coefficients and
the same endpoint pairing. -/
private lemma physClose3_obstructionBoundary :
    physClose3 tensor obstructionBoundary =
      Matrix.diagonal (fun p : Fin 4 × (Fin 4 × Fin 4) ↦
        ((traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2 *
          endpointPairing p.1 p.2.2 : ℝ) : ℂ)) := by
  ext p q
  rcases p with ⟨i, j, k⟩
  rcases q with ⟨i', j', k'⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hj : j = j'
    · subst j'
      by_cases hk : k = k'
      · subst k'
        simpa [physClose3_apply, tensor, Matrix.diagonal_apply] using
          trace_three_sectorMatrices i j k
      · simp [physClose3_apply, tensor, hk]
    · simp [physClose3_apply, tensor, hj]
  · simp [physClose3_apply, tensor, hi]

/-- The four-site closure is diagonal, with three transition coefficients and
the same endpoint pairing. -/
private lemma physClose4_obstructionBoundary :
    physClose4 tensor obstructionBoundary =
      Matrix.diagonal (fun p : Fin 4 × (Fin 4 × (Fin 4 × Fin 4)) ↦
        ((traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2.1 *
          traceMatrix p.2.2.1 p.2.2.2 * endpointPairing p.1 p.2.2.2 : ℝ) : ℂ)) := by
  ext p q
  rcases p with ⟨i, j, k, l⟩
  rcases q with ⟨i', j', k', l'⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hj : j = j'
    · subst j'
      by_cases hk : k = k'
      · subst k'
        by_cases hl : l = l'
        · subst l'
          simpa [physClose4_apply, tensor, Matrix.diagonal_apply] using
            trace_four_sectorMatrices i j k l
        · simp [physClose4_apply, tensor, hl]
      · simp [physClose4_apply, tensor, hk]
    · simp [physClose4_apply, tensor, hj]
  · simp [physClose4_apply, tensor, hi]

/-- The trace norm of a real diagonal matrix is the sum of the absolute values
of its diagonal entries. -/
private lemma traceNorm_diagonal_ofReal {n : ℕ} (g : Fin n → ℝ) :
    Matrix.traceNorm (Matrix.diagonal fun i ↦ (g i : ℂ)) =
      ∑ i, |g i| := by
  rw [Matrix.traceNorm_eq_re_trace_abs, CFC.abs]
  have hmul :
      (Matrix.diagonal (fun i ↦ (g i : ℂ)))ᴴ *
          Matrix.diagonal (fun i ↦ (g i : ℂ)) =
        Matrix.diagonal (fun i ↦ (((g i) ^ 2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  have hpos :
      (Matrix.diagonal (fun i ↦ (((g i) ^ 2 : ℝ) : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i ↦
      (RCLike.ofReal_nonneg (K := ℂ)).2 (sq_nonneg (g i))
  rw [Matrix.star_eq_conjTranspose, hmul,
    CFC.sqrt_eq_real_sqrt _ hpos.nonneg, cfcₙ_eq_cfc,
    Matrix.cfc_diagonal (fun i ↦ (g i) ^ 2) Real.sqrt
    ((Set.finite_range fun i : Fin n ↦ (g i) ^ 2).continuousOn Real.sqrt)]
  simp [Matrix.trace, Real.sqrt_sq_eq_abs]

/-- Canonical finite coordinates for two physical sites. -/
private def twoSiteFinEquiv : (Fin 4 × Fin 4) ≃ Fin 16 :=
  finProdFinEquiv

/-- Canonical finite coordinates for three physical sites. -/
private def threeSiteFinEquiv : (Fin 4 × (Fin 4 × Fin 4)) ≃ Fin 64 :=
  (Equiv.prodCongr (Equiv.refl (Fin 4))
    (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)).trans finProdFinEquiv

/-- Canonical finite coordinates for four physical sites. -/
private def fourSiteFinEquiv : (Fin 4 × (Fin 4 × (Fin 4 × Fin 4))) ≃ Fin 256 :=
  (Equiv.prodCongr (Equiv.refl (Fin 4)) threeSiteFinEquiv).trans
    finProdFinEquiv

/-- Canonical finite coordinates for two-site chain configurations. -/
private def twoSiteChainFinEquiv : (Fin 2 → Fin 4) ≃ Fin 16 :=
  (finTwoArrowEquiv (Fin 4)).trans twoSiteFinEquiv

/-- Canonical finite coordinates for three-site chain configurations. -/
private def threeSiteChainFinEquiv : (Fin 3 → Fin 4) ≃ Fin 64 :=
  (_root_.finThreeArrowEquiv (Fin 4)).trans threeSiteFinEquiv

/-- Canonical finite coordinates for four-site chain configurations. -/
private def fourSiteChainFinEquiv : (Fin 4 → Fin 4) ≃ Fin 256 :=
  (_root_.finFourArrowEquiv (Fin 4)).trans fourSiteFinEquiv

/-- The two-site source closure in finite chain coordinates. -/
private def twoSiteObstruction : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.reindex twoSiteFinEquiv twoSiteFinEquiv
    (physClose2 tensor obstructionBoundary)

/-- The three-site source closure in finite chain coordinates. -/
private def threeSiteObstruction : Matrix (Fin 64) (Fin 64) ℂ :=
  Matrix.reindex threeSiteFinEquiv threeSiteFinEquiv
    (physClose3 tensor obstructionBoundary)

/-- The four-site source closure in finite chain coordinates. -/
private def fourSiteObstruction : Matrix (Fin 256) (Fin 256) ℂ :=
  Matrix.reindex fourSiteFinEquiv fourSiteFinEquiv
    (physClose4 tensor obstructionBoundary)

/-- The finite two-site obstruction is the reindexed general chain closure. -/
private lemma twoSiteObstruction_eq_chain :
    twoSiteObstruction =
      Matrix.reindex twoSiteChainFinEquiv twoSiteChainFinEquiv
        (physCloseN tensor 2 obstructionBoundary) := by
  rw [twoSiteObstruction]
  have htwo := LinearMap.congr_fun
    (physCloseN_two_eq_physClose2 tensor) obstructionBoundary
  rw [← htwo]
  ext i j
  simp [twoSiteChainFinEquiv, Matrix.reindex_apply]

/-- The finite three-site obstruction is the reindexed general chain closure. -/
private lemma threeSiteObstruction_eq_chain :
    threeSiteObstruction =
      Matrix.reindex threeSiteChainFinEquiv threeSiteChainFinEquiv
        (physCloseN tensor 3 obstructionBoundary) := by
  rw [threeSiteObstruction]
  have hthree := LinearMap.congr_fun
    (physCloseN_three_eq_physClose3 tensor) obstructionBoundary
  rw [← hthree]
  ext i j
  simp [threeSiteChainFinEquiv, Matrix.reindex_apply]

/-- The finite four-site obstruction is the reindexed general chain closure. -/
private lemma fourSiteObstruction_eq_chain :
    fourSiteObstruction =
      Matrix.reindex fourSiteChainFinEquiv fourSiteChainFinEquiv
        (physCloseN tensor 4 obstructionBoundary) := by
  rw [fourSiteObstruction]
  have hfour := LinearMap.congr_fun
    (physCloseN_four_eq_physClose4 tensor) obstructionBoundary
  rw [← hfour]
  ext i j
  simp [fourSiteChainFinEquiv, Matrix.reindex_apply]

/-- The exact two-site trace norm is \(337/250\). -/
private lemma traceNorm_twoSiteObstruction :
    Matrix.traceNorm twoSiteObstruction = 337 / 250 := by
  rw [twoSiteObstruction, physClose2_obstructionBoundary]
  have hdiag :
      Matrix.reindex twoSiteFinEquiv twoSiteFinEquiv
          (Matrix.diagonal (fun p : Fin 4 × Fin 4 ↦
            ((traceMatrix p.1 p.2 * endpointPairing p.1 p.2 : ℝ) : ℂ))) =
        Matrix.diagonal (fun i : Fin 16 ↦
          ((traceMatrix (twoSiteFinEquiv.symm i).1
            (twoSiteFinEquiv.symm i).2 *
            endpointPairing (twoSiteFinEquiv.symm i).1
              (twoSiteFinEquiv.symm i).2 : ℝ) : ℂ)) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.diagonal_apply]
  rw [hdiag, traceNorm_diagonal_ofReal]
  have hsum :
      (∑ i : Fin 16,
        |traceMatrix (twoSiteFinEquiv.symm i).1
            (twoSiteFinEquiv.symm i).2 *
          endpointPairing (twoSiteFinEquiv.symm i).1
            (twoSiteFinEquiv.symm i).2|) =
        ∑ p : Fin 4 × Fin 4,
          |traceMatrix p.1 p.2 * endpointPairing p.1 p.2| :=
    twoSiteFinEquiv.symm.sum_comp
      (fun p : Fin 4 × Fin 4 ↦
        |traceMatrix p.1 p.2 * endpointPairing p.1 p.2|)
  rw [hsum]
  rw [Fintype.sum_prod_type]
  norm_num [traceMatrix, endpointPairing, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The exact three-site trace norm is \(27/20\). -/
private lemma traceNorm_threeSiteObstruction :
    Matrix.traceNorm threeSiteObstruction = 27 / 20 := by
  rw [threeSiteObstruction, physClose3_obstructionBoundary]
  have hdiag :
      Matrix.reindex threeSiteFinEquiv threeSiteFinEquiv
          (Matrix.diagonal (fun p : Fin 4 × (Fin 4 × Fin 4) ↦
            ((traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2 *
              endpointPairing p.1 p.2.2 : ℝ) : ℂ))) =
        Matrix.diagonal (fun i : Fin 64 ↦
          ((traceMatrix (threeSiteFinEquiv.symm i).1
              (threeSiteFinEquiv.symm i).2.1 *
            traceMatrix (threeSiteFinEquiv.symm i).2.1
              (threeSiteFinEquiv.symm i).2.2 *
            endpointPairing (threeSiteFinEquiv.symm i).1
              (threeSiteFinEquiv.symm i).2.2 : ℝ) : ℂ)) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.diagonal_apply]
  rw [hdiag, traceNorm_diagonal_ofReal]
  have hsum :
      (∑ i : Fin 64,
        |traceMatrix (threeSiteFinEquiv.symm i).1
              (threeSiteFinEquiv.symm i).2.1 *
            traceMatrix (threeSiteFinEquiv.symm i).2.1
              (threeSiteFinEquiv.symm i).2.2 *
          endpointPairing (threeSiteFinEquiv.symm i).1
            (threeSiteFinEquiv.symm i).2.2|) =
        ∑ p : Fin 4 × (Fin 4 × Fin 4),
          |traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2 *
            endpointPairing p.1 p.2.2| :=
    threeSiteFinEquiv.symm.sum_comp
      (fun p : Fin 4 × (Fin 4 × Fin 4) ↦
        |traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2 *
          endpointPairing p.1 p.2.2|)
  rw [hsum]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have habs (i j k : Fin 4) :
      |traceMatrix i j * traceMatrix j k * endpointPairing i k| =
        traceMatrix i j * traceMatrix j k * |endpointPairing i k| := by
    rw [abs_mul, abs_mul, abs_of_pos (traceMatrix_pos i j),
      abs_of_pos (traceMatrix_pos j k)]
  simp_rw [habs]
  calc
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
        traceMatrix i j * traceMatrix j k * |endpointPairing i k|) =
        ∑ i : Fin 4, ∑ k : Fin 4, ∑ j : Fin 4,
          traceMatrix i j * traceMatrix j k * |endpointPairing i k| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 4, ∑ k : Fin 4,
        (∑ j : Fin 4, traceMatrix i j * traceMatrix j k) *
          |endpointPairing i k| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ i : Fin 4, ∑ k : Fin 4,
        (traceMatrix ^ 2) i k * |endpointPairing i k| := by
      simp only [pow_two, Matrix.mul_apply]
    _ = ∑ i : Fin 4, ∑ k : Fin 4,
        (1 / 4 : ℝ) * |endpointPairing i k| := by
      rw [traceMatrix_sq]
      rfl
    _ = 27 / 20 := by
      norm_num [endpointPairing, Fin.sum_univ_four,
        Matrix.cons_val_two, Matrix.cons_val_three]

/-- The exact four-site trace norm is again \(27/20\).  The equality with the
three-site value is the source relation \(T^3=T^2\). -/
private lemma traceNorm_fourSiteObstruction :
    Matrix.traceNorm fourSiteObstruction = 27 / 20 := by
  rw [fourSiteObstruction, physClose4_obstructionBoundary]
  have hdiag :
      Matrix.reindex fourSiteFinEquiv fourSiteFinEquiv
          (Matrix.diagonal
            (fun p : Fin 4 × (Fin 4 × (Fin 4 × Fin 4)) ↦
              ((traceMatrix p.1 p.2.1 *
                traceMatrix p.2.1 p.2.2.1 *
                traceMatrix p.2.2.1 p.2.2.2 *
                endpointPairing p.1 p.2.2.2 : ℝ) : ℂ))) =
        Matrix.diagonal (fun a : Fin 256 ↦
          ((traceMatrix (fourSiteFinEquiv.symm a).1
              (fourSiteFinEquiv.symm a).2.1 *
            traceMatrix (fourSiteFinEquiv.symm a).2.1
              (fourSiteFinEquiv.symm a).2.2.1 *
            traceMatrix (fourSiteFinEquiv.symm a).2.2.1
              (fourSiteFinEquiv.symm a).2.2.2 *
            endpointPairing (fourSiteFinEquiv.symm a).1
              (fourSiteFinEquiv.symm a).2.2.2 : ℝ) : ℂ)) := by
    ext a b
    simp [Matrix.reindex_apply, Matrix.diagonal_apply]
  rw [hdiag, traceNorm_diagonal_ofReal]
  have hsum :
      (∑ a : Fin 256,
        |traceMatrix (fourSiteFinEquiv.symm a).1
                (fourSiteFinEquiv.symm a).2.1 *
              traceMatrix (fourSiteFinEquiv.symm a).2.1
                (fourSiteFinEquiv.symm a).2.2.1 *
            traceMatrix (fourSiteFinEquiv.symm a).2.2.1
              (fourSiteFinEquiv.symm a).2.2.2 *
          endpointPairing (fourSiteFinEquiv.symm a).1
            (fourSiteFinEquiv.symm a).2.2.2|) =
        ∑ p : Fin 4 × (Fin 4 × (Fin 4 × Fin 4)),
          |traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2.1 *
              traceMatrix p.2.2.1 p.2.2.2 *
            endpointPairing p.1 p.2.2.2| :=
    fourSiteFinEquiv.symm.sum_comp
      (fun p : Fin 4 × (Fin 4 × (Fin 4 × Fin 4)) ↦
        |traceMatrix p.1 p.2.1 * traceMatrix p.2.1 p.2.2.1 *
            traceMatrix p.2.2.1 p.2.2.2 *
          endpointPairing p.1 p.2.2.2|)
  rw [hsum]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have habs (i j k l : Fin 4) :
      |traceMatrix i j * traceMatrix j k * traceMatrix k l *
          endpointPairing i l| =
        traceMatrix i j * traceMatrix j k * traceMatrix k l *
          |endpointPairing i l| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (traceMatrix_pos i j),
      abs_of_pos (traceMatrix_pos j k), abs_of_pos (traceMatrix_pos k l)]
  simp_rw [habs]
  have hcube (i l : Fin 4) :
      (∑ j : Fin 4, ∑ k : Fin 4,
          traceMatrix i j * traceMatrix j k * traceMatrix k l) =
        (traceMatrix ^ 3) i l := by
    calc
      (∑ j : Fin 4, ∑ k : Fin 4,
          traceMatrix i j * traceMatrix j k * traceMatrix k l) =
          ∑ k : Fin 4, ∑ j : Fin 4,
            traceMatrix i j * traceMatrix j k * traceMatrix k l := by
        rw [Finset.sum_comm]
      _ = (traceMatrix ^ 2 * traceMatrix) i l := by
        simp only [Matrix.mul_apply, pow_two]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
      _ = (traceMatrix ^ 3) i l :=
        congrFun (congrFun (pow_succ traceMatrix 2).symm i) l
  calc
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        traceMatrix i j * traceMatrix j k * traceMatrix k l *
          |endpointPairing i l|) =
        ∑ i : Fin 4, ∑ j : Fin 4, ∑ l : Fin 4, ∑ k : Fin 4,
          traceMatrix i j * traceMatrix j k * traceMatrix k l *
            |endpointPairing i l| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 4, ∑ l : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
        traceMatrix i j * traceMatrix j k * traceMatrix k l *
          |endpointPairing i l| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 4, ∑ l : Fin 4,
        (∑ j : Fin 4, ∑ k : Fin 4,
          traceMatrix i j * traceMatrix j k * traceMatrix k l) *
            |endpointPairing i l| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ i : Fin 4, ∑ l : Fin 4,
        (traceMatrix ^ 3) i l * |endpointPairing i l| := by
      simp_rw [hcube]
    _ = ∑ i : Fin 4, ∑ l : Fin 4,
        (1 / 4 : ℝ) * |endpointPairing i l| := by
      rw [← traceMatrix_sq_eq_cube, traceMatrix_sq]
      rfl
    _ = 27 / 20 := by
      norm_num [endpointPairing, Fin.sum_univ_four,
        Matrix.cons_val_two, Matrix.cons_val_three]

/-- The source two-site obstruction is Hermitian. -/
private lemma twoSiteObstruction_isHermitian : twoSiteObstruction.IsHermitian := by
  rw [twoSiteObstruction, physClose2_obstructionBoundary]
  apply Matrix.IsHermitian.reindex
  exact (Matrix.isHermitian_diagonal_iff).2 fun _ ↦ by
    rw [isSelfAdjoint_iff]
    simp [Complex.conj_ofReal]

/-- Trace-norm contractivity rules out a channel taking the two-site
obstruction to any Hermitian target of trace norm \(27/20\). -/
private lemma false_of_isKrausCPTP_map_twoSiteObstruction
    {n : ℕ} (T : Matrix (Fin 16) (Fin 16) ℂ →ₗ[ℂ]
      Matrix (Fin n) (Fin n) ℂ)
    (hT : IsKrausCPTP T) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hmap : T twoSiteObstruction = Y)
    (hYnorm : Matrix.traceNorm Y = 27 / 20) : False := by
  have hcontract := Matrix.traceNorm_map_le_of_positive_of_tracePreserving
    (fun _ hρ ↦ hT.map_posSemidef hρ) (fun ρ ↦ hT.trace_map ρ)
    twoSiteObstruction_isHermitian
  rw [hmap, hYnorm, traceNorm_twoSiteObstruction] at hcontract
  norm_num at hcontract

/-- No trace-preserving completely positive map sends all two-site closures
of the candidate tensor to the corresponding three-site closures.

This is the finite-dimensional channel obstruction used below when the tensor
is placed inside a witness satisfying the standing hypotheses of CPSV16,
Appendix C.2, Proposition `prop2to5`, lines 1628--1665 and 1810--1817. -/
theorem not_exists_two_to_three_site_map :
    ¬ ∃ T : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ →ₗ[ℂ]
        Matrix (Fin 3 → Fin 4) (Fin 3 → Fin 4) ℂ,
      IsKrausCPTP T ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        T (physCloseN tensor 2 X) = physCloseN tensor 3 X := by
  rintro ⟨T, hT, hclose⟩
  let Tfin : Matrix (Fin 16) (Fin 16) ℂ →ₗ[ℂ]
      Matrix (Fin 64) (Fin 64) ℂ :=
    Matrix.equivReindexMap threeSiteChainFinEquiv ∘ₗ T ∘ₗ
      Matrix.equivReindexMap twoSiteChainFinEquiv.symm
  have hTfin : IsKrausCPTP Tfin := by
    exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP twoSiteChainFinEquiv.symm) hT)
      (Matrix.equivReindexMap_isKrausCPTP threeSiteChainFinEquiv)
  have hcloseObstruction :
      Tfin twoSiteObstruction = threeSiteObstruction := by
    have hin :
        Matrix.reindex twoSiteChainFinEquiv.symm twoSiteChainFinEquiv.symm
            twoSiteObstruction =
          physCloseN tensor 2 obstructionBoundary := by
      ext i j
      simp [twoSiteObstruction_eq_chain, Matrix.reindex_apply]
    simp only [Tfin, LinearMap.comp_apply, Matrix.equivReindexMap]
    change Matrix.reindex threeSiteChainFinEquiv threeSiteChainFinEquiv
        (T (Matrix.reindex twoSiteChainFinEquiv.symm
          twoSiteChainFinEquiv.symm twoSiteObstruction)) = threeSiteObstruction
    rw [hin, hclose obstructionBoundary]
    exact threeSiteObstruction_eq_chain.symm
  exact false_of_isKrausCPTP_map_twoSiteObstruction Tfin hTfin
    threeSiteObstruction hcloseObstruction traceNorm_threeSiteObstruction

/-- No trace-preserving completely positive map sends all two-site closures
of the candidate tensor to the corresponding four-site closures.

After lifting to the ambient simple-biCF witness, this also rules out the
twice-blocked refinement conclusion used for the logical implication
`(ii) ⇒ (v)` of CPSV16, Theorem 4.9.  The closing proof at lines 1821--1825
prints the cyclic label `(iii) ⇒ (v)` for this step. -/
theorem not_exists_two_to_four_site_map :
    ¬ ∃ T : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ →ₗ[ℂ]
        Matrix (Fin 4 → Fin 4) (Fin 4 → Fin 4) ℂ,
      IsKrausCPTP T ∧
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        T (physCloseN tensor 2 X) = physCloseN tensor 4 X := by
  rintro ⟨T, hT, hclose⟩
  let Tfin : Matrix (Fin 16) (Fin 16) ℂ →ₗ[ℂ]
      Matrix (Fin 256) (Fin 256) ℂ :=
    Matrix.equivReindexMap fourSiteChainFinEquiv ∘ₗ T ∘ₗ
      Matrix.equivReindexMap twoSiteChainFinEquiv.symm
  have hTfin : IsKrausCPTP Tfin := by
    exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP twoSiteChainFinEquiv.symm) hT)
      (Matrix.equivReindexMap_isKrausCPTP fourSiteChainFinEquiv)
  have hcloseObstruction :
      Tfin twoSiteObstruction = fourSiteObstruction := by
    have hin :
        Matrix.reindex twoSiteChainFinEquiv.symm twoSiteChainFinEquiv.symm
            twoSiteObstruction =
          physCloseN tensor 2 obstructionBoundary := by
      ext i j
      simp [twoSiteObstruction_eq_chain, Matrix.reindex_apply]
    simp only [Tfin, LinearMap.comp_apply, Matrix.equivReindexMap]
    change Matrix.reindex fourSiteChainFinEquiv fourSiteChainFinEquiv
        (T (Matrix.reindex twoSiteChainFinEquiv.symm
          twoSiteChainFinEquiv.symm twoSiteObstruction)) = fourSiteObstruction
    rw [hin, hclose obstructionBoundary]
    exact fourSiteObstruction_eq_chain.symm
  exact false_of_isKrausCPTP_map_twoSiteObstruction Tfin hTfin
    fourSiteObstruction hcloseObstruction traceNorm_fourSiteObstruction

end MPOTensor.CPSVBlockingChannelCounterexample
