/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActiveSectorSpanningCounterexample
import TNLean.MPS.MPDO.PhysicalSectorPruning

/-!
# Inverse-map provenance of the four-sector example

This file computes the inverse-map tensors selected from an explicit Hayashi
decomposition of the three-site marginal of the four-sector classical tensor
in `ActiveSectorSpanningCounterexample`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1413--1499
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ActiveSectorSpanningCounterexample

/-- The diagonal inverse-tensor coefficients reconstruct each virtual matrix
unit from the four nonzero physical slices.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1428. -/
private lemma sum_inverseTensor_diagonal (alpha beta : Fin 2) :
    (∑ i : Fin 4,
        inverseTensor tensor tensor_isInjective (finProdFinEquiv (i, i)) alpha beta •
          sectorMatrix i) = Matrix.single alpha beta (1 : ℂ) := by
  calc
    _ = ∑ q : Fin 4 × Fin 4,
        inverseTensor tensor tensor_isInjective (finProdFinEquiv q) alpha beta •
          tensor.toMPSTensor (finProdFinEquiv q) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · have hdiv : (finProdFinEquiv (i, i)).divNat = i :=
          MPSTensor.finProdFinEquiv_divNat i i
        have hmod : (finProdFinEquiv (i, i)).modNat = i :=
          MPSTensor.finProdFinEquiv_modNat i i
        simp [MPOTensor.toMPSTensor, tensor, hdiv, hmod]
      · intro j _ hji
        have hdiv : (finProdFinEquiv (i, j)).divNat = i :=
          MPSTensor.finProdFinEquiv_divNat i j
        have hmod : (finProdFinEquiv (i, j)).modNat = j :=
          MPSTensor.finProdFinEquiv_modNat i j
        have hij : i ≠ j := Ne.symm hji
        simp [MPOTensor.toMPSTensor, tensor, hij, hdiv, hmod]
      · simp
    _ = ∑ q : Fin (4 * 4),
        inverseTensor tensor tensor_isInjective q alpha beta • tensor.toMPSTensor q := by
      exact (Equiv.sum_comp finProdFinEquiv (fun q =>
        inverseTensor tensor tensor_isInjective q alpha beta • tensor.toMPSTensor q)).symm
    _ = Matrix.single alpha beta (1 : ℂ) :=
      inverseTensor_spec tensor tensor_isInjective alpha beta

/-- The four nonzero physical slices form a basis of the virtual matrix
space, not merely a spanning family.  This is a property of the explicit
counterexample tensor. -/
private lemma sectorMatrix_linearIndependent : LinearIndependent ℂ sectorMatrix := by
  rw [Fintype.linearIndependent_iff]
  intro c hzero k
  have h00 := congrFun (congrFun hzero 0) 0
  have h01 := congrFun (congrFun hzero 0) 1
  have h10 := congrFun (congrFun hzero 1) 0
  have h11 := congrFun (congrFun hzero 1) 1
  simp [sectorMatrix, leftPairing, rightPairing, Matrix.sum_apply,
    Fin.sum_univ_four] at h00 h01 h10 h11
  fin_cases k
  · change c 0 = 0
    linear_combination h00 + 8 * h01 + (1 / 4) * h10 + 2 * h11
  · change c 1 = 0
    linear_combination h00 + 8 * h01 - (1 / 4) * h10 - 2 * h11
  · change c 2 = 0
    linear_combination h00 - 8 * h01 + (1 / 4) * h10 - 2 * h11
  · change c 3 = 0
    linear_combination h00 - 8 * h01 - (1 / 4) * h10 + 2 * h11

/-- The coefficient table dual to the four sector matrices.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1439. -/
private noncomputable def dualCoefficient (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  match i with
  | 0 => !![1, 8; 1 / 4, 2]
  | 1 => !![1, 8; -1 / 4, -2]
  | 2 => !![1, -8; 1 / 4, -2]
  | 3 => !![1, -8; -1 / 4, 2]

/-- The inverse tensor on a diagonal physical slice is the dual basis to the
four sector matrices.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1439. -/
private lemma inverseTensor_diagonal_eq_dualCoefficient (i : Fin 4) :
    inverseTensor tensor tensor_isInjective (finProdFinEquiv (i, i)) =
      dualCoefficient i := by
  ext alpha beta
  apply sub_eq_zero.mp
  apply Fintype.linearIndependent_iff.mp sectorMatrix_linearIndependent
    (fun j =>
      inverseTensor tensor tensor_isInjective (finProdFinEquiv (j, j)) alpha beta -
        dualCoefficient j alpha beta)
  have hinv := sum_inverseTensor_diagonal alpha beta
  have hdual :
      (∑ j : Fin 4, dualCoefficient j alpha beta • sectorMatrix j) =
        Matrix.single alpha beta (1 : ℂ) := by
    ext x y
    fin_cases alpha <;> fin_cases beta <;> fin_cases x <;> fin_cases y <;>
      simp [dualCoefficient, sectorMatrix, leftPairing, rightPairing,
        Fin.sum_univ_four, Matrix.single] <;> norm_num
  simp only [sub_smul]
  rw [Finset.sum_sub_distrib, hinv, hdual, sub_self]

private lemma inverseTensor_diagonal_apply (i : Fin 4) (alpha beta : Fin 2) :
    inverseTensor tensor tensor_isInjective (finProdFinEquiv (i, i)) alpha beta =
      dualCoefficient i alpha beta :=
  congrFun (congrFun (inverseTensor_diagonal_eq_dualCoefficient i) alpha) beta

private lemma sum_evalWord_diagonal (N : ℕ) :
    ∑ sigma : Fin N → Fin 4,
        evalWord tensor (List.ofFn sigma) (List.ofFn sigma) =
      physTraceTransfer tensor ^ N := by
  induction N with
  | zero => simp [evalWord_nil]
  | succ N ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin 4)).sum_comp,
        Fintype.sum_prod_type]
      have hlist : ∀ (a : Fin 4) (rho : Fin N → Fin 4),
          List.ofFn (Fin.cons a rho : Fin (N + 1) → Fin 4) = a :: List.ofFn rho := by
        intro a rho
        simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      calc
        _ = ∑ a : Fin 4, ∑ rho : Fin N → Fin 4,
            tensor a a * evalWord tensor (List.ofFn rho) (List.ofFn rho) := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun rho _ => ?_
              change evalWord tensor (List.ofFn (Fin.cons a rho))
                  (List.ofFn (Fin.cons a rho)) =
                tensor a a * evalWord tensor (List.ofFn rho) (List.ofFn rho)
              rw [hlist a rho, evalWord_cons]
        _ = (∑ a : Fin 4, tensor a a) *
              ∑ rho : Fin N → Fin 4,
                evalWord tensor (List.ofFn rho) (List.ofFn rho) :=
          (Finset.sum_mul_sum _ _ _ _).symm
        _ = physTraceTransfer tensor ^ (N + 1) := by
          rw [ih, pow_succ']
          rfl

private lemma trace_mpo_four :
    (mpo tensor 4).trace = Matrix.trace (physTraceTransfer tensor ^ 4) := by
  rw [← sum_evalWord_diagonal 4, Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, mpo_apply, mpoMatrixEntry]

/-- The source-normalized four-site tail is the idempotent physical-trace
transfer of the example.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1418. -/
lemma normalizedFourSiteTail_tensor :
    normalizedFourSiteTail tensor = leftPairing * rightPairing := by
  have htrace : (mpo tensor 4).trace = 1 := by
    rw [trace_mpo_four, physTraceTransfer_tensor, leftPairing_mul_rightPairing]
    norm_num [Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [normalizedFourSiteTail, htrace, inv_one, one_smul, physTraceTransfer_tensor]

/-- The left density matrix in the four one-dimensional Hayashi sectors.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.3, lines 1351--1363. -/
private noncomputable def hayashiLeftDensity (k : Fin 4) :
    Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) ℂ :=
  Matrix.diagonal fun x => (rightPairing * leftPairing) x.1 k

/-- The right density matrix in the four one-dimensional Hayashi sectors.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.3, lines 1351--1363. -/
private noncomputable def hayashiRightDensity (k : Fin 4) :
    Matrix (Fin 1 × Fin 4) (Fin 1 × Fin 4) ℂ :=
  Matrix.diagonal fun x => (rightPairing * leftPairing) k x.2

private lemma hayashiLeftDensity_posSemidef (k : Fin 4) :
    (hayashiLeftDensity k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  rintro ⟨i, u⟩
  fin_cases u
  rw [rightPairing_mul_leftPairing]
  fin_cases i <;> fin_cases k <;> norm_num [Complex.nonneg_iff]

private lemma trace_hayashiLeftDensity (k : Fin 4) :
    (hayashiLeftDensity k).trace = 1 := by
  rw [Matrix.trace]
  change (∑ x : Fin 4 × Fin 1, (rightPairing * leftPairing) x.1 k) = 1
  rw [Fintype.sum_prod_type]
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> norm_num [Fin.sum_univ_four, Fin.sum_univ_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

private lemma hayashiRightDensity_posSemidef (k : Fin 4) :
    (hayashiRightDensity k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  rintro ⟨u, i⟩
  fin_cases u
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> fin_cases i <;> norm_num [Complex.nonneg_iff]

private lemma trace_hayashiRightDensity (k : Fin 4) :
    (hayashiRightDensity k).trace = 1 := by
  rw [Matrix.trace]
  change (∑ x : Fin 1 × Fin 4, (rightPairing * leftPairing) k x.2) = 1
  rw [Fintype.sum_prod_type]
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> norm_num [Fin.sum_univ_four, Fin.sum_univ_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The explicit classical three-site state used in the refined Hayashi
decomposition.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.3, lines 1351--1363. -/
noncomputable def threeSiteState :
    Matrix (Fin 4 × Fin 4 × Fin 4) (Fin 4 × Fin 4 × Fin 4) ℂ :=
  fun x y => if x = y then
    (1 / 4 : ℂ) * (rightPairing * leftPairing) x.1 x.2.1 *
      (rightPairing * leftPairing) x.2.1 x.2.2
    else 0

/-- The rank-one open sector matrix with left physical label `i` and right
physical label `j`.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1455. -/
noncomputable def crossSectorMatrix (i j : Fin 4) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (fun beta => leftPairing beta i) (fun alpha => rightPairing j alpha)

/-- A closed scalar sector is the open sector matrix with equal endpoint
labels.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1455. -/
lemma sectorMatrix_eq_crossSectorMatrix (i : Fin 4) :
    sectorMatrix i = crossSectorMatrix i i := rfl

/-- Concatenating two open sector matrices contributes the neighboring
transition weight at their common boundary.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1455. -/
lemma crossSectorMatrix_mul (i j k h : Fin 4) :
    crossSectorMatrix i j * crossSectorMatrix k h =
      (rightPairing * leftPairing) j k • crossSectorMatrix i h := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [crossSectorMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- Closing an open sector matrix against the normalized physical-trace
transfer gives the uniform sector weight `1 / 4`.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1455. -/
lemma trace_crossSectorMatrix_mul_transfer (i k : Fin 4) :
    Matrix.trace (crossSectorMatrix i k * (leftPairing * rightPairing)) = 1 / 4 := by
  fin_cases i <;> fin_cases k <;>
    norm_num [crossSectorMatrix, leftPairing, rightPairing, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two]

private lemma trace_three_sectorMatrices_mul_transfer (i j k : Fin 4) :
    Matrix.trace
        (sectorMatrix i * sectorMatrix j * sectorMatrix k *
          (leftPairing * rightPairing)) =
      (1 / 4 : ℂ) * (rightPairing * leftPairing) i j *
        (rightPairing * leftPairing) j k := by
  rw [sectorMatrix_eq_crossSectorMatrix, sectorMatrix_eq_crossSectorMatrix,
    sectorMatrix_eq_crossSectorMatrix, crossSectorMatrix_mul,
    Matrix.smul_mul, crossSectorMatrix_mul]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [trace_crossSectorMatrix_mul_transfer]
  ring

/-- The explicit three-site state is the closure against the normalized
four-site tail selected in Appendix C.2.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1418. -/
private lemma isThreeSiteClosure_threeSiteState :
    IsThreeSiteClosure tensor (normalizedFourSiteTail tensor) threeSiteState := by
  intro i₁ i₂ i₃ j₁ j₂ j₃
  rw [normalizedFourSiteTail_tensor]
  by_cases h₁ : i₁ = j₁
  · subst j₁
    by_cases h₂ : i₂ = j₂
    · subst j₂
      by_cases h₃ : i₃ = j₃
      · subst j₃
        simp only [threeSiteState, if_pos]
        simp only [tensor, if_pos]
        exact (trace_three_sectorMatrices_mul_transfer i₁ i₂ i₃).symm
      · have htuple : (i₁, i₂, i₃) ≠ (i₁, i₂, j₃) := by
          intro h
          exact h₃ (congrArg (fun x => x.2.2) h)
        rw [threeSiteState, if_neg htuple]
        simp [tensor, h₃]
    · have htuple : (i₁, i₂, i₃) ≠ (i₁, j₂, j₃) := by
        intro h
        exact h₂ (congrArg (fun x => x.2.1) h)
      rw [threeSiteState, if_neg htuple]
      simp [tensor, h₂]
  · have htuple : (i₁, i₂, i₃) ≠ (j₁, j₂, j₃) := by
      intro h
      exact h₁ (congrArg Prod.fst h)
    rw [threeSiteState, if_neg htuple]
    simp [tensor, h₁]

/-- The refined four-sector Hayashi decomposition of the explicit three-site
state. Each middle-site classical label is retained as a one-dimensional
direct-sum sector.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.3, lines 1351--1363,
used in Lemma C.4 at lines 1413--1455. -/
noncomputable def hayashiData : EtaStructure threeSiteState where
  m := 4
  dL := fun _ => 1
  dR := fun _ => 1
  decompB := sectorEquiv
  U_B := ⟨1, by simp⟩
  p := p
  hp_nonneg := p_nonneg
  hp_sum := sum_p
  ρ_left := hayashiLeftDensity
  ρ_right := hayashiRightDensity
  hρ_left_dm := fun k => ⟨hayashiLeftDensity_posSemidef k,
    trace_hayashiLeftDensity k⟩
  hρ_right_dm := fun k => ⟨hayashiRightDensity_posSemidef k,
    trace_hayashiRightDensity k⟩
  h_state := by
    ext x y
    obtain ⟨i, ⟨⟨k, ⟨l, r⟩⟩, j⟩⟩ := x
    obtain ⟨i', ⟨⟨k', ⟨l', r'⟩⟩, j'⟩⟩ := y
    fin_cases l
    fin_cases r
    fin_cases l'
    fin_cases r'
    rw [HayashiMarkov.blockState_apply]
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, HayashiMarkov.liftB,
      HayashiMarkov.abcEquiv, sectorEquiv, threeSiteState, p,
      hayashiLeftDensity, hayashiRightDensity]
    by_cases hii : i = i' <;> by_cases hkk : k = k' <;> by_cases hjj : j = j' <;>
      simp [hii, hkk, hjj]

private lemma sum_mul_hayashiLeftDensity (f : Fin 4 → Fin 4 → ℂ) (k : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, f i j * hayashiLeftDensity k (i, 0) (j, 0)) =
      ∑ i : Fin 4, f i i * (rightPairing * leftPairing) i k := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [hayashiLeftDensity]
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    simp [hayashiLeftDensity, hij]
  · simp

private lemma sum_mul_hayashiRightDensity (f : Fin 4 → Fin 4 → ℂ) (k : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, f i j * hayashiRightDensity k (0, i) (0, j)) =
      ∑ i : Fin 4, f i i * (rightPairing * leftPairing) k i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [hayashiRightDensity]
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    simp [hayashiRightDensity, hij]
  · simp

/-- For the refined Hayashi decomposition, the source inverse map recovers
the chosen left sector tensor exactly. The factor `p_k = 1/4` cancels the
factor four in the left inverse contraction.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1439. -/
lemma sectorTensorL_hayashiData (k : Fin 4) (beta : Fin 2) :
    sectorTensorL tensor tensor_isInjective hayashiData
        (normalizedFourSiteTail tensor) 0 0 k beta =
      factorization.leftTensor k beta := by
  ext x y
  fin_cases x
  fin_cases y
  change ((normalizedFourSiteTail tensor 0 0)⁻¹ * (p k : ℂ) *
      (∑ i : Fin 4, ∑ j : Fin 4,
        inverseTensor tensor tensor_isInjective (finProdFinEquiv (i, j)) 0 beta *
          hayashiLeftDensity k (i, 0) (j, 0))) = leftPairing beta k
  rw [normalizedFourSiteTail_tensor, leftPairing_mul_rightPairing]
  norm_num [p]
  rw [sum_mul_hayashiLeftDensity]
  simp_rw [inverseTensor_diagonal_apply]
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> fin_cases beta <;>
    norm_num [dualCoefficient, leftPairing, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- For the refined Hayashi decomposition, the source inverse map recovers
the chosen right sector tensor exactly.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1439. -/
lemma sectorTensorR_hayashiData (k : Fin 4) (alpha : Fin 2) :
    sectorTensorR tensor tensor_isInjective hayashiData 0 k alpha =
      factorization.rightTensor k alpha := by
  ext x y
  fin_cases x
  fin_cases y
  change (∑ i : Fin 4, ∑ j : Fin 4,
      inverseTensor tensor tensor_isInjective (finProdFinEquiv (i, j)) alpha 0 *
        hayashiRightDensity k (0, i) (0, j)) = rightPairing k alpha
  rw [sum_mul_hayashiRightDensity]
  simp_rw [inverseTensor_diagonal_apply]
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> fin_cases alpha <;>
    norm_num [dualCoefficient, rightPairing, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

private lemma normalizedFourSiteTail_tensor_zero_zero_ne :
    normalizedFourSiteTail tensor 0 0 ≠ 0 := by
  rw [normalizedFourSiteTail_tensor, leftPairing_mul_rightPairing]
  norm_num

/-- The source-selected inverse-map factorization, including the inactive-sector
reparameterization. In this example every Hayashi weight is `1/4`, so no
sector is removed.

Source: arXiv:1606.00608, Appendix C.2, lines 1413--1455. -/
noncomputable def inverseMapFactorization : PhysicalSectorFactorization tensor :=
  zeroWeightReparameterizedInverseMapPhysicalSectorFactorization
    tensor tensor_isInjective (normalizedFourSiteTail tensor)
      isThreeSiteClosure_threeSiteState hayashiData 0 0
      normalizedFourSiteTail_tensor_zero_zero_ne

/-- The neighboring operators selected by the explicit inverse-map provenance
are exactly those of the directly written factorization.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1455. -/
lemma inverseMapFactorization_neighboringOperator (k h : Fin 4) :
    inverseMapFactorization.neighboringOperator k h =
      factorization.neighboringOperator k h := by
  unfold inverseMapFactorization
  rw [zeroWeightReparameterizedInverseMapPhysicalSectorFactorization_neighboringOperator]
  have hk : hayashiData.p k ≠ 0 := by
    change p k ≠ 0
    norm_num [p]
  rw [if_pos hk]
  ext x y
  obtain ⟨xR, xL⟩ := x
  obtain ⟨yR, yL⟩ := y
  fin_cases xR
  fin_cases xL
  fin_cases yR
  fin_cases yL
  simp only [sectorEta, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    PhysicalSectorFactorization.neighboringOperator_apply]
  simp_rw [sectorTensorL_hayashiData, sectorTensorR_hayashiData]

/-- The nonzero rectangular remainder survives the exact Hayashi/tail/inverse-map
provenance. Thus the arbitrary-factorization boundary isolated previously is
removed for this witness; the separate formalization of SAL is not asserted
here.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1484--1499. -/
theorem inverseMap_provenance_preserves_rectangular_remainder :
    (∀ k h, inverseMapFactorization.neighboringOperator k h =
      factorization.neighboringOperator k h) ∧
    rightPairing * (1 - leftPairing * rightPairing) * leftPairing ≠ 0 :=
  ⟨inverseMapFactorization_neighboringOperator, rectangular_remainder_ne_zero⟩

end MPOTensor.ActiveSectorSpanningCounterexample
