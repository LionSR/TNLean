/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ActiveSectorSpanningCounterexample
import TNLean.MPS.MPDO.InverseMapPhysicalSectorFactorization

/-!
# Inverse-map provenance of the four-sector classical tensor

This file supplies the explicit three-site Hayashi decomposition needed to
compare the inverse-map construction in Appendix C.2 of arXiv:1606.00608 with
the four-sector classical tensor in
`TNLean.MPS.MPDO.ActiveSectorSpanningCounterexample`.

The source uses the inverse map only through its contraction identity at lines
1415--1438.  It does not derive linear independence of the closed sector
tensors or the rectangular vanishing used after Lemma C.4.

## References

* arXiv:1606.00608, Appendix C.2, Lemma C.4, lines 1406--1471.
* arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ActiveSectorSpanningCounterexample

private noncomputable abbrev traceMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  rightPairing * leftPairing

/-- The left conditional density in the classical Markov decomposition. -/
noncomputable def markovLeft (k : Fin 4) :
    Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) ℂ :=
  Matrix.diagonal fun x => traceMatrix x.1 k

/-- The right conditional density in the classical Markov decomposition. -/
noncomputable def markovRight (k : Fin 4) :
    Matrix (Fin 1 × Fin 4) (Fin 1 × Fin 4) ℂ :=
  Matrix.diagonal fun x => traceMatrix k x.2

/-- The normalized three-site classical Markov state. -/
noncomputable def threeSiteState :
    Matrix (Fin 4 × Fin 4 × Fin 4) (Fin 4 × Fin 4 × Fin 4) ℂ :=
  Matrix.diagonal fun x =>
    (1 / 4 : ℂ) * traceMatrix x.1 x.2.1 * traceMatrix x.2.1 x.2.2

private lemma right_dot_left (i j : Fin 4) :
    (fun alpha => rightPairing i alpha) ⬝ᵥ (fun beta => leftPairing beta j) =
      traceMatrix i j := by
  rfl

private lemma tail_contraction (i k : Fin 4) :
    (fun beta => leftPairing beta i) ⬝ᵥ
        Matrix.vecMul (fun alpha => rightPairing k alpha)
          (leftPairing * rightPairing) =
      (1 / 4 : ℂ) := by
  fin_cases i <;> fin_cases k <;>
    norm_num [leftPairing, rightPairing, dotProduct, Matrix.vecMul,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

private lemma trace_sectorMatrix_product (i j k : Fin 4) :
    Matrix.trace
        (sectorMatrix i * sectorMatrix j * sectorMatrix k *
          (leftPairing * rightPairing)) =
      (1 / 4 : ℂ) * traceMatrix i j * traceMatrix j k := by
  rw [sectorMatrix, sectorMatrix, sectorMatrix]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  simp only [smul_dotProduct, right_dot_left]
  rw [Matrix.smul_vecMul, dotProduct_smul, tail_contraction]
  simp only [smul_eq_mul]
  ring

lemma markovLeft_posSemidef (k : Fin 4) : (markovLeft k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro x
  obtain ⟨i, u⟩ := x
  fin_cases u
  change 0 ≤ (rightPairing * leftPairing) i k
  rw [rightPairing_mul_leftPairing]
  fin_cases i <;> fin_cases k <;> norm_num [Complex.nonneg_iff]

lemma markovRight_posSemidef (k : Fin 4) : (markovRight k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro x
  obtain ⟨u, i⟩ := x
  fin_cases u
  change 0 ≤ (rightPairing * leftPairing) k i
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;> fin_cases i <;> norm_num [Complex.nonneg_iff]

lemma trace_markovLeft (k : Fin 4) : (markovLeft k).trace = 1 := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [markovLeft, Fin.sum_univ_one]
  change (∑ i : Fin 4, (rightPairing * leftPairing) i k) = 1
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;>
    norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

lemma trace_markovRight (k : Fin 4) : (markovRight k).trace = 1 := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [markovRight, Fin.sum_univ_one]
  change (∑ i : Fin 4, (rightPairing * leftPairing) k i) = 1
  rw [rightPairing_mul_leftPairing]
  fin_cases k <;>
    norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The classical three-site state has the four one-dimensional middle
sectors dictated by the four physical symbols. -/
noncomputable def etaStructure : EtaStructure threeSiteState where
  m := 4
  dL := fun _ => 1
  dR := fun _ => 1
  decompB := sectorEquiv
  U_B := ⟨1, one_mem _⟩
  p := p
  hp_nonneg := p_nonneg
  hp_sum := sum_p
  ρ_left := markovLeft
  ρ_right := markovRight
  hρ_left_dm := fun k => ⟨markovLeft_posSemidef k, trace_markovLeft k⟩
  hρ_right_dm := fun k => ⟨markovRight_posSemidef k, trace_markovRight k⟩
  h_state := by
    ext x y
    obtain ⟨a, ⟨⟨k, ⟨l, r⟩⟩, c⟩⟩ := x
    obtain ⟨a', ⟨⟨k', ⟨l', r'⟩⟩, c'⟩⟩ := y
    fin_cases l
    fin_cases r
    fin_cases l'
    fin_cases r'
    simp [HayashiMarkov.abcEquiv, HayashiMarkov.liftB, threeSiteState,
      HayashiMarkov.blockState_apply, sectorEquiv, markovLeft, markovRight]
    by_cases haa : a = a' <;> by_cases hkk : k = k' <;> by_cases hcc : c = c'
    all_goals simp [haa, hkk, hcc, p]

/-- The classical Markov state is the three-site closure of the tensor against
the idempotent virtual tail `LQ`. -/
lemma isThreeSiteClosure_threeSiteState :
    IsThreeSiteClosure tensor (leftPairing * rightPairing) threeSiteState := by
  intro i₁ i₂ i₃ j₁ j₂ j₃
  by_cases h₁ : i₁ = j₁
  · subst j₁
    by_cases h₂ : i₂ = j₂
    · subst j₂
      by_cases h₃ : i₃ = j₃
      · subst j₃
        simp only [threeSiteState, Matrix.diagonal_apply_eq]
        rw [tensor, if_pos rfl, tensor, if_pos rfl, tensor, if_pos rfl]
        exact trace_sectorMatrix_product i₁ i₂ i₃ |>.symm
      · rw [threeSiteState, Matrix.diagonal_apply_ne]
        · simp [tensor, h₃]
        · exact fun h => h₃ (congrArg (fun x => x.2.2) h)
    · rw [threeSiteState, Matrix.diagonal_apply_ne]
      · simp [tensor, h₂]
      · exact fun h => h₂ (congrArg (fun x => x.2.1) h)
  · rw [threeSiteState, Matrix.diagonal_apply_ne]
    · simp [tensor, h₁]
    · exact fun h => h₁ (congrArg Prod.fst h)

private lemma inverseTensor_diagonal_expansion (alpha beta : Fin 2) :
    ∑ i : Fin 4,
        inverseTensor tensor tensor_isInjective (finProdFinEquiv (i, i)) alpha beta •
          sectorMatrix i =
      Matrix.single alpha beta (1 : ℂ) := by
  have h := inverseTensor_spec tensor tensor_isInjective alpha beta
  rw [← Equiv.sum_comp finProdFinEquiv] at h
  rw [Fintype.sum_prod_type] at h
  simpa only [MPOTensor.toMPSTensor, tensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_pos] using h

private lemma hayashiInverseLeft_eq (beta : Fin 2) (k : Fin 4)
    (l l' : Fin (etaStructure.dL k)) :
    hayashiInverseLeft tensor tensor_isInjective etaStructure 0 beta k l l' =
      4 * leftPairing beta k := by
  change Fin 1 at l l'
  fin_cases l
  fin_cases l'
  have h := inverseTensor_diagonal_expansion 0 beta
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  fin_cases beta <;> fin_cases k
  all_goals
    norm_num [sectorMatrix, leftPairing, rightPairing, Fin.sum_univ_four,
      Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three] at h00 h01
    simp [hayashiInverseLeft, etaStructure, markovLeft, traceMatrix,
      leftPairing, rightPairing, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three];
      first | linear_combination h00 + 4 * h01 | linear_combination h00 - 4 * h01

private lemma hayashiInverseRight_eq (alpha : Fin 2) (k : Fin 4)
    (r r' : Fin (etaStructure.dR k)) :
    hayashiInverseRight tensor tensor_isInjective etaStructure alpha 0 k r r' =
      rightPairing k alpha := by
  change Fin 1 at r r'
  fin_cases r
  fin_cases r'
  have h := inverseTensor_diagonal_expansion alpha 0
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  fin_cases alpha <;> fin_cases k
  all_goals
    norm_num [sectorMatrix, leftPairing, rightPairing, Fin.sum_univ_four,
      Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three] at h00 h10
    simp [hayashiInverseRight, etaStructure, markovRight, traceMatrix,
      leftPairing, rightPairing, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three];
      first | linear_combination h00 + (1 / 8) * h10 |
        linear_combination h00 - (1 / 8) * h10

private lemma selectedTail_ne_zero :
    (leftPairing * rightPairing) 0 0 ≠ 0 := by
  rw [leftPairing_mul_rightPairing]
  norm_num

/-- For the four-sector tensor, the left factor constructed by the arbitrary
right inverse in Appendix C.2 is exactly the displayed left sector vector.

This is a provenance statement for this explicit tensor.  It does not assert
the general rank-one conclusion printed in Lemma C.5.

Source: arXiv:1606.00608, Appendix C.2, equation `Qketc`, lines 1415--1428,
and equation `formK`, lines 1434--1439. -/
theorem inverseMap_sectorTensorL_eq (k : Fin 4) (beta : Fin 2) :
    sectorTensorL tensor tensor_isInjective etaStructure
        (leftPairing * rightPairing) 0 0 k beta =
      factorization.leftTensor k beta := by
  ext l l'
  rw [sectorTensorL]
  simp only [Matrix.of_apply]
  rw [hayashiInverseLeft_eq]
  rw [leftPairing_mul_rightPairing]
  simp [etaStructure, p, factorization]

/-- For the four-sector tensor, the right factor constructed by the arbitrary
right inverse in Appendix C.2 is exactly the displayed right sector vector.

This is a provenance statement for this explicit tensor.  It does not assert
the general rank-one conclusion printed in Lemma C.5.

Source: arXiv:1606.00608, Appendix C.2, equation `Qketc`, lines 1415--1428,
and equation `formK`, lines 1434--1439. -/
theorem inverseMap_sectorTensorR_eq (k : Fin 4) (alpha : Fin 2) :
    sectorTensorR tensor tensor_isInjective etaStructure 0 k alpha =
      factorization.rightTensor k alpha := by
  ext r r'
  rw [sectorTensorR]
  simp only [Matrix.of_apply]
  rw [hayashiInverseRight_eq]
  rfl

/-- The inverse-map physical-sector factorization has exactly the displayed
left and right sector tensors for the four-sector classical example.

Thus the arbitrary choice of right inverse does not remove this example: the
inverse-map construction recovers its non-idempotent active-sector trace
matrix.  The theorem is deliberately restricted to the explicit tensor and
does not prove the paper's general rank-one inference.

Source: arXiv:1606.00608, Appendix C.2, lines 1415--1445. -/
theorem inverseMap_factorization_recovers_displayed_tensors :
    (∀ k beta,
      (inverseMapPhysicalSectorFactorization tensor tensor_isInjective
          (leftPairing * rightPairing) isThreeSiteClosure_threeSiteState
          etaStructure 0 0 selectedTail_ne_zero).leftTensor k beta =
        factorization.leftTensor k beta) ∧
    (∀ k alpha,
      (inverseMapPhysicalSectorFactorization tensor tensor_isInjective
          (leftPairing * rightPairing) isThreeSiteClosure_threeSiteState
          etaStructure 0 0 selectedTail_ne_zero).rightTensor k alpha =
        factorization.rightTensor k alpha) := by
  constructor
  · exact inverseMap_sectorTensorL_eq
  · exact inverseMap_sectorTensorR_eq

end MPOTensor.ActiveSectorSpanningCounterexample
