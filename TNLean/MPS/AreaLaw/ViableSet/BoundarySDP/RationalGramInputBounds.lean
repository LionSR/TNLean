/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContraction
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalStorage
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CommonDenominator
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBinaryBounds

/-!
# Common denominators for the actual weighted-contraction inputs

Clear the finitely many scalar caps, local tensor entries, and one-site
weights together. The denominator exponent depends on the stored input
dimensions. It is independent of the number of physical configurations.
-/

namespace TNLean.MPS.AreaLaw

/-- Height-bounded rational inputs to weighted contraction have one common
denominator, bounded by the number of actual stored complex parameters. -/
theorem OBCChainTensor.exists_common_weighted_parameter_denominator
    {q Da Db n H : ℕ} (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (W p s t))) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ H ^ (2 * (2 + n * q * Da ^ 2 + n * q * Db ^ 2 + n * q ^ 2)) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capA) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capB) ∧
      (∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e))) ∧
      (∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e))) ∧
      ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)) := by
  classical
  let I := Fin 2 ⊕ (OBCChainTensor.ParameterIndex A ⊕ OBCChainTensor.ParameterIndex B) ⊕
    (Fin n × Fin q × Fin q)
  let z : I → ℂ := fun e ↦ match e with
    | Sum.inl c => if c = 0 then decodeRationalComplex capA else decodeRationalComplex capB
    | Sum.inr (Sum.inl (Sum.inl a)) => decodeRationalComplex (PA a)
    | Sum.inr (Sum.inl (Sum.inr b)) => decodeRationalComplex (PB b)
    | Sum.inr (Sum.inr p) => decodeRationalComplex (W p.1 p.2.1 p.2.2)
  have hz : ∀ e, HasRationalComplexCoordinatesOfHeight H (z e) := by
    intro e
    rcases e with c | ((a | b) | p)
    · dsimp only [z]
      split_ifs
      · exact hcapA
      · exact hcapB
    · exact hPA a
    · exact hPB b
    · exact hW p.1 p.2.1 p.2.2
  obtain ⟨M, hM, hbound, hclear⟩ := exists_common_gaussianInteger_denominator hz
  have hH : 1 ≤ H := by
    obtain ⟨x, _y, _hxy, hx, _hy⟩ := hcapA
    exact x.den_pos.trans_le ((den_le_rationalHeight x).trans hx)
  have hcard : Fintype.card I ≤ 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + n * q ^ 2 := by
    dsimp only [I]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hA := OBCChainTensor.card_parameterIndex_le A
    have hB := OBCChainTensor.card_parameterIndex_le B
    nlinarith only [hA, hB]
  refine ⟨M, hM, hbound.trans (Nat.pow_le_pow_right hH (Nat.mul_le_mul_left 2 hcard)),
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [z, ↓reduceIte] using hclear (Sum.inl (0 : Fin 2))
  · have hne : (1 : Fin 2) ≠ 0 := by decide
    simpa only [z, hne, ↓reduceIte] using hclear (Sum.inl (1 : Fin 2))
  · exact fun e ↦ hclear (Sum.inr (Sum.inl (Sum.inl e)))
  · exact fun e ↦ hclear (Sum.inr (Sum.inl (Sum.inr e)))
  · exact fun p s t ↦ hclear (Sum.inr (Sum.inr (p, s, t)))

/-- A single bounded-height input gives bounds at every actual weighted
contraction prefix. The same denominator also clears both scalar caps. -/
theorem OBCChainTensor.exists_weightedTransfer_prefix_bounds_of_height
    {q Da Db n H : ℕ} (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (W p s t))) :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + n * q ^ 2
    ∃ M : ℕ, 0 < M ∧ M ≤ H ^ (2 * P) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capA) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capB) ∧
      ∀ t ≤ n,
        let j₀ := finProdFinEquiv
          ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
        let row := RationalRectMatrixCode.rowProduct (Pi.single j₀ (1, 0))
          ((OBCChainTensor.weightedTransferSiteList A B PA PB W).take t)
        let R : ℕ := (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ t
        ∀ j, HasGaussianIntegerDenominator (M ^ (3 * t)) (decodeRationalComplex (row j)) ∧
          ‖decodeRationalComplex (row j)‖ ≤ (R : ℝ) ∧
          rationalHeight (row j).1 ≤ H ^ (6 * P * t) * max 1 R ∧
          rationalHeight (row j).2 ≤ H ^ (6 * P * t) * max 1 R := by
  intro P
  obtain ⟨M, hM, hbound, hcA, hcB, ha, hb, hw⟩ :=
    OBCChainTensor.exists_common_weighted_parameter_denominator A B capA capB PA PB W
      hcapA hcapB hPA hPB hW
  refine ⟨M, hM, hbound, hcA, hcB, ?_⟩
  intro t ht j₀ row R j
  have hprefix := OBCChainTensor.weightedTransfer_prefix_bounds (C := 2 * H)
    A B PA PB W ht hM ha hb hw
    (fun e ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hPA e).norm_le_two_mul)
    (fun e ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hPB e).norm_le_two_mul)
    (fun p s t ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hW p s t).norm_le_two_mul)
  have hpower : M ^ (3 * t) ≤ H ^ (6 * P * t) := by
    calc
      _ ≤ (H ^ (2 * P)) ^ (3 * t) := Nat.pow_le_pow_left hbound _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  refine ⟨(hprefix j).1, (hprefix j).2.1, ?_, ?_⟩
  · exact (hprefix j).2.2.1.trans (Nat.mul_le_mul_right _ hpower)
  · exact (hprefix j).2.2.2.trans (Nat.mul_le_mul_right _ hpower)

/-- The actual rational coordinates of every weighted prefix have a polynomial
binary exponent when the stored local input coordinates have height at most `2^h`. -/
theorem OBCChainTensor.weightedTransfer_prefix_coordinate_heights_two_pow
    {q Da Db n H h : ℕ} (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (W p s t)))
    (hH : H ≤ 2 ^ h) (t : ℕ) (ht : t ≤ n) :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + n * q ^ 2
    let j₀ := finProdFinEquiv
      ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
    let row := RationalRectMatrixCode.rowProduct (Pi.single j₀ (1, 0))
      ((OBCChainTensor.weightedTransferSiteList A B PA PB W).take t)
    ∀ j, rationalHeight (row j).1 ≤
        2 ^ ((6 * h * P + Da * Db + 2 * q + 3 * h + 3) * t) ∧
      rationalHeight (row j).2 ≤
        2 ^ ((6 * h * P + Da * Db + 2 * q + 3 * h + 3) * t) := by
  intro P j₀ row j
  obtain ⟨_M, _hM, _hbound, _hcA, _hcB, hprefix⟩ :=
    OBCChainTensor.exists_weightedTransfer_prefix_bounds_of_height A B capA capB PA PB W
      hcapA hcapB hPA hPB hW
  have hbound := weightedTransfer_prefix_height_le_two_pow
    (P := P) (t := t) (Da := Da) (Db := Db) (q := q) hH
  exact ⟨(hprefix t ht j).2.2.1.trans hbound, (hprefix t ht j).2.2.2.trans hbound⟩

end TNLean.MPS.AreaLaw
