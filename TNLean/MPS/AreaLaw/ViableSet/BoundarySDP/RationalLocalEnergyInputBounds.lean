/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergy
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalStorage
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CommonDenominator

/-!
# Common denominators for local-energy inputs

The two rational MPS representations and all two-site coefficient matrices
form one finite family. Clearing its denominators gives one denominator
valid for every local term, so subsequent summation need not multiply
denominators belonging to different terms.

## References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
-/

namespace TNLean.MPS.AreaLaw

/-- All actual rational inputs of a finite local-energy calculation have
one common denominator. The exponent counts both caps, the stored tensor
entries, and the fourth-power many coefficients of each local term. -/
theorem OBCChainTensor.exists_common_localEnergy_parameter_denominator
    {q Da Db n m H : ℕ} (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hK : ∀ i a b, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (K i a b))) :
    ∃ M : ℕ, 0 < M ∧
      M ≤ H ^ (2 * (2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4)) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capA) ∧
      HasGaussianIntegerDenominator M (decodeRationalComplex capB) ∧
      (∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e))) ∧
      (∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e))) ∧
      ∀ i a b, HasGaussianIntegerDenominator M (decodeRationalComplex (K i a b)) := by
  classical
  let I := Fin 2 ⊕ (OBCChainTensor.ParameterIndex A ⊕ OBCChainTensor.ParameterIndex B) ⊕
    (Fin m × (Fin q × Fin q) × (Fin q × Fin q))
  let z : I → ℂ := fun e ↦ match e with
    | Sum.inl c => if c = 0 then decodeRationalComplex capA else decodeRationalComplex capB
    | Sum.inr (Sum.inl (Sum.inl a)) => decodeRationalComplex (PA a)
    | Sum.inr (Sum.inl (Sum.inr b)) => decodeRationalComplex (PB b)
    | Sum.inr (Sum.inr k) => decodeRationalComplex (K k.1 k.2.1 k.2.2)
  have hz : ∀ e, HasRationalComplexCoordinatesOfHeight H (z e) := by
    intro e
    rcases e with c | ((a | b) | k)
    · dsimp only [z]
      split_ifs
      · exact hcapA
      · exact hcapB
    · exact hPA a
    · exact hPB b
    · exact hK k.1 k.2.1 k.2.2
  obtain ⟨M, hM, hbound, hclear⟩ := exists_common_gaussianInteger_denominator hz
  have hH : 1 ≤ H := by
    obtain ⟨x, _y, _hxy, hx, _hy⟩ := hcapA
    exact x.den_pos.trans_le ((den_le_rationalHeight x).trans hx)
  have hcard : Fintype.card I ≤ 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4 := by
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
  · exact fun i a b ↦ hclear (Sum.inr (Sum.inr (i, a, b)))

end TNLean.MPS.AreaLaw
