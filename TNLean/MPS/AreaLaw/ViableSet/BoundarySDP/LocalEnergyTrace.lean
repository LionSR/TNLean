/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedOverlapTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergyBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergyInputBounds

/-!
# Recorded arithmetic for local two-site matrix elements

A matrix-unit term combines a weighted overlap with its local operator
coefficient. Two levels of finite sums record the resulting local Hamiltonian
matrix element and bound the heights of its intermediate rational operations.
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- Compute one product-operator matrix element and multiply it by a local
Gaussian-rational coefficient. -/
def weightedMatrixElementTerm {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (weight : ℚ × ℚ) :
    Arithmetic (ℚ × ℚ) := do
  let overlap ← weightedOverlapOfRationalParameters
    A B capA capB PA PB W
  complexMul weight overlap

theorem erase_weightedMatrixElementTerm {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (weight : ℚ × ℚ) :
    erase (weightedMatrixElementTerm A B capA capB PA PB W weight) =
      RationalLocalEnergyCost.weightedMatrixElementTerm A B capA capB PA PB W weight := by
  simp only [weightedMatrixElementTerm, RationalLocalEnergyCost.weightedMatrixElementTerm,
    weightedOverlapOfRationalParameters,
    RationalGramContractionCost.weightedOverlapOfRationalParameters,
    weightedInputSites, erase_bind, erase_weightedContract, erase_complexMul]

/-- Evaluate the matrix-unit expansion of a rational two-site observable.
Each of the `q⁴` terms computes its weighted overlap once before accumulation. -/
def twoSiteMatrixElementOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) : Arithmetic (ℚ × ℚ) :=
  sumFin ((q * q) * (q * q)) fun j ↦
    let uv : Fin (q * q) × Fin (q * q) := finProdFinEquiv.symm j
    let ab : Fin q × Fin q := finProdFinEquiv.symm uv.1
    let cd : Fin q × Fin q := finProdFinEquiv.symm uv.2
    weightedMatrixElementTerm A B capA capB PA PB
      (twoSiteMatrixUnitCodeFactors p r ab.1 ab.2 cd.1 cd.2)
      (K (ab.1, cd.1) (ab.2, cd.2))

theorem erase_twoSiteMatrixElement {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    erase (twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K) =
      RationalLocalEnergyCost.twoSiteMatrixElementOfRationalParameters
        A B capA capB PA PB p r K := by
  simp only [twoSiteMatrixElementOfRationalParameters,
    RationalLocalEnergyCost.twoSiteMatrixElementOfRationalParameters, erase_sumFin,
    erase_weightedMatrixElementTerm]

/-- Evaluate and accumulate the matrix elements of a finite family of local
two-site terms, computing each local contribution once. -/
def matrixElementOfLocalTerms {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    Arithmetic (ℚ × ℚ) :=
  sumFin m fun i ↦
    twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i)

theorem erase_matrixElementOfLocalTerms {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    erase (matrixElementOfLocalTerms A B capA capB PA PB p r K) =
      RationalLocalEnergyCost.matrixElementOfLocalTerms A B capA capB PA PB p r K := by
  simp only [matrixElementOfLocalTerms, RationalLocalEnergyCost.matrixElementOfLocalTerms,
    erase_sumFin, erase_twoSiteMatrixElement]

theorem localTerms_value_length {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    let x := matrixElementOfLocalTerms A B capA capB PA PB p r K
    x.run.1 = OBCChainTensor.matrixElementOfLocalTerms A B capA capB PA PB p r K ∧
      x.run.2.length = m * (q ^ 4 * (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 8) + 2) := by
  apply value_length_of_run_erase
  rw [erase_matrixElementOfLocalTerms, RationalLocalEnergyCost.run_matrixElementOfLocalTerms]

section CommonData

variable {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (hM : 0 < M) (hC : 1 ≤ C)
    (hcapA : HasGaussianIntegerDenominator M (decodeRationalComplex capA))
    (hcapB : HasGaussianIntegerDenominator M (decodeRationalComplex capB))
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hcapAnorm : ‖decodeRationalComplex capA‖ ≤ (C : ℝ))
    (hcapBnorm : ‖decodeRationalComplex capB‖ ≤ (C : ℝ))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))

include hM hC hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm

def localWeightedTermHeight (q Da Db n M C : ℕ) : ℕ :=
  let V := M ^ (3 * n + 2) * max 1 (C ^ 2 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n)
  max (weightedOverlapHeightBound q Da Db n M C) (2 * (max (M * max 1 C) V) ^ 4)

/-- The local coefficient multiply adds six records after the matrix-unit overlap. -/
theorem localWeightedTerm_maxHeight_le (p r : Fin n) (a b c d : Fin q) (weight : ℚ × ℚ)
    (hw : HasGaussianIntegerDenominator M (decodeRationalComplex weight))
    (hn : ‖decodeRationalComplex weight‖ ≤ (C : ℝ)) :
    maxHeight (weightedMatrixElementTerm A B capA capB PA PB
      (twoSiteMatrixUnitCodeFactors p r a b c d) weight).run.2 ≤
      localWeightedTermHeight q Da Db n M C := by
  let W := twoSiteMatrixUnitCodeFactors p r a b c d
  have hf := twoSiteMatrixUnitCodeFactors_bounds p r a b c d hM hC
  have hv := OBCChainTensor.weightedOverlapOfRationalParameters_bounds A B capA capB PA PB W hM
    hcapA hcapB hPA hPB (fun j s t ↦ (hf j s t).1) hcapAnorm hcapBnorm hPAnorm hPBnorm
    (fun j s t ↦ (hf j s t).2)
  have ht := weightedOverlap_maxHeight_le A B PA PB W hM hPA hPB (fun j s t ↦ (hf j s t).1)
    hPAnorm hPBnorm (fun j s t ↦ (hf j s t).2) capA capB
    (hcapA.height_of_norm_le hcapAnorm) (hcapB.height_of_norm_le hcapBnorm)
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  simp only [weightedMatrixElementTerm, run_bind, List.mem_append,
    (weightedOverlap_value_length ..).1] at hop
  rcases hop with h | h
  · exact le_max_of_le_left ((maxHeight_le_iff _ _).mp ht op h)
  · exact le_max_of_le_right ((maxHeight_le_iff _ _).mp
      (complexMul_maxHeight_le weight _ ((hw.height_of_norm_le hn).mono (le_max_left ..))
        ((hv.1.height_of_norm_le hv.2.1).mono (le_max_right ..))) op h)

/-- Uniform record height for the matrix-unit expansion, including each prefix addition. -/
theorem twoSite_maxHeight_le (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K s u)))
    (hnK : ∀ s u, ‖decodeRationalComplex (K s u)‖ ≤ (C : ℝ)) :
    let R := C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n
    let S := M ^ (3 * n + 3) * max 1 (q ^ 4 * R)
    maxHeight (twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K).run.2 ≤
      max (localWeightedTermHeight q Da Db n M C) (2 * S ^ 2) := by
  intro R S
  have hterms (a b c d : Fin q) := RationalLocalEnergyCost.weightedMatrixElementTerm_bounds
    A B capA capB PA PB hM hC hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm
    p r a b c d (K (a, c) (b, d)) (hK _ _) (hnK _ _)
  have hv (a b c d : Fin q) := congrArg (fun x ↦ (WriterT.run x).1)
    (erase_weightedMatrixElementTerm A B capA capB PA PB
      (twoSiteMatrixUnitCodeFactors p r a b c d) (K (a, c) (b, d)))
  simp only [run_erase] at hv
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  apply sumFin_operation_height_le _ (pow_pos hM (3 * n + 3)) (C := R) _ _ _ _ op hop
  · intro i
    rw [hv]
    exact (hterms _ _ _ _).1
  · intro i
    rw [hv]
    exact (hterms _ _ _ _).2.1
  · intro i
    exact localWeightedTerm_maxHeight_le A B capA capB PA PB hM hC hcapA hcapB hPA hPB
      hcapAnorm hcapBnorm hPAnorm hPBnorm p r _ _ _ _ _ (hK _ _) (hnK _ _)
  · simp [S, pow_succ, Nat.mul_assoc]

/-- Height for all inner and outer sums of the local Hamiltonian. -/
def localTermsHeight (q Da Db n m M C : ℕ) : ℕ :=
  let R := q ^ 4 * (C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n)
  let N := M ^ (3 * n + 3)
  max (max (localWeightedTermHeight q Da Db n M C) (2 * (N * max 1 R) ^ 2))
    (2 * (N * max 1 (m * R)) ^ 2)

theorem localTerms_maxHeight_le {m : ℕ} (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ i s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K i s u)))
    (hnK : ∀ i s u, ‖decodeRationalComplex (K i s u)‖ ≤ (C : ℝ)) :
    maxHeight (matrixElementOfLocalTerms A B capA capB PA PB p r K).run.2 ≤
      localTermsHeight q Da Db n m M C := by
  let R := q ^ 4 * (C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n)
  have hb (i : Fin m) := RationalLocalEnergyCost.twoSiteMatrixElementOfRationalParameters_bounds
    A B capA capB PA PB hM hC hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm
    (p i) (r i) (K i) (hK i) (hnK i)
  have hv (i : Fin m) := congrArg (fun x ↦ (WriterT.run x).1)
    (erase_twoSiteMatrixElement A B capA capB PA PB (p i) (r i) (K i))
  simp only [run_erase, RationalLocalEnergyCost.run_twoSiteMatrixElementOfRationalParameters] at hv
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  apply sumFin_operation_height_le _ (pow_pos hM (3 * n + 3)) (C := R) _ _ _ le_rfl op hop
  · intro i
    rw [hv]
    exact (hb i).1
  · intro i
    rw [hv]
    exact (hb i).2.1
  · exact fun i ↦ twoSite_maxHeight_le A B capA capB PA PB hM hC hcapA hcapB hPA hPB
      hcapAnorm hcapBnorm hPAnorm hPBnorm (p i) (r i) (K i) (hK i) (hnK i)

theorem localTerms_schoolbookCharge_le {m : ℕ} (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ i s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K i s u)))
    (hnK : ∀ i s u, ‖decodeRationalComplex (K i s u)‖ ≤ (C : ℝ)) :
    schoolbookCharge (matrixElementOfLocalTerms A B capA capB PA PB p r K).run.2 ≤
      (m * (q ^ 4 * (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 8) + 2)) *
        rationalSchoolbookOperationCost (Nat.log2 (localTermsHeight q Da Db n m M C) + 1) := by
  have h := schoolbookCharge_le_of_maxHeight_le
    (localTerms_maxHeight_le A B capA capB PA PB hM hC hcapA hcapB hPA hPB
      hcapAnorm hcapBnorm hPAnorm hPBnorm p r K hK hnK)
  rwa [(localTerms_value_length A B capA capB PA PB p r K).2] at h

end CommonData



variable {q Da Db n m H : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hcapA : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capA))
    (hcapB : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex capB))
    (hPA : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (PB e)))
    (hK : ∀ i a b, HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex (K i a b)))

include hcapA hcapB hPA hPB hK

/-- Input coordinate heights alone bound every record, with one common denominator
chosen for both chains, both caps and all operator coefficients. -/
theorem localTerms_maxHeight_of_inputHeight :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4
    maxHeight (matrixElementOfLocalTerms A B capA capB PA PB p r K).run.2 ≤
      localTermsHeight q Da Db n m (H ^ (2 * P)) (2 * H) := by
  intro P
  obtain ⟨M, hM, hbound, hcA, hcB, ha, hb, hk⟩ :=
    OBCChainTensor.exists_common_localEnergy_parameter_denominator A B capA capB PA PB K
      hcapA hcapB hPA hPB hK
  have hH : 1 ≤ H := by
    obtain ⟨x, _y, _hxy, hx, _hy⟩ := hcapA
    exact x.den_pos.trans_le ((den_le_rationalHeight x).trans hx)
  have hC : 1 ≤ 2 * H := by omega
  have h := localTerms_maxHeight_le (C := 2 * H)
    A B capA capB PA PB hM hC hcA hcB ha hb
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcapA.norm_le_two_mul)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcapB.norm_le_two_mul)
    (fun e ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hPA e).norm_le_two_mul)
    (fun e ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hPB e).norm_le_two_mul)
    p r K hk
    (fun i s t ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hK i s t).norm_le_two_mul)
  apply h.trans
  have hle : M ≤ H ^ (2 * P) := hbound
  unfold localTermsHeight localWeightedTermHeight weightedOverlapHeightBound
  dsimp only
  gcongr

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
