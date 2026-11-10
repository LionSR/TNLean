/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergyBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergyInputBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.LocalEnergyBinaryBounds

/-!
# Heights of actual rational local-energy values

One common denominator clears the scalar caps, the two rational MPS tensors,
and all local operator coefficients. The resulting denominator and norm
estimates bound the actual fractions returned at every prefix of the local
energy sum. If the input heights are bounded by a power of two, the output
coordinate heights have an explicit polynomial binary exponent, uniformly
over all prefix lengths.

## References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
- Nature Physics 11 (2015), 566–569, supplementary information.
-/

namespace TNLean.MPS.AreaLaw.RationalLocalEnergyCost

section InputData

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

/-- Input coordinate heights give one common denominator and bounds on every
actual local-term accumulator. The denominator exponent counts the two caps,
both tensor parameter families, and all local operator coefficients. -/
theorem exists_matrixElementOfLocalTerms_prefix_bounds_of_height :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4
    let R := q ^ 4 * ((2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n)
    ∃ M : ℕ, 0 < M ∧ M ≤ H ^ (2 * P) ∧
      ∀ a (ha : a ≤ m),
        let z := (RationalGramContractionCost.sumFin a (fun j ↦
          let i := Fin.castLE ha j
          twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i))).run.1
        HasGaussianIntegerDenominator (M ^ (3 * n + 3)) (decodeRationalComplex z) ∧
          ‖decodeRationalComplex z‖ ≤ (a * R : ℕ) ∧
          rationalHeight z.1 ≤ H ^ (2 * P * (3 * n + 3)) * max 1 (a * R) ∧
          rationalHeight z.2 ≤ H ^ (2 * P * (3 * n + 3)) * max 1 (a * R) := by
  intro P R
  obtain ⟨M, hM, hbound, hcA, hcB, ha, hb, hk⟩ :=
    OBCChainTensor.exists_common_localEnergy_parameter_denominator A B capA capB PA PB K
      hcapA hcapB hPA hPB hK
  have hH : 1 ≤ H := by
    obtain ⟨x, _y, _hxy, hx, _hy⟩ := hcapA
    exact x.den_pos.trans_le ((den_le_rationalHeight x).trans hx)
  have hC : 1 ≤ 2 * H := by omega
  have hpower : M ^ (3 * n + 3) ≤ H ^ (2 * P * (3 * n + 3)) := by
    calc
      _ ≤ (H ^ (2 * P)) ^ (3 * n + 3) := Nat.pow_le_pow_left hbound _
      _ = _ := by rw [← pow_mul]
  refine ⟨M, hM, hbound, ?_⟩
  intro a hat z
  have hprefix := matrixElementOfLocalTerms_prefix_bounds (C := 2 * H)
    A B capA capB PA PB hM hC hcA hcB ha hb
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcapA.norm_le_two_mul)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcapB.norm_le_two_mul)
    (fun e ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hPA e).norm_le_two_mul)
    (fun e ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hPB e).norm_le_two_mul)
    p r K hk
    (fun i s t ↦ by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hK i s t).norm_le_two_mul)
    hat
  exact ⟨hprefix.1, hprefix.2.1,
    hprefix.2.2.1.trans (Nat.mul_le_mul_right _ hpower),
    hprefix.2.2.2.trans (Nat.mul_le_mul_right _ hpower)⟩

/-- Every actual local-term accumulator has a polynomial binary coordinate
height bound, with an exponent independent of the prefix length. -/
theorem matrixElementOfLocalTerms_prefix_coordinate_heights_two_pow {h : ℕ}
    (hH : H ≤ 2 ^ h) (a : ℕ) (ha : a ≤ m) :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4
    let E := 6 * h * P * (n + 1) + m * q ^ 2 + 2 * q + 3 * h + 3 +
      (Da * Db + 2 * q + 3 * h + 3) * n
    let z := (RationalGramContractionCost.sumFin a (fun j ↦
      let i := Fin.castLE ha j
      twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i))).run.1
    rationalHeight z.1 ≤ 2 ^ E ∧ rationalHeight z.2 ≤ 2 ^ E := by
  intro P E z
  obtain ⟨_M, _hM, _hbound, hprefix⟩ :=
    exists_matrixElementOfLocalTerms_prefix_bounds_of_height A B capA capB PA PB p r K
      hcapA hcapB hPA hPB hK
  have hnorm : a * (q ^ 4 * ((2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n)) ≤
      m * q ^ 4 * (2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n := by
    calc
      _ ≤ m * (q ^ 4 * ((2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n)) :=
        Nat.mul_le_mul_right _ ha
      _ = _ := by ring
  have hbudget : H ^ (2 * P * (3 * n + 3)) *
      max 1 (a * (q ^ 4 * ((2 * H) ^ 3 * (Da * Db * (q ^ 2 * (2 * H) ^ 3)) ^ n))) ≤
      2 ^ E :=
    (Nat.mul_le_mul_left _ (max_le_max_left 1 hnorm)).trans
      (localEnergy_height_le_two_pow hH)
  exact ⟨(hprefix a ha).2.2.1.trans hbudget, (hprefix a ha).2.2.2.trans hbudget⟩

/-- The fractions in the actual full rational local-energy output have a
polynomial binary height exponent determined entirely by the input heights,
the number of local terms, and the chain and matrix dimensions. -/
theorem matrixElementOfLocalTerms_coordinate_heights_two_pow {h : ℕ}
    (hH : H ≤ 2 ^ h) :
    let P := 2 + n * q * Da ^ 2 + n * q * Db ^ 2 + m * q ^ 4
    let E := 6 * h * P * (n + 1) + m * q ^ 2 + 2 * q + 3 * h + 3 +
      (Da * Db + 2 * q + 3 * h + 3) * n
    let z := OBCChainTensor.matrixElementOfLocalTerms A B capA capB PA PB p r K
    rationalHeight z.1 ≤ 2 ^ E ∧ rationalHeight z.2 ≤ 2 ^ E := by
  have hbound := matrixElementOfLocalTerms_prefix_coordinate_heights_two_pow
    A B capA capB PA PB p r K hcapA hcapB hPA hPB hK hH m (Nat.le_refl m)
  simp only [Fin.castLE_refl] at hbound
  rw [← matrixElementOfLocalTerms] at hbound
  simpa only [run_matrixElementOfLocalTerms] using hbound

end InputData

end TNLean.MPS.AreaLaw.RationalLocalEnergyCost
