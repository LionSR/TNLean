/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBounds

/-!
# Denominators and norms of capped weighted overlaps

The two scalar caps contribute two further powers of the common input
denominator to the sequential mixed-transfer contraction. These estimates
concern the rational value actually computed, without any normalization
assumption on the tensor entries.

## References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
- Nature Physics 11 (2015), 566–569, supplementary information.
-/

namespace TNLean.MPS.AreaLaw.OBCChainTensor

/-- Including both scalar caps gives common denominator `M^(3n+2)` and
norm at most `C² (Da Db q² C³)^n` for the actual rational weighted overlap. -/
theorem weightedOverlapOfRationalParameters_bounds {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hcapA : HasGaussianIntegerDenominator M (decodeRationalComplex capA))
    (hcapB : HasGaussianIntegerDenominator M (decodeRationalComplex capB))
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)))
    (hcapAnorm : ‖decodeRationalComplex capA‖ ≤ (C : ℝ))
    (hcapBnorm : ‖decodeRationalComplex capB‖ ≤ (C : ℝ))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))
    (hWnorm : ∀ p s t, ‖decodeRationalComplex (W p s t)‖ ≤ (C : ℝ)) :
    let z := weightedOverlapOfRationalParameters A B capA capB PA PB W
    let R := C ^ 2 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n
    HasGaussianIntegerDenominator (M ^ (3 * n + 2)) (decodeRationalComplex z) ∧
      ‖decodeRationalComplex z‖ ≤ (R : ℝ) ∧
      rationalHeight z.1 ≤ M ^ (3 * n + 2) * max 1 R ∧
      rationalHeight z.2 ≤ M ^ (3 * n + 2) * max 1 R := by
  intro z R
  have hrow := weightedTransfer_prefix_bounds A B PA PB W (Nat.le_refl n) hM hPA hPB hW
    hPAnorm hPBnorm hWnorm
  have htake : (weightedTransferSiteList A B PA PB W).take n =
      weightedTransferSiteList A B PA PB W :=
    List.take_of_length_le (by simp [weightedTransferSiteList])
  rw [htake] at hrow
  let j := finProdFinEquiv
    ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
  have hden : HasGaussianIntegerDenominator (M ^ (3 * n + 2))
      (decodeRationalComplex z) := by
    have h := (hcapA.star.mul hcapB).mul (hrow j).1
    have hp : M * M * M ^ (3 * n) = M ^ (3 * n + 2) := by
      simp only [pow_add, pow_two]
      ac_rfl
    rw [hp] at h
    simpa only [z, weightedOverlapOfRationalParameters,
      RationalComplexCode.decode_mul, RationalComplexCode.decode_conj] using h
  have hnorm : ‖decodeRationalComplex z‖ ≤ (R : ℝ) := by
    simp only [z, weightedOverlapOfRationalParameters, RationalComplexCode.decode_mul,
      RationalComplexCode.decode_conj, norm_mul, norm_star]
    calc
      _ ≤ (C : ℝ) * C * ((Da * Db * (q ^ 2 * C ^ 3)) ^ n : ℕ) := by
        gcongr
        exact (hrow j).2.1
      _ = (R : ℝ) := by simp [R, pow_two]
  exact ⟨hden, hnorm,
    RationalComplexCode.coordinate_heights_of_common_denominator _ hden hnorm⟩

end TNLean.MPS.AreaLaw.OBCChainTensor
