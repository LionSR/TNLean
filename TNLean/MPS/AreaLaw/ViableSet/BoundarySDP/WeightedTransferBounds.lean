/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ContractionIntermediateBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContraction

/-!
# Intermediate bounds for weighted transfer contraction

Zero-padding preserves common denominators and entry norm bounds. Each weighted
transfer entry is a sum of squared physical-dimension many products of three
entries. The resulting bounds apply to the actual transfer-site list and every
materialized prefix row of its rational contraction.
-/

namespace TNLean.MPS.AreaLaw

/-- Zero has every positive Gaussian-integer denominator. -/
theorem HasGaussianIntegerDenominator.zero {M : ℕ} (hM : 0 < M) :
    HasGaussianIntegerDenominator M (0 : ℂ) := ⟨hM, ⟨0, by simp⟩⟩

/-- Complex conjugation preserves a common Gaussian-integer denominator. -/
theorem HasGaussianIntegerDenominator.star {M : ℕ} {z : ℂ}
    (hz : HasGaussianIntegerDenominator M z) :
    HasGaussianIntegerDenominator M (star z) := by
  obtain ⟨hM, a, ha⟩ := hz
  refine ⟨hM, ⟨Star.star a, ?_⟩⟩
  calc
    ((Star.star a : GaussianInt) : ℂ) = Star.star (a : ℂ) := GaussianInt.toComplex_star a
    _ = Star.star ((M : ℂ) * z) := congrArg Star.star ha
    _ = (M : ℂ) * Star.star z := by simp

namespace RationalRectMatrixCode

/-- Actual weighted transfer entries have denominator `M³` and norm bound
`q² C³` when both tensor families and the physical weight have denominator `M`
and entry norm at most `C`. -/
theorem weightedTransfer_bounds {q Da Db M C : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hA : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A s i j)))
    (hB : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (B s i j)))
    (hW : ∀ s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W s t)))
    (hAnorm : ∀ s i j, ‖decodeRationalComplex (A s i j)‖ ≤ (C : ℝ))
    (hBnorm : ∀ s i j, ‖decodeRationalComplex (B s i j)‖ ≤ (C : ℝ))
    (hWnorm : ∀ s t, ‖decodeRationalComplex (W s t)‖ ≤ (C : ℝ)) :
    ∀ a c, HasGaussianIntegerDenominator (M ^ 3)
        (decodeRationalComplex (weightedTransfer A B W a c)) ∧
      ‖decodeRationalComplex (weightedTransfer A B W a c)‖ ≤ (q ^ 2 * C ^ 3 : ℕ) := by
  intro a c
  let a' := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm a
  let c' := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm c
  let f : Fin (q * q) → ℂ := fun i ↦
    let s := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm i
    (star (decodeRationalComplex (A s.1 a'.1 c'.1)) * decodeRationalComplex (W s.1 s.2)) *
      decodeRationalComplex (B s.2 a'.2 c'.2)
  have hfden : ∀ i, HasGaussianIntegerDenominator (M ^ 3) (f i) := by
    intro i
    simpa only [f, pow_succ, pow_zero, Nat.one_mul] using
      (((hA (finProdFinEquiv.symm i).1 a'.1 c'.1).star.mul
        (hW (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).mul
          (hB (finProdFinEquiv.symm i).2 a'.2 c'.2))
  have hfnorm : ∀ i, ‖f i‖ ≤ (C ^ 3 : ℕ) := by
    intro i
    dsimp only [f]
    rw [norm_mul, norm_mul, norm_star, Nat.cast_pow]
    calc
      _ ≤ (C : ℝ) * C * C := by gcongr <;> first | apply hAnorm | apply hWnorm | apply hBnorm
      _ = (C : ℝ) ^ 3 := by ring
  simp only [weightedTransfer, decodeRationalComplex_fintype_sum,
    RationalComplexCode.decode_mul, RationalComplexCode.decode_conj]
  change HasGaussianIntegerDenominator (M ^ 3) (∑ i, f i) ∧
    ‖∑ i, f i‖ ≤ (q ^ 2 * C ^ 3 : ℕ)
  refine ⟨HasGaussianIntegerDenominator.finset_sum (pow_pos hM _) (fun i _hi ↦ hfden i), ?_⟩
  calc
    _ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (q * q), ((C ^ 3 : ℕ) : ℝ) := Finset.sum_le_sum fun i _hi ↦ hfnorm i
    _ = (q ^ 2 * C ^ 3 : ℕ) := by simp [pow_two, Nat.cast_mul, mul_assoc]

end RationalRectMatrixCode

namespace OBCChainTensor

/-- Actual rational zero-padding preserves the local common denominator and
entry norm bound, including all padded zeros. -/
theorem zeroPadRationalParameters_bounds {q D n M C : ℕ} (A : OBCChainTensor q D n)
    (PA : ParameterIndex A → ℚ × ℚ) (hM : 0 < M)
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (p : Fin n) (s : Fin q) (i j : Fin D) :
    HasGaussianIntegerDenominator M
        (decodeRationalComplex (zeroPadRationalParameters A PA p s i j)) ∧
      ‖decodeRationalComplex (zeroPadRationalParameters A PA p s i j)‖ ≤ (C : ℝ) := by
  have hzero : HasGaussianIntegerDenominator M (decodeRationalComplex (0 : ℚ × ℚ)) ∧
      ‖decodeRationalComplex (0 : ℚ × ℚ)‖ ≤ (C : ℝ) := by
    simpa only [decodeRationalComplex_zero, norm_zero] using
      And.intro (HasGaussianIntegerDenominator.zero hM) (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  unfold zeroPadRationalParameters
  split_ifs <;> first | exact ⟨hPA _, hPAnorm _⟩ | exact hzero

/-- Every matrix in the actual weighted-transfer list inherits denominator
`M³` and entry norm bound `q² C³` from the rational tensor and weight data. -/
theorem weightedTransferSiteList_bounds {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))
    (hWnorm : ∀ p s t, ‖decodeRationalComplex (W p s t)‖ ≤ (C : ℝ)) :
    ∀ T ∈ weightedTransferSiteList A B PA PB W, ∀ a c,
      HasGaussianIntegerDenominator (M ^ 3) (decodeRationalComplex (T a c)) ∧
        ‖decodeRationalComplex (T a c)‖ ≤ (q ^ 2 * C ^ 3 : ℕ) := by
  intro T hT
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hT
  exact RationalRectMatrixCode.weightedTransfer_bounds _ _ _ hM
    (fun s i j ↦ (zeroPadRationalParameters_bounds A PA hM hPA hPAnorm p s i j).1)
    (fun s i j ↦ (zeroPadRationalParameters_bounds B PB hM hPB hPBnorm p s i j).1)
    (hW p)
    (fun s i j ↦ (zeroPadRationalParameters_bounds A PA hM hPA hPAnorm p s i j).2)
    (fun s i j ↦ (zeroPadRationalParameters_bounds B PB hM hPB hPBnorm p s i j).2)
    (hWnorm p)

/-- Every materialized prefix of the actual padded weighted-transfer contraction
has a common denominator and explicit entry norm and rational-coordinate heights.
The initial row is exactly the paired boundary row used by the overlap evaluator. -/
theorem weightedTransfer_prefix_bounds {q Da Db n M C t : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (ht : t ≤ n) (hM : 0 < M)
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))
    (hWnorm : ∀ p s t, ‖decodeRationalComplex (W p s t)‖ ≤ (C : ℝ)) :
    let j₀ := finProdFinEquiv
      ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
    let row := RationalRectMatrixCode.rowProduct (Pi.single j₀ (1, 0))
      ((weightedTransferSiteList A B PA PB W).take t)
    let R := (Da * Db * (q ^ 2 * C ^ 3)) ^ t
    ∀ j, HasGaussianIntegerDenominator (M ^ (3 * t)) (decodeRationalComplex (row j)) ∧
      ‖decodeRationalComplex (row j)‖ ≤ (R : ℝ) ∧
      rationalHeight (row j).1 ≤ M ^ (3 * t) * max 1 R ∧
      rationalHeight (row j).2 ≤ M ^ (3 * t) * max 1 R := by
  classical
  intro j₀ row R
  have hinitial : ∀ j : Fin (Da * Db),
      HasGaussianIntegerDenominator 1
        (decodeRationalComplex ((Pi.single j₀ (1, 0) : Fin (Da * Db) → ℚ × ℚ) j)) ∧
      ‖decodeRationalComplex ((Pi.single j₀ (1, 0) : Fin (Da * Db) → ℚ × ℚ) j)‖ ≤ (1 : ℝ) := by
    intro j
    by_cases hj : j = j₀
    · subst j
      simp only [Pi.single_eq_same, decodeRationalComplex_ratCast, Rat.cast_one, norm_one]
      exact ⟨⟨by decide, ⟨1, by simp⟩⟩, le_rfl⟩
    · simp only [Pi.single_eq_of_ne hj, decodeRationalComplex_zero, norm_zero]
      exact ⟨HasGaussianIntegerDenominator.zero (by decide), zero_le_one⟩
  have hsites := weightedTransferSiteList_bounds A B PA PB W hM hPA hPB hW
    hPAnorm hPBnorm hWnorm
  have hprefix := RationalRectMatrixCode.rowProduct_take_bounds (N := 1) (R := 1)
    (Pi.single j₀ (1, 0)) (weightedTransferSiteList A B PA PB W)
    (by simpa only [weightedTransferSiteList, List.length_ofFn] using ht)
    (by decide) (pow_pos hM 3) (fun j ↦ (hinitial j).1)
    (fun j ↦ by simpa using (hinitial j).2)
    (fun T hT a c ↦ (hsites T hT a c).1) (fun T hT a c ↦ (hsites T hT a c).2)
  intro j
  have hden : HasGaussianIntegerDenominator (M ^ (3 * t)) (decodeRationalComplex (row j)) := by
    simpa only [Nat.one_mul, ← pow_mul] using (hprefix j).1
  have hnorm : ‖decodeRationalComplex (row j)‖ ≤ (R : ℝ) := by
    simpa only [Nat.one_mul] using (hprefix j).2
  have hheight := (RationalComplexCode.decode_height_iff _).mp (hden.height_of_norm_le hnorm)
  exact ⟨hden, hnorm, hheight⟩

end OBCChainTensor

end TNLean.MPS.AreaLaw
