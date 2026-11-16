/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalAccumulationBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBounds

/-!
# Bounds during construction of weighted transfer entries

The counted weighted term first multiplies a conjugated tensor entry by a
physical weight, and then by the second tensor entry. These intermediate
products have denominators of degrees two and three. Every actual prefix of
the physical-pair accumulation retains the degree-three common denominator.
-/

namespace TNLean.MPS.AreaLaw.RationalGramContractionCost

open RationalContractionCost

/-- The actual first product inside a counted weighted term has denominator
`M²`, norm at most `C²`, and the corresponding reduced-coordinate height bound. -/
theorem weightedTerm_firstProduct_bounds {M C : ℕ} (x weight : ℚ × ℚ)
    (hx : HasGaussianIntegerDenominator M (decodeRationalComplex x))
    (hw : HasGaussianIntegerDenominator M (decodeRationalComplex weight))
    (hxnorm : ‖decodeRationalComplex x‖ ≤ (C : ℝ))
    (hwnorm : ‖decodeRationalComplex weight‖ ≤ (C : ℝ)) :
    let out := (complexMul (complexConj x).run.1 weight).run.1
    HasGaussianIntegerDenominator (M ^ 2) (decodeRationalComplex out) ∧
      ‖decodeRationalComplex out‖ ≤ (C ^ 2 : ℕ) ∧
      rationalHeight out.1 ≤ M ^ 2 * max 1 (C ^ 2) ∧
      rationalHeight out.2 ≤ M ^ 2 * max 1 (C ^ 2) := by
  intro out
  have hvalue : decodeRationalComplex out =
      star (decodeRationalComplex x) * decodeRationalComplex weight := by
    simp only [out, run_complexMul, run_complexConj, RationalComplexCode.decode_mul,
      RationalComplexCode.decode_conj]
  have hden : HasGaussianIntegerDenominator (M ^ 2) (decodeRationalComplex out) := by
    rw [hvalue, pow_two]
    exact hx.star.mul hw
  have hnorm : ‖decodeRationalComplex out‖ ≤ (C ^ 2 : ℕ) := by
    rw [hvalue, norm_mul, norm_star, Nat.cast_pow, pow_two]
    exact mul_le_mul hxnorm hwnorm (norm_nonneg _) (Nat.cast_nonneg C)
  exact ⟨hden, hnorm, RationalComplexCode.coordinate_heights_of_common_denominator out hden hnorm⟩

/-- A counted weighted term is bounded directly from its three raw inputs:
the conjugated tensor entry, physical weight, and second tensor entry. -/
theorem weightedTerm_bounds {M C : ℕ} (x weight y : ℚ × ℚ)
    (hx : HasGaussianIntegerDenominator M (decodeRationalComplex x))
    (hw : HasGaussianIntegerDenominator M (decodeRationalComplex weight))
    (hy : HasGaussianIntegerDenominator M (decodeRationalComplex y))
    (hxnorm : ‖decodeRationalComplex x‖ ≤ (C : ℝ))
    (hwnorm : ‖decodeRationalComplex weight‖ ≤ (C : ℝ))
    (hynorm : ‖decodeRationalComplex y‖ ≤ (C : ℝ)) :
    let out := (weightedTerm x weight y).run.1
    HasGaussianIntegerDenominator (M ^ 3) (decodeRationalComplex out) ∧
      ‖decodeRationalComplex out‖ ≤ (C ^ 3 : ℕ) ∧
      rationalHeight out.1 ≤ M ^ 3 * max 1 (C ^ 3) ∧
      rationalHeight out.2 ≤ M ^ 3 * max 1 (C ^ 3) := by
  intro out
  have hfirst := weightedTerm_firstProduct_bounds x weight hx hw hxnorm hwnorm
  have hvalue : decodeRationalComplex out =
      decodeRationalComplex (complexMul (complexConj x).run.1 weight).run.1 *
        decodeRationalComplex y := by
    simp only [out, run_weightedTerm, run_complexMul, run_complexConj,
      RationalComplexCode.decode_mul]
  have hden : HasGaussianIntegerDenominator (M ^ 3) (decodeRationalComplex out) := by
    rw [hvalue, pow_succ]
    exact hfirst.1.mul hy
  have hnorm : ‖decodeRationalComplex out‖ ≤ (C ^ 3 : ℕ) := by
    rw [hvalue, norm_mul]
    calc
      _ ≤ ((C ^ 2 : ℕ) : ℝ) * C :=
        mul_le_mul hfirst.2.1 hynorm (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (C ^ 3 : ℕ) := by push_cast; ring
  exact ⟨hden, hnorm, RationalComplexCode.coordinate_heights_of_common_denominator out hden hnorm⟩

/-- Every prefix of the physical-pair sum used by `weightedTransferEntry`
retains denominator `M³`, has norm at most `a C³`, and has the displayed bounds
on the rational coordinates actually stored in its accumulator. The summand
indexing is exactly that of the counted transfer-entry evaluator. -/
theorem weightedTransferEntry_prefix_bounds {q Da Db M C a : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hA : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A s i j)))
    (hB : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (B s i j)))
    (hW : ∀ s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W s t)))
    (hAnorm : ∀ s i j, ‖decodeRationalComplex (A s i j)‖ ≤ (C : ℝ))
    (hBnorm : ∀ s i j, ‖decodeRationalComplex (B s i j)‖ ≤ (C : ℝ))
    (hWnorm : ∀ s t, ‖decodeRationalComplex (W s t)‖ ≤ (C : ℝ))
    (ha : a ≤ q * q) (i j : Fin (Da * Db)) :
    let out := (sumFin a fun z ↦
      let st := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm (Fin.castLE ha z)
      let ij := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm i
      let jj := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm j
      weightedTerm (A st.1 ij.1 jj.1) (W st.1 st.2) (B st.2 ij.2 jj.2)).run.1
    HasGaussianIntegerDenominator (M ^ 3) (decodeRationalComplex out) ∧
      ‖decodeRationalComplex out‖ ≤ (a * C ^ 3 : ℕ) ∧
      rationalHeight out.1 ≤ M ^ 3 * max 1 (a * C ^ 3) ∧
      rationalHeight out.2 ≤ M ^ 3 * max 1 (a * C ^ 3) := by
  let f : Fin (q * q) → Arithmetic (ℚ × ℚ) := fun z ↦
    let st := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm z
    let ij := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm i
    let jj := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm j
    weightedTerm (A st.1 ij.1 jj.1) (W st.1 st.2) (B st.2 ij.2 jj.2)
  have hf : ∀ z, HasGaussianIntegerDenominator (M ^ 3) (decodeRationalComplex (f z).run.1) ∧
      ‖decodeRationalComplex (f z).run.1‖ ≤ (C ^ 3 : ℕ) := by
    intro z
    let st := (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm z
    let ij := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm i
    let jj := (finProdFinEquiv : Fin Da × Fin Db ≃ Fin (Da * Db)).symm j
    have h := weightedTerm_bounds (A st.1 ij.1 jj.1) (W st.1 st.2) (B st.2 ij.2 jj.2)
      (hA _ _ _) (hW _ _) (hB _ _ _)
      (hAnorm _ _ _) (hWnorm _ _) (hBnorm _ _ _)
    exact ⟨h.1, h.2.1⟩
  exact sumFin_prefix_bounds f ha (pow_pos hM _) (fun z ↦ (hf z).1) (fun z ↦ (hf z).2)

end TNLean.MPS.AreaLaw.RationalGramContractionCost
