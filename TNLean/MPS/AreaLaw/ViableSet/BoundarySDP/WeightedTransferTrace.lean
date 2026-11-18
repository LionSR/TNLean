/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferEntryTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalCoefficientTraceHeights

/-!
# Arithmetic records for a materialized weighted transfer matrix
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- Compute and store every weighted transfer entry before using the matrix. -/
def weightedTransfer {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    Arithmetic (RationalRectMatrixCode (Fin (Da * Db)) (Fin (Da * Db))) := do
  let rows ← Vector.ofFnM fun a : Fin (Da * Db) ↦
    Vector.ofFnM fun c : Fin (Da * Db) ↦ weightedTransferEntry A B W a c
  pure fun a c ↦ rows[a.val][c.val]

theorem erase_weightedTransfer {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    erase (weightedTransfer A B W) = RationalGramContractionCost.weightedTransfer A B W := by
  simp only [weightedTransfer, RationalGramContractionCost.weightedTransfer, erase_bind,
    erase_vectorOfFnM, erase_weightedTransferEntry, erase_pure]

theorem weightedTransfer_value_length {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    (weightedTransfer A B W).run.1 = RationalRectMatrixCode.weightedTransfer A B W ∧
      (weightedTransfer A B W).run.2.length = 15 * q ^ 2 * (Da * Db) ^ 2 := by
  apply value_length_of_run_erase
  rw [erase_weightedTransfer, RationalGramContractionCost.run_weightedTransfer]

theorem weightedTransfer_maxHeight_le {q Da Db M C : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hA : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A s i j)))
    (hB : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (B s i j)))
    (hW : ∀ s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W s t)))
    (nA : ∀ s i j, ‖decodeRationalComplex (A s i j)‖ ≤ (C : ℝ))
    (nB : ∀ s i j, ‖decodeRationalComplex (B s i j)‖ ≤ (C : ℝ))
    (nW : ∀ s t, ‖decodeRationalComplex (W s t)‖ ≤ (C : ℝ)) :
    let S := M * max 1 C
    let U := M ^ 3 * max 1 (q ^ 2 * C ^ 3)
    maxHeight (weightedTransfer A B W).run.2 ≤
      max (2 * (2 * S ^ 4) ^ 4) (2 * U ^ 2) := by
  intro S U
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  simp only [weightedTransfer, run_bind, run_pure, List.append_nil] at hop
  obtain ⟨a, ha⟩ := mem_vectorOfFnM_operations _ op hop
  obtain ⟨c, hc⟩ := mem_vectorOfFnM_operations _ op ha
  exact (maxHeight_le_iff _ _).mp
    (weightedTransferEntry_maxHeight_le A B W a c hM hA hB hW nA nB nW) op hc

theorem weightedTransfer_schoolbookCharge_le {q Da Db M C : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hA : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A s i j)))
    (hB : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (B s i j)))
    (hW : ∀ s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W s t)))
    (nA : ∀ s i j, ‖decodeRationalComplex (A s i j)‖ ≤ (C : ℝ))
    (nB : ∀ s i j, ‖decodeRationalComplex (B s i j)‖ ≤ (C : ℝ))
    (nW : ∀ s t, ‖decodeRationalComplex (W s t)‖ ≤ (C : ℝ)) :
    let S := M * max 1 C
    let U := M ^ 3 * max 1 (q ^ 2 * C ^ 3)
    let H := max (2 * (2 * S ^ 4) ^ 4) (2 * U ^ 2)
    schoolbookCharge (weightedTransfer A B W).run.2 ≤
      (15 * q ^ 2 * (Da * Db) ^ 2) * rationalSchoolbookOperationCost (Nat.log2 H + 1) := by
  intro S U H
  have h := schoolbookCharge_le_of_maxHeight_le
    (weightedTransfer_maxHeight_le A B W hM hA hB hW nA nB nW)
  rwa [(weightedTransfer_value_length A B W).2] at h

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
