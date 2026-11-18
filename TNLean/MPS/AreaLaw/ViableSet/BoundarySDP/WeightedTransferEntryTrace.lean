/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTermTrace
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferBounds

/-!
# Arithmetic records for physical-pair sums in weighted transfer entries
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

/-- Record the prefix, the new summand, then the two coordinate additions. -/
def sumFin : (n : ℕ) → (Fin n → Arithmetic (ℚ × ℚ)) → Arithmetic (ℚ × ℚ)
  | 0, _ => pure (0, 0)
  | n + 1, f => do
    let previous ← sumFin n (fun i ↦ f i.castSucc)
    let term ← f (Fin.last n)
    complexAdd previous term

theorem erase_sumFin (n : ℕ) (f : Fin n → Arithmetic (ℚ × ℚ)) :
    erase (sumFin n f) = RationalGramContractionCost.sumFin n (fun i ↦ erase (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin, RationalGramContractionCost.sumFin, erase_bind, erase_complexAdd, ih]

theorem sumFin_value (n : ℕ) (f : Fin n → Arithmetic (ℚ × ℚ)) :
    (sumFin n f).run.1 = ∑ i, (f i).run.1 := by
  induction n with
  | zero => simp [sumFin]; rfl
  | succ n ih =>
    simp only [sumFin, run_bind, run_complexAdd, Fin.sum_univ_castSucc, ih]
    rfl

/-- Prefixes retain the common summand denominator regardless of the number of additions. -/
theorem sumFin_bounds {n M C : ℕ} (f : Fin n → Arithmetic (ℚ × ℚ)) (hM : 0 < M)
    (hd : ∀ i, HasGaussianIntegerDenominator M (decodeRationalComplex (f i).run.1))
    (hn : ∀ i, ‖decodeRationalComplex (f i).run.1‖ ≤ (C : ℝ)) :
    HasGaussianIntegerDenominator M (decodeRationalComplex (sumFin n f).run.1) ∧
      ‖decodeRationalComplex (sumFin n f).run.1‖ ≤ (n * C : ℕ) := by
  rw [sumFin_value, decodeRationalComplex_fintype_sum]
  refine ⟨HasGaussianIntegerDenominator.finset_sum hM (fun i _ ↦ hd i), ?_⟩
  calc
    _ ≤ ∑ i, ‖decodeRationalComplex (f i).run.1‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (C : ℝ) := Finset.sum_le_sum fun i _ ↦ hn i
    _ = _ := by simp

/-- Bound additions from the actual prefix values, retaining the given bound
for the primitive operations internal to each summand. -/
theorem sumFin_operation_height_le {n M C S T : ℕ} (f : Fin n → Arithmetic (ℚ × ℚ))
    (hM : 0 < M) (hd : ∀ i, HasGaussianIntegerDenominator M (decodeRationalComplex (f i).run.1))
    (hn : ∀ i, ‖decodeRationalComplex (f i).run.1‖ ≤ (C : ℝ))
    (ht : ∀ i, maxHeight (f i).run.2 ≤ T) (hs : M * max 1 (n * C) ≤ S)
    (op : Operation) (hop : op ∈ (sumFin n f).run.2) : op.height ≤ max T (2 * S ^ 2) := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil hop)
  | succ n ih =>
    have hmono (j : ℕ) (hj : j ≤ n + 1) : M * max 1 (j * C) ≤ S :=
      (Nat.mul_le_mul_left _ (max_le_max_left _ (Nat.mul_le_mul_right _ hj))).trans hs
    simp only [sumFin, run_bind, List.mem_append] at hop
    rcases hop with h | h | h
    · exact ih _ (fun i ↦ hd i.castSucc) (fun i ↦ hn i.castSucc)
        (fun i ↦ ht i.castSucc) (hmono n (by omega)) h
    · exact ((maxHeight_le_iff _ _).mp (ht _) op h).trans (le_max_left _ _)
    · have hb := sumFin_bounds (fun i : Fin n ↦ f i.castSucc) hM
          (fun i ↦ hd _) (fun i ↦ hn _)
      apply LE.le.trans _ (le_max_right _ _)
      apply (Operation.height_le_iff _ _).mpr
      apply complexAdd_operation_heights _ _ ((hb.1.height_of_norm_le hb.2).mono
        (hmono n (by omega))) (((hd _).height_of_norm_le (hn _)).mono _) op h
      simpa only [Nat.one_mul] using hmono 1 (by omega)

/-- Record all physical-pair summands in one transfer matrix entry. -/
def weightedTransferEntry {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (a c : Fin (Da * Db)) :
    Arithmetic (ℚ × ℚ) :=
  sumFin (q * q) fun z ↦
    let st := finProdFinEquiv.symm z
    let ac := finProdFinEquiv.symm a
    let cc := finProdFinEquiv.symm c
    weightedTerm (A st.1 ac.1 cc.1) (W st.1 st.2) (B st.2 ac.2 cc.2)

theorem erase_weightedTransferEntry {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (a c : Fin (Da * Db)) :
    erase (weightedTransferEntry A B W a c) =
      RationalGramContractionCost.weightedTransferEntry A B W a c := by
  simp only [weightedTransferEntry, RationalGramContractionCost.weightedTransferEntry,
    erase_sumFin, erase_weightedTerm]

private theorem decode_weightedTerm (x w y : ℚ × ℚ) :
    decodeRationalComplex (weightedTerm x w y).run.1 =
      star (decodeRationalComplex x) * decodeRationalComplex w * decodeRationalComplex y := by
  have hv := congrArg (fun z ↦ (WriterT.run z).1) (erase_weightedTerm x w y)
  simp only [run_erase, RationalGramContractionCost.run_weightedTerm] at hv
  rw [hv, RationalComplexCode.decode_mul, RationalComplexCode.decode_mul,
    RationalComplexCode.decode_conj]

/-- A common input denominator enters cubically; summation affects only the
norm budget of the prefix. The maximum covers all operations in an actual entry. -/
theorem weightedTransferEntry_maxHeight_le {q Da Db M C : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (a c : Fin (Da * Db)) (hM : 0 < M)
    (hA : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (A s i j)))
    (hB : ∀ s i j, HasGaussianIntegerDenominator M (decodeRationalComplex (B s i j)))
    (hW : ∀ s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W s t)))
    (nA : ∀ s i j, ‖decodeRationalComplex (A s i j)‖ ≤ (C : ℝ))
    (nB : ∀ s i j, ‖decodeRationalComplex (B s i j)‖ ≤ (C : ℝ))
    (nW : ∀ s t, ‖decodeRationalComplex (W s t)‖ ≤ (C : ℝ)) :
    let S := M * max 1 C
    let U := M ^ 3 * max 1 (q ^ 2 * C ^ 3)
    maxHeight (weightedTransferEntry A B W a c).run.2 ≤
      max (2 * (2 * S ^ 4) ^ 4) (2 * U ^ 2) := by
  intro S U
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  apply sumFin_operation_height_le _ (pow_pos hM 3) (C := C ^ 3) _ _ _ _ op hop
  · intro z
    rw [decode_weightedTerm]
    simpa only [pow_succ, pow_zero, Nat.one_mul] using
      (((hA _ _ _).star.mul (hW _ _)).mul (hB _ _ _))
  · intro z
    rw [decode_weightedTerm, norm_mul, norm_mul, norm_star, Nat.cast_pow]
    calc
      _ ≤ (C : ℝ) * C * C := by gcongr <;> first | apply nA | apply nW | apply nB
      _ = _ := by ring
  · intro z
    exact weightedTerm_maxHeight_le _ _ _ ((hA _ _ _).height_of_norm_le (nA _ _ _))
      ((hW _ _).height_of_norm_le (nW _ _)) ((hB _ _ _).height_of_norm_le (nB _ _ _))
  · simp [U, pow_two]

/-- The retained operand records compute the transfer entry with exactly
fifteen operations per physical pair, including both prefix additions. -/
theorem weightedTransferEntry_value_length {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (a c : Fin (Da * Db)) :
    (weightedTransferEntry A B W a c).run.1 = RationalRectMatrixCode.weightedTransfer A B W a c ∧
      (weightedTransferEntry A B W a c).run.2.length = 15 * q ^ 2 := by
  have h := congrArg WriterT.run (erase_weightedTransferEntry A B W a c)
  simp only [run_erase, RationalGramContractionCost.run_weightedTransferEntry] at h
  exact ⟨congrArg Prod.fst h, congrArg Multiplicative.toAdd (congrArg Prod.snd h)⟩

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
