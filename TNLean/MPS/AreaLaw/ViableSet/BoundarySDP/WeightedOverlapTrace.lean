/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedTransferTrace

/-!
# Arithmetic records of sequential weighted row contraction
-/

namespace TNLean.MPS.AreaLaw.RationalArithmeticTrace

open RationalGramContractionCost (WeightedSite)


/-- Compute one transfer matrix, update the stored row, and continue to the
next site. No transfer entry or intermediate row coordinate is recomputed. -/
def weightedRowProduct {q Da Db : ℕ} (v : Fin (Da * Db) → ℚ × ℚ)
    (sites : List (WeightedSite q Da Db)) : Arithmetic (Fin (Da * Db) → ℚ × ℚ) :=
  match sites with
  | [] => pure v
  | site :: sites => do
    let transfer ← weightedTransfer site.1 site.2.1 site.2.2
    let next ← RationalContractionTrace.rowMul v transfer
    weightedRowProduct next sites

theorem erase_weightedRowProduct {q Da Db : ℕ} (v : Fin (Da * Db) → ℚ × ℚ)
    (sites : List (WeightedSite q Da Db)) :
    erase (weightedRowProduct v sites) =
      RationalGramContractionCost.weightedRowProduct v sites := by
  induction sites generalizing v with
  | nil => rfl
  | cons s ss ih =>
    simp only [weightedRowProduct, RationalGramContractionCost.weightedRowProduct, erase_bind,
      erase_weightedTransfer, RationalContractionTrace.erase_rowMul, ih]

private abbrev matrices {q Da Db : ℕ} (sites : List (WeightedSite q Da Db)) :=
  sites.map fun s ↦ RationalRectMatrixCode.weightedTransfer s.1 s.2.1 s.2.2

theorem weightedRowProduct_value {q Da Db : ℕ} (v : Fin (Da * Db) → ℚ × ℚ)
    (sites : List (WeightedSite q Da Db)) :
    (weightedRowProduct v sites).run.1 = RationalRectMatrixCode.rowProduct v (matrices sites) := by
  have h := congrArg (fun x ↦ (WriterT.run x).1) (erase_weightedRowProduct v sites)
  simpa only [run_erase, RationalGramContractionCost.run_weightedRowProduct] using h

private theorem mem_row_records {q Da Db : ℕ} (v : Fin (Da * Db) → ℚ × ℚ)
    (sites : List (WeightedSite q Da Db)) (op : Operation)
    (hop : op ∈ (weightedRowProduct v sites).run.2) :
    (∃ s ∈ sites, op ∈ (weightedTransfer s.1 s.2.1 s.2.2).run.2) ∨
      op ∈ (RationalContractionTrace.rowProduct v (matrices sites)).run.2 := by
  induction sites generalizing v with
  | nil => exact False.elim (List.not_mem_nil hop)
  | cons s ss ih =>
    simp only [weightedRowProduct, run_bind, List.mem_append, (weightedTransfer_value_length ..).1]
      at hop
    simp only [matrices, List.map_cons, RationalContractionTrace.rowProduct, run_bind,
      List.mem_append]
    rcases hop with h | h | h
    · exact Or.inl ⟨s, List.mem_cons_self, h⟩
    · exact Or.inr (Or.inl h)
    · rcases ih _ h with ⟨u, hu, hop⟩ | hop
      · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, hop⟩
      · exact Or.inr (Or.inr hop)

/-- Contract the weighted transfer rows and include the two scalar caps. -/
def weightedContract {q Da Db : ℕ} (capA capB : ℚ × ℚ)
    (v : Fin (Da * Db) → ℚ × ℚ) (sites : List (WeightedSite q Da Db))
    (j : Fin (Da * Db)) : Arithmetic (ℚ × ℚ) := do
  let row ← weightedRowProduct v sites
  weightedTerm capA capB (row j)

theorem erase_weightedContract {q Da Db : ℕ} (capA capB : ℚ × ℚ)
    (v : Fin (Da * Db) → ℚ × ℚ) (sites : List (WeightedSite q Da Db)) (j : Fin (Da * Db)) :
    erase (weightedContract capA capB v sites j) =
      RationalGramContractionCost.weightedContract capA capB v sites j := by
  simp only [weightedContract, erase_bind, erase_weightedRowProduct, erase_weightedTerm]
  rfl

/-- Padded site data in contraction order. -/
abbrev weightedInputSites {q Da Db n : ℕ} (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ) (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) : List (WeightedSite q Da Db) :=
  List.ofFn fun p ↦ (OBCChainTensor.zeroPadRationalParameters A PA p,
    OBCChainTensor.zeroPadRationalParameters B PB p, W p)

/-- Evaluate the weighted overlap of two rational open chains, materializing
one paired transfer matrix and one row at each site. -/
def weightedOverlapOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) : Arithmetic (ℚ × ℚ) :=
  let j := finProdFinEquiv
    ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
  let sites := weightedInputSites A B PA PB W
  weightedContract capA capB (Pi.single j (1, 0)) sites j

theorem weightedOverlap_value_length {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) :
    let x := weightedOverlapOfRationalParameters A B capA capB PA PB W
    x.run.1 = OBCChainTensor.weightedOverlapOfRationalParameters A B capA capB PA PB W ∧
      x.run.2.length = n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 := by
  dsimp only
  apply value_length_of_run_erase
  simpa only [weightedOverlapOfRationalParameters, erase_weightedContract,
    RationalGramContractionCost.weightedOverlapOfRationalParameters, weightedInputSites] using
    RationalGramContractionCost.run_weightedOverlapOfRationalParameters A B capA capB PA PB W

open TNLean.MPS.AreaLaw.OBCChainTensor

private theorem matrices_weightedInputSites {q Da Db n : ℕ} (A : OBCChainTensor q Da n)
    (B : OBCChainTensor q Db n) (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) :
    matrices (weightedInputSites A B PA PB W) = weightedTransferSiteList A B PA PB W := by
  simp [matrices, weightedInputSites, weightedTransferSiteList, List.map_ofFn, Function.comp_def]

/-- The actual row after any prefix has a single cubic denominator factor per site. -/
theorem weightedRow_prefix_bounds {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))
    (hWnorm : ∀ p s t, ‖decodeRationalComplex (W p s t)‖ ≤ (C : ℝ)) (t : ℕ) (ht : t ≤ n) :
    let j₀ := finProdFinEquiv
      ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
    let row := (weightedRowProduct (Pi.single j₀ (1, 0))
       ((weightedInputSites A B PA PB W).take t)).run.1
    ∀ j, HasGaussianIntegerDenominator (M ^ (3 * t)) (decodeRationalComplex (row j)) ∧
      ‖decodeRationalComplex (row j)‖ ≤ ((Da * Db * (q ^ 2 * C ^ 3)) ^ t : ℕ) := by
  intro j₀ row j
  have hp := weightedTransfer_prefix_bounds A B PA PB W ht hM hPA hPB hW hPAnorm hPBnorm hWnorm j
  have hm : matrices ((weightedInputSites A B PA PB W).take t) =
      (weightedTransferSiteList A B PA PB W).take t := by
    rw [← matrices_weightedInputSites, matrices, List.map_take]
  simpa only [row, weightedRowProduct_value, hm, j₀] using And.intro hp.1 hp.2.1

/-- Uniform height budget for the transfer records, row propagation, and caps. -/
def weightedOverlapHeightBound (q Da Db n M C : ℕ) : ℕ :=
  let D := Da * Db
  let K := max 1 (q ^ 2 * C ^ 3)
  let U := M ^ 3 * K
  let S := max U ((M ^ 3 * D * K) ^ n)
  let F := max (M * max 1 C) (M ^ (3 * n) * max 1 ((D * (q ^ 2 * C ^ 3)) ^ n))
  max (max (2 * (2 * (M * max 1 C) ^ 4) ^ 4) (2 * U ^ 2))
    (max (2 * S ^ 4) (2 * (2 * F ^ 4) ^ 4))

/-- Every recorded operand and result, including both boundary multiplications. -/
theorem weightedOverlap_maxHeight_le {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))
    (hWnorm : ∀ p s t, ‖decodeRationalComplex (W p s t)‖ ≤ (C : ℝ))
    (capA capB : ℚ × ℚ)
    (ha : HasRationalComplexCoordinatesOfHeight (M * max 1 C) (decodeRationalComplex capA))
    (hb : HasRationalComplexCoordinatesOfHeight (M * max 1 C) (decodeRationalComplex capB)) :
    maxHeight (weightedOverlapOfRationalParameters A B capA capB PA PB W).run.2 ≤
      weightedOverlapHeightBound q Da Db n M C := by
  let D := Da * Db
  let K := max 1 (q ^ 2 * C ^ 3)
  let U := M ^ 3 * K
  let S := max U ((M ^ 3 * D * K) ^ n)
  let F := max (M * max 1 C) (M ^ (3 * n) * max 1 ((D * (q ^ 2 * C ^ 3)) ^ n))
  let j := finProdFinEquiv
    ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
  let v : Fin (Da * Db) → ℚ × ℚ := Pi.single j (1, 0)
  let sites := weightedInputSites A B PA PB W
  have hp := weightedRow_prefix_bounds A B PA PB W hM hPA hPB hW hPAnorm hPBnorm hWnorm
  have hinit (i) := hp 0 (Nat.zero_le _) i
  simp only [List.take_zero, weightedRowProduct, run_pure, Nat.mul_zero, pow_zero, Nat.cast_one]
    at hinit
  have hfinal := hp n le_rfl j
  have hlen : sites.length = n := List.length_ofFn
  change HasGaussianIntegerDenominator _ (decodeRationalComplex
    ((weightedRowProduct v (sites.take n)).run.1 j)) ∧ _ at hfinal
  rw [List.take_of_length_le hlen.le] at hfinal
  have hs := weightedTransferSiteList_bounds A B PA PB W hM hPA hPB hW hPAnorm hPBnorm hWnorm
  apply (maxHeight_le_iff _ _).mpr
  intro op hop
  change op ∈ (weightedContract capA capB v sites j).run.2 at hop
  simp only [weightedContract, run_bind, List.mem_append] at hop
  rcases hop with h | h
  · rcases mem_row_records v sites op h with ⟨site, hm, he⟩ | hr
    · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hm
      have a := zeroPadRationalParameters_bounds A PA hM hPA hPAnorm p
      have b := zeroPadRationalParameters_bounds B PB hM hPB hPBnorm p
      exact le_max_of_le_left ((maxHeight_le_iff _ _).mp
        (weightedTransfer_maxHeight_le _ _ _ hM (fun s i j ↦ (a s i j).1)
          (fun s i j ↦ (b s i j).1) (hW p) (fun s i j ↦ (a s i j).2)
          (fun s i j ↦ (b s i j).2) (hWnorm p)) op he)
    · rw [show matrices sites = _ from matrices_weightedInputSites A B PA PB W] at hr
      apply le_max_of_le_right (le_max_of_le_left ?_)
      apply RationalContractionTrace.rowProduct_operation_height_le (N := 1) (R := 1)
        (M := M ^ 3) (C := K) v _ (Nat.mul_pos A.bondBound_pos B.bondBound_pos)
        (by decide) (pow_pos hM 3) (by decide) (show 1 ≤ K from le_max_left ..)
        (fun i ↦ (hinit i).1) (fun i ↦ by simpa using (hinit i).2)
        (fun T ht i j ↦ (hs T ht i j).1) _ (le_max_left ..) _ op hr
      · intro T ht i j
        exact ((hs T ht i j).2).trans (Nat.cast_le.mpr (le_max_right ..))
      · simpa only [weightedTransferSiteList, List.length_ofFn, Nat.one_mul] using
          (le_max_right U ((M ^ 3 * D * K) ^ n))
  · have hy := hfinal.1.height_of_norm_le hfinal.2
    exact le_max_of_le_right (le_max_of_le_right ((maxHeight_le_iff _ _).mp
      (weightedTerm_maxHeight_le capA capB _ (ha.mono (le_max_left ..))
        (hb.mono (le_max_left ..)) (hy.mono (le_max_right ..))) op h))

/-- Schoolbook charge for one complete weighted overlap, including the empty chain. -/
theorem weightedOverlap_schoolbookCharge_le {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (PA : ParameterIndex A → ℚ × ℚ) (PB : ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (hM : 0 < M)
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hW : ∀ p s t, HasGaussianIntegerDenominator M (decodeRationalComplex (W p s t)))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))
    (hWnorm : ∀ p s t, ‖decodeRationalComplex (W p s t)‖ ≤ (C : ℝ))
    (capA capB : ℚ × ℚ)
    (ha : HasRationalComplexCoordinatesOfHeight (M * max 1 C) (decodeRationalComplex capA))
    (hb : HasRationalComplexCoordinatesOfHeight (M * max 1 C) (decodeRationalComplex capB)) :
    schoolbookCharge (weightedOverlapOfRationalParameters A B capA capB PA PB W).run.2 ≤
      (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13) *
        rationalSchoolbookOperationCost
          (Nat.log2 (weightedOverlapHeightBound q Da Db n M C) + 1) := by
  have h := schoolbookCharge_le_of_maxHeight_le
    (weightedOverlap_maxHeight_le A B PA PB W hM hPA hPB hW hPAnorm hPBnorm hWnorm capA capB ha hb)
  rwa [(weightedOverlap_value_length A B capA capB PA PB W).2] at h

end TNLean.MPS.AreaLaw.RationalArithmeticTrace
