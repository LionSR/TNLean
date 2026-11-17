/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContraction
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContractionCost

/-!
# Arithmetic counts for rational overlap contraction

Weighted transfer matrices contract pairs of open-chain tensor entries without
enumerating full physical configurations. The counted computation evaluates
every transfer entry and every intermediate row once. Its count records only
rational additions, subtractions, and multiplications, as in the counted
single-chain contraction.
-/

namespace TNLean.MPS.AreaLaw.RationalGramContractionCost

open RationalContractionCost

/-- Conjugate a Gaussian rational by one counted subtraction from zero. -/
def complexConj (z : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let imag ← rationalSub 0 z.2
  pure (z.1, imag)

/-- Conjugation returns the rational conjugate with exactly one charged operation. -/
@[simp] theorem run_complexConj (z : ℚ × ℚ) :
    (complexConj z).run = (RationalComplexCode.conj z, Multiplicative.ofAdd 1) := by
  change ((z.1, (0 : ℚ) - z.2), Multiplicative.ofAdd 1) = _
  simp only [zero_sub, RationalComplexCode.conj]

/-- Sum finitely many computed Gaussian rationals, accumulating from zero. -/
def sumFin : (n : ℕ) → (Fin n → Arithmetic (ℚ × ℚ)) → Arithmetic (ℚ × ℚ)
  | 0, _ => pure (0, 0)
  | n + 1, f => do
    let previous ← sumFin n (fun i ↦ f i.castSucc)
    let term ← f (Fin.last n)
    complexAdd previous term

/-- Summing `n` computed terms of count `c` adds two rational operations per term. -/
theorem run_sumFin {n c : ℕ} (f : Fin n → Arithmetic (ℚ × ℚ))
    (v : Fin n → ℚ × ℚ)
    (h : ∀ i, (f i).run = (v i, Multiplicative.ofAdd c)) :
    (sumFin n f).run = (∑ i, v i, Multiplicative.ofAdd (n * (c + 2))) := by
  induction n with
  | zero => simp [sumFin]; rfl
  | succ n ih =>
    simp only [sumFin, run_bind,
      ih (fun i ↦ f i.castSucc) (fun i ↦ v i.castSucc) (fun i ↦ h i.castSucc), h,
      run_complexAdd]
    simp only [Fin.sum_univ_castSucc, RationalComplexCode.add]
    congr 1
    change n * (c + 2) + (c + 2) = (n + 1) * (c + 2)
    simp [Nat.add_mul]

/-- One weighted transfer term: conjugate the left entry, then multiply by
the physical weight and the right entry. -/
def weightedTerm (x weight y : ℚ × ℚ) : Arithmetic (ℚ × ℚ) := do
  let left ← complexConj x
  let weighted ← complexMul left weight
  complexMul weighted y

/-- Each weighted transfer term uses one conjugation and two complex products. -/
@[simp] theorem run_weightedTerm (x weight y : ℚ × ℚ) :
    (weightedTerm x weight y).run =
      (RationalComplexCode.mul (RationalComplexCode.mul (RationalComplexCode.conj x) weight) y,
        Multiplicative.ofAdd 13) := by
  simp only [weightedTerm, run_bind, run_complexConj, run_complexMul]
  rfl

/-- Evaluate one weighted transfer entry by a single sum over the physical pair. -/
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

/-- The physical-pair sum evaluates a transfer entry in exactly `15q²` rational
operations. -/
@[simp] theorem run_weightedTransferEntry {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) (a c : Fin (Da * Db)) :
    (weightedTransferEntry A B W a c).run =
      (RationalRectMatrixCode.weightedTransfer A B W a c,
        Multiplicative.ofAdd (15 * q ^ 2)) := by
  unfold weightedTransferEntry
  rw [run_sumFin _ _ (fun z ↦ run_weightedTerm _ _ _)]
  congr 1
  change q * q * (13 + 2) = 15 * q ^ 2
  ring

/-- Compute and store every weighted transfer entry before using the matrix. -/
def weightedTransfer {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    Arithmetic (RationalRectMatrixCode (Fin (Da * Db)) (Fin (Da * Db))) := do
  let rows ← Vector.ofFnM fun a : Fin (Da * Db) ↦
    Vector.ofFnM fun c : Fin (Da * Db) ↦ weightedTransferEntry A B W a c
  pure fun a c ↦ rows[a.val][c.val]

/-- A materialized weighted transfer matrix uses exactly `15q²(Da Db)²`
rational operations and returns the ordinary rational transfer matrix. -/
@[simp] theorem run_weightedTransfer {q Da Db : ℕ}
    (A : Fin q → RationalRectMatrixCode (Fin Da) (Fin Da))
    (B : Fin q → RationalRectMatrixCode (Fin Db) (Fin Db))
    (W : RationalRectMatrixCode (Fin q) (Fin q)) :
    (weightedTransfer A B W).run =
      (RationalRectMatrixCode.weightedTransfer A B W,
        Multiplicative.ofAdd (15 * q ^ 2 * (Da * Db) ^ 2)) := by
  have hrow (a : Fin (Da * Db)) := run_vectorOfFnM
    (fun c : Fin (Da * Db) ↦ weightedTransferEntry A B W a c)
    (fun c ↦ RationalRectMatrixCode.weightedTransfer A B W a c)
    (fun c ↦ run_weightedTransferEntry A B W a c)
  have hmatrix := run_vectorOfFnM
    (fun a : Fin (Da * Db) ↦
      Vector.ofFnM fun c : Fin (Da * Db) ↦ weightedTransferEntry A B W a c)
    (fun a ↦ Vector.ofFn fun c ↦ RationalRectMatrixCode.weightedTransfer A B W a c)
    hrow
  simp only [weightedTransfer, run_bind, hmatrix, run_pure, Vector.getElem_ofFn]
  congr 1
  change (Da * Db) * ((Da * Db) * (15 * q ^ 2)) + 0 = 15 * q ^ 2 * (Da * Db) ^ 2
  ring

/-- The two local tensor families and the physical weight at one site. -/
abbrev WeightedSite (q Da Db : ℕ) :=
  (Fin q → RationalRectMatrixCode (Fin Da) (Fin Da)) ×
    (Fin q → RationalRectMatrixCode (Fin Db) (Fin Db)) ×
      RationalRectMatrixCode (Fin q) (Fin q)

/-- Compute one transfer matrix, update the stored row, and continue to the
next site. No transfer entry or intermediate row coordinate is recomputed. -/
def weightedRowProduct {q Da Db : ℕ} (v : Fin (Da * Db) → ℚ × ℚ)
    (sites : List (WeightedSite q Da Db)) : Arithmetic (Fin (Da * Db) → ℚ × ℚ) :=
  match sites with
  | [] => pure v
  | site :: sites => do
    let transfer ← weightedTransfer site.1 site.2.1 site.2.2
    let next ← RationalContractionCost.rowMul v transfer
    weightedRowProduct next sites

/-- Transfer construction and row propagation together use exactly
`n(15q²+8)(Da Db)²` rational operations on a list of `n` sites. -/
@[simp] theorem run_weightedRowProduct {q Da Db : ℕ} (v : Fin (Da * Db) → ℚ × ℚ)
    (sites : List (WeightedSite q Da Db)) :
    (weightedRowProduct v sites).run =
      (RationalRectMatrixCode.rowProduct v (sites.map fun site ↦
        RationalRectMatrixCode.weightedTransfer site.1 site.2.1 site.2.2),
        Multiplicative.ofAdd (sites.length * (15 * q ^ 2 + 8) * (Da * Db) ^ 2)) := by
  induction sites generalizing v with
  | nil => simp [weightedRowProduct]; rfl
  | cons site sites ih =>
    simp only [weightedRowProduct, run_bind, run_weightedTransfer,
      RationalContractionCost.run_rowMul, ih, List.map_cons,
      RationalRectMatrixCode.rowProduct_cons, List.length_cons]
    congr 1
    change 15 * q ^ 2 * (Da * Db) ^ 2 +
        (8 * (Da * Db) ^ 2 + sites.length * (15 * q ^ 2 + 8) * (Da * Db) ^ 2) =
      (sites.length + 1) * (15 * q ^ 2 + 8) * (Da * Db) ^ 2
    ring

/-- Contract the weighted transfer rows and include the two scalar caps. -/
def weightedContract {q Da Db : ℕ} (capA capB : ℚ × ℚ)
    (v : Fin (Da * Db) → ℚ × ℚ) (sites : List (WeightedSite q Da Db))
    (j : Fin (Da * Db)) : Arithmetic (ℚ × ℚ) := do
  let row ← weightedRowProduct v sites
  let leftCap ← complexConj capA
  let cap ← complexMul leftCap capB
  complexMul cap (row j)

/-- The scalar caps add one conjugation and two complex products to the
transfer contraction, namely thirteen rational operations. -/
@[simp] theorem run_weightedContract {q Da Db : ℕ} (capA capB : ℚ × ℚ)
    (v : Fin (Da * Db) → ℚ × ℚ) (sites : List (WeightedSite q Da Db))
    (j : Fin (Da * Db)) :
    (weightedContract capA capB v sites j).run =
      (RationalComplexCode.mul (RationalComplexCode.mul (RationalComplexCode.conj capA) capB)
        (RationalRectMatrixCode.rowProduct v (sites.map fun site ↦
          RationalRectMatrixCode.weightedTransfer site.1 site.2.1 site.2.2) j),
        Multiplicative.ofAdd (sites.length * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13)) := by
  simp only [weightedContract, run_bind, run_weightedRowProduct,
    run_complexConj, run_complexMul]
  rfl

/-- Evaluate the weighted overlap of two rational open chains, materializing
one paired transfer matrix and one row at each site. -/
def weightedOverlapOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) : Arithmetic (ℚ × ℚ) :=
  let j := finProdFinEquiv
    ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))
  let sites : List (WeightedSite q Da Db) := List.ofFn fun p : Fin n ↦
    ((fun i ↦ OBCChainTensor.zeroPadRationalParameters A PA p i),
      (fun i ↦ OBCChainTensor.zeroPadRationalParameters B PB p i), W p)
  weightedContract capA capB (Pi.single j (1, 0)) sites j

/-- The counted paired-chain evaluator returns the actual rational weighted
overlap and performs exactly `n(15q²+8)(Da Db)²+13` rational operations. -/
@[simp] theorem run_weightedOverlapOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) :
    (weightedOverlapOfRationalParameters A B capA capB PA PB W).run =
      (OBCChainTensor.weightedOverlapOfRationalParameters A B capA capB PA PB W,
        Multiplicative.ofAdd (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13)) := by
  simpa only [weightedOverlapOfRationalParameters,
    OBCChainTensor.weightedOverlapOfRationalParameters,
    OBCChainTensor.weightedTransferSiteList, List.length_ofFn, List.map_ofFn,
    Function.comp_def] using run_weightedContract capA capB
    (Pi.single (finProdFinEquiv
      ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db))) (1, 0))
    (List.ofFn fun p : Fin n ↦
      ((fun i ↦ OBCChainTensor.zeroPadRationalParameters A PA p i),
        (fun i ↦ OBCChainTensor.zeroPadRationalParameters B PB p i), W p))
    (finProdFinEquiv
      ((⟨0, A.bondBound_pos⟩ : Fin Da), (⟨0, B.bondBound_pos⟩ : Fin Db)))

end TNLean.MPS.AreaLaw.RationalGramContractionCost
