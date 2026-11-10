/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergy
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalGramContractionCost

/-!
# Arithmetic counts for rational two-site matrix elements

Expand a two-site observable in its matrix units. Each of its fourth-power
many local coefficients multiplies one weighted overlap contraction. The
counted evaluation computes each overlap once and accumulates the resulting
terms. Only rational additions, subtractions, and multiplications are charged.
-/

namespace TNLean.MPS.AreaLaw.RationalLocalEnergyCost

open RationalContractionCost

/-- Compute one product-operator matrix element and multiply it by a local
Gaussian-rational coefficient. -/
def weightedMatrixElementTerm {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (weight : ℚ × ℚ) :
    Arithmetic (ℚ × ℚ) := do
  let overlap ← RationalGramContractionCost.weightedOverlapOfRationalParameters
    A B capA capB PA PB W
  complexMul weight overlap

/-- The extra local coefficient costs one complex multiplication, namely six
rational operations, in addition to the actual weighted overlap count. -/
@[simp] theorem run_weightedMatrixElementTerm {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (W : Fin n → RationalRectMatrixCode (Fin q) (Fin q)) (weight : ℚ × ℚ) :
    (weightedMatrixElementTerm A B capA capB PA PB W weight).run =
      (RationalComplexCode.mul weight
        (OBCChainTensor.weightedOverlapOfRationalParameters A B capA capB PA PB W),
        Multiplicative.ofAdd (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 6)) := by
  simp only [weightedMatrixElementTerm, run_bind,
    RationalGramContractionCost.run_weightedOverlapOfRationalParameters, run_complexMul]
  rfl

/-- Evaluate the matrix-unit expansion of a rational two-site observable.
Each of the `q⁴` terms computes its weighted overlap once before accumulation. -/
def twoSiteMatrixElementOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) : Arithmetic (ℚ × ℚ) :=
  RationalGramContractionCost.sumFin ((q * q) * (q * q)) fun j ↦
    let uv : Fin (q * q) × Fin (q * q) := finProdFinEquiv.symm j
    let ab : Fin q × Fin q := finProdFinEquiv.symm uv.1
    let cd : Fin q × Fin q := finProdFinEquiv.symm uv.2
    weightedMatrixElementTerm A B capA capB PA PB
      (twoSiteMatrixUnitCodeFactors p r ab.1 ab.2 cd.1 cd.2)
      (K (ab.1, cd.1) (ab.2, cd.2))

/-- The counted two-site evaluator returns the actual rational matrix element.
Every term adds six operations for its coefficient and two for accumulation
to the weighted overlap count, giving the exact displayed arithmetic count. -/
@[simp] theorem run_twoSiteMatrixElementOfRationalParameters {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    (twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K).run =
      (OBCChainTensor.twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K,
        Multiplicative.ofAdd
          (q ^ 4 * (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 8))) := by
  unfold twoSiteMatrixElementOfRationalParameters
  rw [RationalGramContractionCost.run_sumFin _ _
    (fun j ↦ run_weightedMatrixElementTerm _ _ _ _ _ _ _ _)]
  congr 1
  change (q * q) * (q * q) *
      ((n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 6) + 2) =
    q ^ 4 * (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 8)
  ring

/-- Evaluate and accumulate the matrix elements of a finite family of local
two-site terms, computing each local contribution once. -/
def matrixElementOfLocalTerms {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    Arithmetic (ℚ × ℚ) :=
  RationalGramContractionCost.sumFin m fun i ↦
    twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i)

/-- The counted local-Hamiltonian evaluator returns the actual rational sum.
Accumulating `m` local terms adds two rational operations per term to their
individual matrix-element counts. -/
@[simp] theorem run_matrixElementOfLocalTerms {q Da Db n m : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n) (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ) (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    (matrixElementOfLocalTerms A B capA capB PA PB p r K).run =
      (OBCChainTensor.matrixElementOfLocalTerms A B capA capB PA PB p r K,
        Multiplicative.ofAdd
          (m * (q ^ 4 * (n * (15 * q ^ 2 + 8) * (Da * Db) ^ 2 + 13 + 8) + 2))) := by
  exact RationalGramContractionCost.run_sumFin _ _
    (fun i ↦ run_twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i))

end TNLean.MPS.AreaLaw.RationalLocalEnergyCost
