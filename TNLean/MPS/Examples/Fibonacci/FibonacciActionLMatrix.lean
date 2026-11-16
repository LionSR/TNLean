/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciActionDecomposition
import TNLean.MPS.MPDO.BoundaryActionLMatrix
import TNLean.MPS.MPDO.BoundaryFusionFMatrix
/-!
# The multiplicity L matrix of the Fibonacci regular module equals F
For the existing two normal Fibonacci states, the exact action-tree
contractions give the standard Fibonacci F symbols in the explicit gauge
of `FibonacciActionDecomposition`. Every sector, including empty sectors,
is retained. The sequential multiplicity index is the right fusion index;
the fusion-then-action multiplicity index is the left fusion index.
Source: GLM23, arXiv:2203.12563v3, `eq:F_symbol2`, `1Fsymbol`,
lines 595--605 and 1991--1993. The source prints no pair of MPS tensors;
these are the existing explicit tensors of this development. The MPO-entry
provenance restriction is recorded in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.
-/
open scoped Matrix BigOperators Kronecker
open MPSTensor MPOTensor GoldenInt
namespace FibonacciCompression.Boundary
/-- The fusion-then-action analysis contraction over the golden integers. -/
def fusionActionAnalysisGolden (a b x : Fin 2)
    (q : FusionActionPath fibNim fibNim a b x) :
    Matrix (Fin (fibNimDim q.2.1)) (Fin (fibBlockDim a * fibBlockDim b * fibNimDim x)) GoldenInt :=
  fun u v ↦
    let w := finProdFinEquiv.symm v
    let t := finProdFinEquiv.symm w.1
    ∑ k : Fin (fibBlockDim q.1.1),
      actionAnalysisGolden q.1.1 x q.2.1 q.2.2 u (finProdFinEquiv (k, w.2)) *
        fusionAnalysisGolden a b q.1.1 q.1.2 k (finProdFinEquiv t)
private theorem fusionActionAnalysis_eq (a b x : Fin 2)
    (q : FusionActionPath fibNim fibNim a b x) :
    fusionThenActionAnalysis fusionAnalysis actionAnalysis a b x q =
      complexOfGolden (fusionActionAnalysisGolden a b x q) := by
  rcases q with ⟨⟨c, μ⟩, y, k⟩
  ext u v
  obtain ⟨⟨ab, xx⟩, rfl⟩ := finProdFinEquiv.surjective v
  obtain ⟨⟨xa, xb⟩, rfl⟩ := finProdFinEquiv.surjective ab
  rw [fusionThenActionAnalysis_apply]
  simp [fusionActionAnalysisGolden, fusionAnalysis, fusionSynthesis,
    actionAnalysis, actionSynthesis, map_sum, map_mul]
/-- The fusion-then-action synthesis contraction over the golden integers. -/
def fusionActionSynthesisGolden (a b x : Fin 2)
    (q : FusionActionPath fibNim fibNim a b x) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b * fibNimDim x)) (Fin (fibNimDim q.2.1)) GoldenInt :=
  fun u v ↦
    let w := finProdFinEquiv.symm u
    let t := finProdFinEquiv.symm w.1
    ∑ k : Fin (fibBlockDim q.1.1),
      fusionSynthesisGolden a b q.1.1 q.1.2 (finProdFinEquiv t) k *
        actionSynthesisGolden q.1.1 x q.2.1 q.2.2 (finProdFinEquiv (k, w.2)) v
private theorem fusionActionSynthesis_eq (a b x : Fin 2)
    (q : FusionActionPath fibNim fibNim a b x) :
    fusionThenActionSynthesis fusionSynthesis actionSynthesis a b x q =
      complexOfGolden (fusionActionSynthesisGolden a b x q) := by
  rcases q with ⟨⟨c, μ⟩, y, k⟩
  ext u v
  obtain ⟨⟨ab, xx⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨xa, xb⟩, rfl⟩ := finProdFinEquiv.surjective ab
  rw [fusionThenActionSynthesis_apply]
  simp [fusionActionSynthesisGolden, fusionAnalysis, fusionSynthesis,
    actionAnalysis, actionSynthesis, map_sum, map_mul]
/-- The sequential analysis contraction over the golden integers. -/
def sequentialAnalysisGolden (a b x : Fin 2)
    (q : SequentialActionPath fibNim a b x) :
    Matrix (Fin (fibNimDim q.2.1)) (Fin (fibBlockDim a * fibBlockDim b * fibNimDim x)) GoldenInt :=
  fun u v ↦
    let w := finProdFinEquiv.symm v
    let t := finProdFinEquiv.symm w.1
    ∑ k : Fin (fibNimDim q.1.1),
      actionAnalysisGolden a q.1.1 q.2.1 q.2.2 u (finProdFinEquiv (t.1, k)) *
        actionAnalysisGolden b x q.1.1 q.1.2 k (finProdFinEquiv (t.2, w.2))
private theorem sequentialAnalysis_eq (a b x : Fin 2)
    (q : SequentialActionPath fibNim a b x) :
    sequentialActionAnalysis actionAnalysis a b x q =
      complexOfGolden (sequentialAnalysisGolden a b x q) := by
  rcases q with ⟨⟨z, j⟩, y, i⟩
  ext u v
  obtain ⟨⟨ab, xx⟩, rfl⟩ := finProdFinEquiv.surjective v
  obtain ⟨⟨xa, xb⟩, rfl⟩ := finProdFinEquiv.surjective ab
  rw [sequentialActionAnalysis_apply]
  simp [sequentialAnalysisGolden, fusionAnalysis, fusionSynthesis,
    actionAnalysis, actionSynthesis, map_sum, map_mul]
/-- The sequential synthesis contraction over the golden integers. -/
def sequentialSynthesisGolden (a b x : Fin 2)
    (q : SequentialActionPath fibNim a b x) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b * fibNimDim x)) (Fin (fibNimDim q.2.1)) GoldenInt :=
  fun u v ↦
    let w := finProdFinEquiv.symm u
    let t := finProdFinEquiv.symm w.1
    ∑ k : Fin (fibNimDim q.1.1),
      actionSynthesisGolden b x q.1.1 q.1.2 (finProdFinEquiv (t.2, w.2)) k *
        actionSynthesisGolden a q.1.1 q.2.1 q.2.2 (finProdFinEquiv (t.1, k)) v
private theorem sequentialSynthesis_eq (a b x : Fin 2)
    (q : SequentialActionPath fibNim a b x) :
    sequentialActionSynthesis actionSynthesis a b x q =
      complexOfGolden (sequentialSynthesisGolden a b x q) := by
  rcases q with ⟨⟨z, j⟩, y, i⟩
  ext u v
  obtain ⟨⟨ab, xx⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨xa, xb⟩, rfl⟩ := finProdFinEquiv.surjective ab
  rw [sequentialActionSynthesis_apply]
  simp [sequentialSynthesisGolden, fusionAnalysis, fusionSynthesis,
    actionAnalysis, actionSynthesis, map_sum, map_mul]
private theorem action_crossGolden : ∀ (a b x y : Fin 2)
    (p : SequentialActionMultiplicity fibNim a b x y)
    (q : FusionActionMultiplicity fibNim fibNim a b x y),
    sequentialAnalysisGolden a b x (sequentialActionPathEquiv a b x ⟨y, p⟩) *
        fusionActionSynthesisGolden a b x (fusionActionPathEquiv a b x ⟨y, q⟩) =
      fibFSymbolGolden a b x y q.1 p.1 •
        (1 : Matrix (Fin (fibNimDim y)) (Fin (fibNimDim y)) GoldenInt) := by
  decide +kernel
private theorem action_inverseCrossGolden : ∀ (a b x y : Fin 2)
    (q : FusionActionMultiplicity fibNim fibNim a b x y)
    (p : SequentialActionMultiplicity fibNim a b x y),
    fusionActionAnalysisGolden a b x (fusionActionPathEquiv a b x ⟨y, q⟩) *
        sequentialSynthesisGolden a b x (sequentialActionPathEquiv a b x ⟨y, p⟩) =
      fibFSymbolGolden a b x y q.1 p.1 •
        (1 : Matrix (Fin (fibNimDim y)) (Fin (fibNimDim y)) GoldenInt) := by
  decide +kernel
private theorem inv_dim_trace {D : ℕ} (hD : 0 < D) (z : ℂ) :
    (D : ℂ)⁻¹ * Matrix.trace (z • (1 : Matrix (Fin D) (Fin D) ℂ)) = z := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have hn : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp
private theorem state_dim_pos (y : Fin 2) : 0 < fibNimDim y := by
  fin_cases y <;> decide
/-- Every entry of the actual multiplicity L matrix equals the printed
Fibonacci F symbol, with the source's opposite multiplicity index orders.
Source: GLM23, `1Fsymbol` and the Fibonacci example, lines 1991--1993. -/
theorem actionLMatrix_eq_fSymbol (a b x y : Fin 2)
    (p : SequentialActionMultiplicity fibNim a b x y)
    (q : FusionActionMultiplicity fibNim fibNim a b x y) :
    actionLMatrix fusionSynthesis actionAnalysis actionSynthesis a b x y p q =
      goldenToComplex (fibFSymbolGolden a b x y q.1 p.1) := by
  rw [actionLMatrix, sequentialAnalysis_eq, fusionActionSynthesis_eq,
    ← complexOfGolden_mul, action_crossGolden,
    complexOfRing_smul, complexOfGolden_one]
  exact inv_dim_trace (state_dim_pos y) _
/-- The reverse action-tree comparison has the transposed standard F entries.
Source: GLM23, `eq:F_symbol2` and `1Fsymbol`. -/
theorem inverseActionLMatrix_eq_fSymbol (a b x y : Fin 2)
    (q : FusionActionMultiplicity fibNim fibNim a b x y)
    (p : SequentialActionMultiplicity fibNim a b x y) :
    inverseActionLMatrix fusionAnalysis actionAnalysis actionSynthesis a b x y q p =
      goldenToComplex (fibFSymbolGolden a b x y q.1 p.1) := by
  rw [inverseActionLMatrix, fusionActionAnalysis_eq, sequentialSynthesis_eq,
    ← complexOfGolden_mul, action_inverseCrossGolden,
    complexOfRing_smul, complexOfGolden_one]
  exact inv_dim_trace (state_dim_pos y) _
/-- The only two-dimensional multiplicity sector is the standard
`[[sigma², sigma], [sigma, -sigma²]]` Fibonacci matrix. -/
theorem actionLMatrix_tau
    (p : SequentialActionMultiplicity fibNim 1 1 1 1)
    (q : FusionActionMultiplicity fibNim fibNim 1 1 1 1) :
    actionLMatrix fusionSynthesis actionAnalysis actionSynthesis 1 1 1 1 p q =
      goldenToComplex (fibFTauGolden p.1 q.1) := by
  rw [actionLMatrix_eq_fSymbol, fibFSymbolGolden_tau]
  have h : fibFTauGolden q.1 p.1 = fibFTauGolden p.1 q.1 := by
    have hs : ∀ c z : Fin 2, fibFTauGolden c z = fibFTauGolden z c := by decide +kernel
    exact hs _ _
  rw [h]
/-- Printed Fibonacci coefficients with the action multiplicity index types. -/
def printedLGolden (a b x y : Fin 2) :
    Matrix (SequentialActionMultiplicity fibNim a b x y)
      (FusionActionMultiplicity fibNim fibNim a b x y) GoldenInt :=
  fun p q ↦ fibFSymbolGolden a b x y q.1 p.1
/-- Printed coefficients with the reverse action multiplicity index types. -/
def printedInverseLGolden (a b x y : Fin 2) :
    Matrix (FusionActionMultiplicity fibNim fibNim a b x y)
      (SequentialActionMultiplicity fibNim a b x y) GoldenInt :=
  fun q p ↦ fibFSymbolGolden a b x y q.1 p.1
private theorem printedL_inverseGolden : ∀ a b x y : Fin 2,
    printedLGolden a b x y * printedInverseLGolden a b x y = 1 ∧
      printedInverseLGolden a b x y * printedLGolden a b x y = 1 := by
  decide +kernel
/-- The actual double-action comparison matrices are inverse in every sector,
including the empty multiplicity spaces. Source: GLM23, `1Fsymbol`. -/
theorem actionLMatrix_inverse (a b x y : Fin 2) :
    actionLMatrix fusionSynthesis actionAnalysis actionSynthesis a b x y *
        inverseActionLMatrix fusionAnalysis actionAnalysis actionSynthesis a b x y = 1 ∧
      inverseActionLMatrix fusionAnalysis actionAnalysis actionSynthesis a b x y *
        actionLMatrix fusionSynthesis actionAnalysis actionSynthesis a b x y = 1 := by
  have hL : actionLMatrix fusionSynthesis actionAnalysis actionSynthesis a b x y =
      complexOfGolden (printedLGolden a b x y) := by
    ext p q
    exact actionLMatrix_eq_fSymbol a b x y p q
  have hI : inverseActionLMatrix fusionAnalysis actionAnalysis actionSynthesis a b x y =
      complexOfGolden (printedInverseLGolden a b x y) := by
    ext q p
    exact inverseActionLMatrix_eq_fSymbol a b x y q p
  constructor
  · rw [hL, hI, ← complexOfGolden_mul, (printedL_inverseGolden a b x y).1,
      complexOfGolden_one]
  · rw [hL, hI, ← complexOfGolden_mul, (printedL_inverseGolden a b x y).2,
      complexOfGolden_one]
/-- Left-associated fusion analysis over the golden integers. -/
def fusionLeftAnalysisGolden (a b x y : Fin 2)
    (q : FusionLeftMultiplicity fibNim a b x y) :
    Matrix (Fin (fibBlockDim y))
      ((Fin (fibBlockDim a) × Fin (fibBlockDim b)) × Fin (fibBlockDim x)) GoldenInt :=
  fun u v ↦ ∑ t : Fin (fibBlockDim q.1),
    fusionAnalysisGolden q.1 x y q.2.2 u (finProdFinEquiv (t, v.2)) *
      fusionAnalysisGolden a b q.1 q.2.1 t (finProdFinEquiv v.1)
/-- Right-associated fusion synthesis over the golden integers. -/
def fusionRightSynthesisGolden (a b x y : Fin 2)
    (p : FusionRightMultiplicity fibNim a b x y) :
    Matrix ((Fin (fibBlockDim a) × Fin (fibBlockDim b)) × Fin (fibBlockDim x))
      (Fin (fibBlockDim y)) GoldenInt :=
  fun v u ↦ ∑ t : Fin (fibBlockDim p.1),
    fusionSynthesisGolden b x p.1 p.2.1 (finProdFinEquiv (v.1.2, v.2)) t *
      fusionSynthesisGolden a p.1 y p.2.2 (finProdFinEquiv (v.1.1, t)) u
private theorem fusion_crossGolden : ∀ (a b x y : Fin 2)
    (q : FusionLeftMultiplicity fibNim a b x y)
    (p : FusionRightMultiplicity fibNim a b x y),
    fusionLeftAnalysisGolden a b x y q * fusionRightSynthesisGolden a b x y p =
      fibFSymbolGolden a b x y q.1 p.1 •
        (1 : Matrix (Fin (fibBlockDim y)) (Fin (fibBlockDim y)) GoldenInt) := by
  decide +kernel
/-- The same fusion gauge gives the printed Fibonacci F symbols, using
`fusionFMatrix`'s left-analysis/right-synthesis orientation. -/
theorem fusionFMatrix_eq_fSymbol (a b x y : Fin 2)
    (q : FusionLeftMultiplicity fibNim a b x y)
    (p : FusionRightMultiplicity fibNim a b x y) :
    fusionFMatrix fusionAnalysis fusionSynthesis a b x y q p =
      goldenToComplex (fibFSymbolGolden a b x y q.1 p.1) := by
  have hH : (fun (u : Fin (fibBlockDim y))
      (v : (Fin (fibBlockDim a) × Fin (fibBlockDim b)) × Fin (fibBlockDim x)) ↦
        ∑ t : Fin (fibBlockDim q.1),
          fusionAnalysis q.1 x y q.2.2 u (finProdFinEquiv (t, v.2)) *
            fusionAnalysis a b q.1 q.2.1 t (finProdFinEquiv v.1)) =
      complexOfGolden (fusionLeftAnalysisGolden a b x y q) := by
    ext u v
    simp [fusionAnalysis, fusionLeftAnalysisGolden, map_sum, map_mul]
  have hS : (fun
      (v : (Fin (fibBlockDim a) × Fin (fibBlockDim b)) × Fin (fibBlockDim x))
      (u : Fin (fibBlockDim y)) ↦
        ∑ t : Fin (fibBlockDim p.1),
          fusionSynthesis b x p.1 p.2.1 (finProdFinEquiv (v.1.2, v.2)) t *
            fusionSynthesis a p.1 y p.2.2 (finProdFinEquiv (v.1.1, t)) u) =
      complexOfGolden (fusionRightSynthesisGolden a b x y p) := by
    ext v u
    simp [fusionSynthesis, fusionRightSynthesisGolden, map_sum, map_mul]
  rcases q with ⟨c, μ, k⟩
  rcases p with ⟨z, j, i⟩
  change (fibBlockDim y : ℂ)⁻¹ * Matrix.trace (_ * _) = _
  rw [hH, hS, ← complexOfGolden_mul, fusion_crossGolden,
    complexOfRing_smul, complexOfGolden_one]
  apply inv_dim_trace
  fin_cases y <;> decide
/-- The actual L and F constructions agree after the explicit channel gauges
and the source's reversal of left/right multiplicity index types.
This is the construction for the displayed two normal blocks, not a
classification of all module associativity structures.
Source: GLM23, lines 605 and 1991--1993. -/
theorem actionLMatrix_eq_fusionFMatrix (a b x y : Fin 2)
    (p : SequentialActionMultiplicity fibNim a b x y)
    (q : FusionActionMultiplicity fibNim fibNim a b x y) :
    actionLMatrix fusionSynthesis actionAnalysis actionSynthesis a b x y p q =
      fusionFMatrix fusionAnalysis fusionSynthesis a b x y
        ⟨q.1, q.2.2, q.2.1⟩ ⟨p.1, p.2.2, p.2.1⟩ := by
  rw [actionLMatrix_eq_fSymbol, fusionFMatrix_eq_fSymbol]
end FibonacciCompression.Boundary
