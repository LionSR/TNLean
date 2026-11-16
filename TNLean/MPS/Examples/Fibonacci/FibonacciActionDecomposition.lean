/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciFSymbol
import TNLean.MPS.MPDO.BoundaryActionTreeEntries
/-!
# Exact boundary decompositions for the two Fibonacci states
The normal states are the existing all-tau product state and its Fibonacci
operator image. All four fusion pairs and all four actions are decomposed
at the unblocked letter level. Analysis and synthesis are independent
biorthogonal maps. The gauge is explicit: action analysis in the tau-tau-tau
channel is multiplied by sigma, and fusion analysis in the tau-tau-one and
tau-tau-tau channels by sigma and minus its inverse, respectively.
Source: GLM23, arXiv:2203.12563v3, `fusiontensors`, `fusiontensors2`,
`eq:orthoV`, the gauge transformations at lines 595--605, and the Fibonacci
example at lines 1991--1993. The explicit states and maps are constructions
of this development. The MPO-entry provenance restriction is recorded in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.
-/
open scoped Matrix BigOperators Kronecker
open MPSTensor MPOTensor GoldenInt
namespace FibonacciCompression.Boundary
/-- The existing Fibonacci operator blocks over the golden integers. -/
def operatorGolden : (a : Fin 2) → Fin 2 → Fin 2 →
    Matrix (Fin (fibBlockDim a)) (Fin (fibBlockDim a)) GoldenInt
  | 0 => fibOneGolden
  | 1 => fibTauGolden
/-- The analysis gauge on the three action labels. Source: GLM23, lines 595--605. -/
def actionGauge (a x y : Fin 2) : GoldenInt :=
  if (a, x, y) = (1, 1, 1) then sigma else 1
/-- The reciprocal action gauge, written as a golden integer. -/
def actionGaugeInv (a x y : Fin 2) : GoldenInt :=
  if (a, x, y) = (1, 1, 1) then sigma + sigma ^ 3 else 1
/-- The fusion analysis gauge. Source: GLM23, lines 595--605. -/
def fusionGauge (a b c : Fin 2) : GoldenInt :=
  if (a, b, c) = (1, 1, 0) then sigma
  else if (a, b, c) = (1, 1, 1) then -(sigma + sigma ^ 3) else 1
/-- The reciprocal fusion gauge, written as a golden integer. -/
def fusionGaugeInv (a b c : Fin 2) : GoldenInt :=
  if (a, b, c) = (1, 1, 0) then sigma + sigma ^ 3
  else if (a, b, c) = (1, 1, 1) then -sigma else 1
/-- Each displayed gauge is a unit; synthesis uses the inverse scale. -/
theorem gauge_mul_inv : ∀ a b c : Fin 2,
    actionGauge a b c * actionGaugeInv a b c = 1 ∧
      fusionGauge a b c * fusionGaugeInv a b c = 1 := by
  decide +kernel
/-- The complex action and fusion scales are nonzero, so these are valid
channel gauges. Source: GLM23, lines 595--605. -/
theorem gauge_ne_zero (a b c : Fin 2) :
    goldenToComplex (actionGauge a b c) ≠ 0 ∧
      goldenToComplex (fusionGauge a b c) ≠ 0 := by
  constructor
  · intro h
    have he := congrArg goldenToComplex (gauge_mul_inv a b c).1
    rw [map_mul, map_one, h, zero_mul] at he
    exact zero_ne_one he
  · intro h
    have he := congrArg goldenToComplex (gauge_mul_inv a b c).2
    rw [map_mul, map_one, h, zero_mul] at he
    exact zero_ne_one he

/-- Target rows of the recorded fusion gauges. -/
def fusionAnalysisRawGolden : (a b c : Fin 2) →
    Fin (fibNim a b c) →
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) GoldenInt
  | 0, 0, 0, _ => fibOneOneGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 0, 1, 1, _ => fibOneTauGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 1, 0, 1, _ => fibTauOneGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 1, 1, 0, _ => fibGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 1, 1, 1, _ => fibGaugeGolden.submatrix (fun i ↦ ⟨2 + i.val, by omega⟩) id
  | _, _, _, _ => 0
/-- The fusion analysis after the explicit scalar gauge. -/
def fusionAnalysisGolden (a b c : Fin 2)
    (μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) GoldenInt :=
  fusionGauge a b c • fusionAnalysisRawGolden a b c μ
/-- The complex fusion analysis maps. -/
noncomputable def fusionAnalysis (a b c : Fin 2)
    (μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) ℂ :=
  complexOfGolden (fusionAnalysisGolden a b c μ)
/-- Target columns of the recorded fusion gauges. -/
def fusionSynthesisRawGolden : (a b c : Fin 2) →
    Fin (fibNim a b c) →
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) GoldenInt
  | 0, 0, 0, _ => fibOneOneGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 0, 1, 1, _ => fibOneTauGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 1, 0, 1, _ => fibTauOneGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 1, 1, 0, _ => fibGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 1, 1, 1, _ => fibGaugeInvGolden.submatrix id (fun i ↦ ⟨2 + i.val, by omega⟩)
  | _, _, _, _ => 0
/-- The fusion synthesis after the explicit scalar gauge. -/
def fusionSynthesisGolden (a b c : Fin 2)
    (μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) GoldenInt :=
  fusionGaugeInv a b c • fusionSynthesisRawGolden a b c μ
/-- The complex fusion synthesis maps. -/
noncomputable def fusionSynthesis (a b c : Fin 2)
    (μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) ℂ :=
  complexOfGolden (fusionSynthesisGolden a b c μ)
/-- Target rows of the recorded action gauges. -/
def actionAnalysisRawGolden : (a x y : Fin 2) →
    Fin (fibNim a x y) → Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) GoldenInt
  | 0, 0, 0, _ => fibUnitAllTauGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 1, 0, 1, _ => fibActAllTauGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 1, 1, 0, _ => fibActChainGaugeGolden.submatrix (fun i ↦ ⟨0 + i.val, by omega⟩) id
  | 1, 1, 1, _ => fibActChainGaugeGolden.submatrix (fun i ↦ ⟨1 + i.val, by omega⟩) id
  | 0, 1, 1, _ => !![1, -sigma ^ 2, 1, 0; 0, 0, 0, 1]
  | _, _, _, _ => 0
/-- The action analysis after the explicit scalar gauge. -/
def actionAnalysisGolden (a x y : Fin 2)
    (μ : Fin (fibNim a x y)) :
    Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) GoldenInt :=
  actionGauge a x y • actionAnalysisRawGolden a x y μ
/-- The complex action analysis maps. -/
noncomputable def actionAnalysis (a x y : Fin 2)
    (μ : Fin (fibNim a x y)) : Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) ℂ :=
  complexOfGolden (actionAnalysisGolden a x y μ)
/-- Target columns of the recorded action gauges. -/
def actionSynthesisRawGolden : (a x y : Fin 2) →
    Fin (fibNim a x y) → Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) GoldenInt
  | 0, 0, 0, _ => fibUnitAllTauGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 1, 0, 1, _ => fibActAllTauGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 1, 1, 0, _ => fibActChainGaugeInvGolden.submatrix id (fun i ↦ ⟨0 + i.val, by omega⟩)
  | 1, 1, 1, _ => fibActChainGaugeInvGolden.submatrix id (fun i ↦ ⟨1 + i.val, by omega⟩)
  | 0, 1, 1, _ => !![1, 0; 0, 0; 0, 0; 0, 1]
  | _, _, _, _ => 0
/-- The action synthesis after the explicit scalar gauge. -/
def actionSynthesisGolden (a x y : Fin 2)
    (μ : Fin (fibNim a x y)) :
    Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) GoldenInt :=
  actionGaugeInv a x y • actionSynthesisRawGolden a x y μ
/-- The complex action synthesis maps. -/
noncomputable def actionSynthesis (a x y : Fin 2)
    (μ : Fin (fibNim a x y)) : Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) ℂ :=
  complexOfGolden (actionSynthesisGolden a x y μ)
private theorem fusion_retractGolden : ∀ (a b : Fin 2)
    (q : (c : Fin 2) × Fin (fibNim a b c)),
    fusionAnalysisGolden a b q.1 q.2 * fusionSynthesisGolden a b q.1 q.2 = 1 := by
  decide +kernel
private theorem fusion_orthogonalGolden : ∀ (a b : Fin 2)
    (q t : (c : Fin 2) × Fin (fibNim a b c)), q ≠ t →
    fusionAnalysisGolden a b q.1 q.2 * fusionSynthesisGolden a b t.1 t.2 = 0 := by
  decide +kernel
private theorem action_retractGolden : ∀ (a x : Fin 2)
    (q : (y : Fin 2) × Fin (fibNim a x y)),
    actionAnalysisGolden a x q.1 q.2 * actionSynthesisGolden a x q.1 q.2 = 1 := by
  decide +kernel
private theorem action_orthogonalGolden : ∀ (a x : Fin 2)
    (q t : (y : Fin 2) × Fin (fibNim a x y)), q ≠ t →
    actionAnalysisGolden a x q.1 q.2 * actionSynthesisGolden a x t.1 t.2 = 0 := by
  decide +kernel
private theorem fusion_letterGolden : ∀ (a b i k : Fin 2),
    mulTensorR (operatorGolden a) (operatorGolden b) i k =
      ∑ q : (c : Fin 2) × Fin (fibNim a b c),
        fusionSynthesisGolden a b q.1 q.2 * operatorGolden q.1 i k *
          fusionAnalysisGolden a b q.1 q.2 := by
  decide +kernel
private theorem action_letterGolden : ∀ (a x i : Fin 2),
    actTensorR (operatorGolden a) (fibNimTargetsGolden x) i =
      ∑ q : (y : Fin 2) × Fin (fibNim a x y),
        actionSynthesisGolden a x q.1 q.2 * fibNimTargetsGolden q.1 i *
          actionAnalysisGolden a x q.1 q.2 := by
  decide +kernel
private theorem operator_eq (a : Fin 2) :
    fibBlock a = fun i j ↦ complexOfGolden (operatorGolden a i j) := by
  fin_cases a <;> rfl
/-- Exact unblocked Fibonacci fusion decompositions, including empty channels.
Source: GLM23, `fusiontensors` and `eq:orthoW`. -/
theorem fusion_isBiorthogonal (a b : Fin 2) :
    IsBiorthogonalDecomposition (mulTensor (fibBlock a) (fibBlock b)).toMPSTensor
      (fun q : (c : Fin 2) × Fin (fibNim a b c) ↦ (fibBlock q.1).toMPSTensor)
      (fun q ↦ fusionAnalysis a b q.1 q.2) (fun q ↦ fusionSynthesis a b q.1 q.2) where
  retract q := by
    rw [fusionAnalysis, fusionSynthesis, ← complexOfGolden_mul,
      fusion_retractGolden, complexOfGolden_one]
  orthogonal q t h := by
    rw [fusionAnalysis, fusionSynthesis, ← complexOfGolden_mul,
      fusion_orthogonalGolden a b q t h, complexOfGolden_zero]
  letter ij := by
    change mulTensor (fibBlock a) (fibBlock b) ij.divNat ij.modNat = _
    rw [operator_eq a, operator_eq b, mulTensor_complexOfRing,
      fusion_letterGolden, complexOfRing_sum]
    simp only [complexOfGolden_mul]
    congr 1
    funext q
    rw [operator_eq q.1]
    rfl
/-- Exact unblocked action decompositions for the existing two normal states.
Source: GLM23, `fusiontensors2` and `eq:orthoV`. -/
theorem action_isBiorthogonal (a x : Fin 2) :
    IsBiorthogonalDecomposition (actTensor (fibBlock a) (fibNimTargets x))
      (fun q : (y : Fin 2) × Fin (fibNim a x y) ↦ fibNimTargets q.1)
      (fun q ↦ actionAnalysis a x q.1 q.2) (fun q ↦ actionSynthesis a x q.1 q.2) where
  retract q := by
    rw [actionAnalysis, actionSynthesis, ← complexOfGolden_mul,
      action_retractGolden, complexOfGolden_one]
  orthogonal q t h := by
    rw [actionAnalysis, actionSynthesis, ← complexOfGolden_mul,
      action_orthogonalGolden a x q t h, complexOfGolden_zero]
  letter i := by
    have hA : fibNimTargets x = fun j ↦ complexOfGolden (fibNimTargetsGolden x j) :=
      funext (fibNimTargets_eq x)
    rw [operator_eq a, hA, actTensor_complexOfRing, action_letterGolden,
      complexOfRing_sum]
    simp only [complexOfGolden_mul]
    congr 1
    funext q
    rw [fibNimTargets_eq]
    rfl
/-- Both displayed state blocks are normal, with positive bond dimensions. -/
theorem states_isNormal (x : Fin 2) : Kraus.IsNormal (fibNimTargets x) := by
  fin_cases x
  · exact fibAllTau_isNormal
  · exact fibChain_isNormal
/-- Both explicitly constructed action trees reconstruct the same double-action
letters with biorthogonal summands. Source: GLM23, `rawrels`. -/
theorem actionTrees_isBiorthogonal (a b x : Fin 2) :
    IsBiorthogonalDecomposition
      (actTensor (mulTensor (fibBlock a) (fibBlock b)) (fibNimTargets x))
      (fun q : FusionActionPath fibNim fibNim a b x ↦ fibNimTargets q.2.1)
      (fusionThenActionAnalysis fusionAnalysis actionAnalysis a b x)
      (fusionThenActionSynthesis fusionSynthesis actionSynthesis a b x) ∧
    IsBiorthogonalDecomposition
      (actTensor (mulTensor (fibBlock a) (fibBlock b)) (fibNimTargets x))
      (fun q : SequentialActionPath fibNim a b x ↦ fibNimTargets q.2.1)
      (sequentialActionAnalysis actionAnalysis a b x)
      (sequentialActionSynthesis actionSynthesis a b x) :=
  ⟨fusionThenAction_isBiorthogonal fusionAnalysis fusionSynthesis actionAnalysis actionSynthesis
      fusion_isBiorthogonal action_isBiorthogonal a b x,
    sequentialAction_isBiorthogonal actionAnalysis actionSynthesis action_isBiorthogonal a b x⟩
end FibonacciCompression.Boundary
