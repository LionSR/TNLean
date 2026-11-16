/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciActionTrees
import TNLean.MPS.MPDO.BoundaryActionTreeEntries

/-!
# Exact boundary decompositions for the two Fibonacci states
The normal states and exact maps are reused from `FibonacciActionTrees`.
For both action and fusion, analysis in the tau-tau-one and tau-tau-tau
channels is multiplied by sigma and minus its inverse, respectively;
synthesis receives the reciprocal factors. All four fusion pairs and all
four actions remain exact at the unblocked letter level.
Source: GLM23, arXiv:2203.12563v3, `fusiontensors`, `fusiontensors2`,
`eq:orthoV`, the gauge transformations at lines 595--605, and the Fibonacci
example at lines 1991--1993. The explicit states and maps are constructions
of this development. The MPO-entry provenance restriction is recorded in
`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.
-/
open scoped Matrix BigOperators Kronecker
open MPSTensor MPOTensor GoldenInt
namespace FibonacciCompression.Boundary

/-- The analysis gauge on the three action labels. Source: GLM23, lines 595--605. -/
def actionGauge (a x y : Fin 2) : GoldenInt :=
  if (a, x, y) = (1, 1, 0) then sigma
  else if (a, x, y) = (1, 1, 1) then -(sigma + sigma ^ 3) else 1

/-- The reciprocal action gauge, written as a golden integer. -/
def actionGaugeInv (a x y : Fin 2) : GoldenInt :=
  if (a, x, y) = (1, 1, 0) then sigma + sigma ^ 3
  else if (a, x, y) = (1, 1, 1) then -sigma else 1

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

/-- The fusion analysis after the explicit scalar gauge. -/
def fusionAnalysisGolden (a b c : Fin 2)
    (_μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) GoldenInt :=
  fusionGauge a b c • fibFusionAnalysisGolden a b c

/-- The complex fusion analysis maps. -/
noncomputable def fusionAnalysis (a b c : Fin 2)
    (μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) ℂ :=
  complexOfGolden (fusionAnalysisGolden a b c μ)

/-- The fusion synthesis after the explicit scalar gauge. -/
def fusionSynthesisGolden (a b c : Fin 2)
    (_μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) GoldenInt :=
  fusionGaugeInv a b c • fibFusionSynthesisGolden a b c

/-- The complex fusion synthesis maps. -/
noncomputable def fusionSynthesis (a b c : Fin 2)
    (μ : Fin (fibNim a b c)) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) ℂ :=
  complexOfGolden (fusionSynthesisGolden a b c μ)

/-- The action analysis after the explicit scalar gauge. -/
def actionAnalysisGolden (a x y : Fin 2)
    (_μ : Fin (fibNim a x y)) :
    Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) GoldenInt :=
  actionGauge a x y • fibActAnalysisGolden a x y

/-- The complex action analysis maps. -/
noncomputable def actionAnalysis (a x y : Fin 2)
    (μ : Fin (fibNim a x y)) : Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) ℂ :=
  complexOfGolden (actionAnalysisGolden a x y μ)

/-- The action synthesis after the explicit scalar gauge. -/
def actionSynthesisGolden (a x y : Fin 2)
    (_μ : Fin (fibNim a x y)) :
    Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) GoldenInt :=
  actionGaugeInv a x y • fibActSynthesisGolden a x y

/-- The complex action synthesis maps. -/
noncomputable def actionSynthesis (a x y : Fin 2)
    (μ : Fin (fibNim a x y)) : Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) ℂ :=
  complexOfGolden (actionSynthesisGolden a x y μ)

set_option maxRecDepth 8000 in
private theorem fusion_retractGolden : ∀ (a b : Fin 2)
    (q : (c : Fin 2) × Fin (fibNim a b c)),
    fusionAnalysisGolden a b q.1 q.2 * fusionSynthesisGolden a b q.1 q.2 = 1 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 8000 in
private theorem fusion_orthogonalGolden : ∀ (a b : Fin 2)
    (q t : (c : Fin 2) × Fin (fibNim a b c)), q ≠ t →
    fusionAnalysisGolden a b q.1 q.2 * fusionSynthesisGolden a b t.1 t.2 = 0 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 8000 in
private theorem action_retractGolden : ∀ (a x : Fin 2)
    (q : (y : Fin 2) × Fin (fibNim a x y)),
    actionAnalysisGolden a x q.1 q.2 * actionSynthesisGolden a x q.1 q.2 = 1 := by
  intro a x
  fin_cases a <;> fin_cases x <;> decide +kernel

set_option maxRecDepth 8000 in
private theorem action_orthogonalGolden : ∀ (a x : Fin 2)
    (q t : (y : Fin 2) × Fin (fibNim a x y)), q ≠ t →
    actionAnalysisGolden a x q.1 q.2 * actionSynthesisGolden a x t.1 t.2 = 0 := by
  intro a x
  fin_cases a <;> fin_cases x <;> decide +kernel

set_option maxRecDepth 8000 in
private theorem fusion_letterGolden : ∀ (a b i k : Fin 2),
    mulTensorR (fibBlockGolden a) (fibBlockGolden b) i k =
      ∑ q : (c : Fin 2) × Fin (fibNim a b c),
        fusionSynthesisGolden a b q.1 q.2 * fibBlockGolden q.1 i k *
          fusionAnalysisGolden a b q.1 q.2 := by
  decide +kernel

set_option maxRecDepth 8000 in
private theorem action_letterGolden : ∀ (a x i : Fin 2),
    actTensorR (fibBlockGolden a) (fibNimTargetsGolden x) i =
      ∑ q : (y : Fin 2) × Fin (fibNim a x y),
        actionSynthesisGolden a x q.1 q.2 * fibNimTargetsGolden q.1 i *
          actionAnalysisGolden a x q.1 q.2 := by
  decide +kernel

/-- The standard-gauge fusion maps remain exact at the unblocked letter level.
Source: GLM23, `fusiontensors` and `eq:orthoW`. -/
theorem fusion_isBiorthogonal (a b : Fin 2) :
    IsBiorthogonalDecomposition (mulTensor (fibBlock a) (fibBlock b)).toMPSTensor
      (fun q : (c : Fin 2) × Fin (fibNim a b c) ↦ (fibBlock q.1).toMPSTensor)
      (fun q ↦ fusionAnalysis a b q.1 q.2) (fun q ↦ fusionSynthesis a b q.1 q.2) := by
  have hB : (mulTensor (fibBlock a) (fibBlock b)).toMPSTensor = fun p ↦
      complexOfGolden (mulTensorR (fibBlockGolden a) (fibBlockGolden b) p.divNat p.modNat) := by
    funext p
    change mulTensor (fibBlock a) (fibBlock b) p.divNat p.modNat = _
    rw [fibBlock_eq_complexOfGolden a, fibBlock_eq_complexOfGolden b]
    exact mulTensor_complexOfRing goldenToComplex _ _ _ _
  have hA : (fun q : (c : Fin 2) × Fin (fibNim a b c) ↦ (fibBlock q.1).toMPSTensor) =
      fun (q : (c : Fin 2) × Fin (fibNim a b c)) (p : Fin (2 * 2)) ↦
        complexOfGolden (fibBlockGolden q.1 p.divNat p.modNat) := by
    funext q p
    rw [fibBlock_eq_complexOfGolden q.1]
    rfl
  rw [hB, hA]
  exact isBiorthogonalDecomposition_complexOfRing goldenToComplex _ _
    (fun q : (c : Fin 2) × Fin (fibNim a b c) ↦ fusionAnalysisGolden a b q.1 q.2)
    (fun q : (c : Fin 2) × Fin (fibNim a b c) ↦ fusionSynthesisGolden a b q.1 q.2)
    (fusion_retractGolden a b) (fusion_orthogonalGolden a b)
    (fun p ↦ fusion_letterGolden a b p.divNat p.modNat)

/-- The standard-gauge action maps remain exact for the two existing normal states.
Source: GLM23, `fusiontensors2` and `eq:orthoV`. -/
theorem action_isBiorthogonal (a x : Fin 2) :
    IsBiorthogonalDecomposition (actTensor (fibBlock a) (fibNimTargets x))
      (fun q : (y : Fin 2) × Fin (fibNim a x y) ↦ fibNimTargets q.1)
      (fun q ↦ actionAnalysis a x q.1 q.2) (fun q ↦ actionSynthesis a x q.1 q.2) := by
  have hB : actTensor (fibBlock a) (fibNimTargets x) = fun i ↦
      complexOfGolden (actTensorR (fibBlockGolden a) (fibNimTargetsGolden x) i) := by
    funext i
    rw [fibBlock_eq_complexOfGolden a, fibNimTargets_eq_complexOfGolden x]
    exact actTensor_complexOfRing goldenToComplex _ _ i
  have hA : (fun q : (y : Fin 2) × Fin (fibNim a x y) ↦ fibNimTargets q.1) =
      fun (q : (y : Fin 2) × Fin (fibNim a x y)) (i : Fin 2) ↦
        complexOfGolden (fibNimTargetsGolden q.1 i) := by
    funext q i
    exact fibNimTargets_eq _ _
  rw [hB, hA]
  exact isBiorthogonalDecomposition_complexOfRing goldenToComplex _ _
    (fun q : (y : Fin 2) × Fin (fibNim a x y) ↦ actionAnalysisGolden a x q.1 q.2)
    (fun q : (y : Fin 2) × Fin (fibNim a x y) ↦ actionSynthesisGolden a x q.1 q.2)
    (action_retractGolden a x) (action_orthogonalGolden a x) (action_letterGolden a x)

/-- Both displayed state blocks are normal. -/
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
