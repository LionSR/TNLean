/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionLMatrix

/-!
# Actual multiplicity L-matrix regressions

These signatures use exact fusion/action maps, derive target separation from
individual injectivity, and do not assume an L matrix or a coherence law.
-/

set_option linter.hashCommand false

open scoped Matrix BigOperators Kronecker

namespace BoundaryActionLMatrixTest

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (MPOTensor.mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (MPOTensor.actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
  (hInj : ∀ y, Kraus.IsInjective (A y)) (hD : ∀ y, 0 < D y)
  (hne : MPSTensor.BlocksNotGaugePhaseEquiv A)

include hF hA hInj hD hne in
example (a b : Fin r) (x y : Fin s) :
    MPOTensor.actionLMatrix WF VA WA a b x y *
        MPOTensor.inverseActionLMatrix VF VA WA a b x y = 1 ∧
      MPOTensor.inverseActionLMatrix VF VA WA a b x y *
        MPOTensor.actionLMatrix WF VA WA a b x y = 1 :=
  MPOTensor.actionLMatrix_inverse_of_isInjective VF WF VA WA hF hA hD hInj hne a b x y

-- This is the actual analysis-tree equation, in the printed source direction.
include hF hA hInj hD hne in
example (a b : Fin r) (x : Fin s) :
    Matrix.blockDiagonal' (fun y ↦ MPOTensor.actionLMatrix WF VA WA a b x y ⊗ₖ
        (1 : Matrix (Fin (D y)) (Fin (D y)) ℂ)) *
      (MPSTensor.decompositionAnalysis
        (MPOTensor.fusionThenActionAnalysis VF VA a b x)).submatrix
        (MPOTensor.fusionActionCoordinateEquiv (D := D) a b x) id =
      (MPSTensor.decompositionAnalysis (MPOTensor.sequentialActionAnalysis VA a b x)).submatrix
        (MPOTensor.sequentialActionCoordinateEquiv (D := D) a b x) id := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hD hne
  exact MPOTensor.actionLMatrix_analysis VF WF VA WA hF hA
    (fun y ↦ (hInj y).isNormal) hD a b x hL hSpan

/-- info: 'MPOTensor.fusionThenAction_isBiorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.fusionThenAction_isBiorthogonal
/-- info: 'MPOTensor.sequentialAction_isBiorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.sequentialAction_isBiorthogonal
/-- info: 'MPOTensor.fullActionComparison_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.fullActionComparison_spec
/-- info: 'MPOTensor.actionLMatrix_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.actionLMatrix_cross
/-- info: 'MPOTensor.actionLMatrix_inverse_of_isInjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.actionLMatrix_inverse_of_isInjective
/-- info: 'MPOTensor.actionLMatrix_analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.actionLMatrix_analysis

end BoundaryActionLMatrixTest
