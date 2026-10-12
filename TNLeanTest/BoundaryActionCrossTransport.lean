/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionCrossTransport

/-!
# Regression checks for rectangular endpoint action transport

The reverse endpoint sector uses the transpose of an arbitrary rectangular
matrix. The exact raw L equality is reversed by symmetry; no inverse L,
common F matrix, or operator injectivity is supplied.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d₀ d₁ r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)
  {O₀ : ∀ a, MPOTensor d₀ (χ₀ a)} {A₀ : MPSTensor d₀ D₀}
  {O₁ : ∀ a, MPOTensor d₁ (χ₁ a)} {A₁ : MPSTensor d₁ D₁}
  (hF₀ : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O₀ a) A₀)
    (fun _ : Fin (m a) ↦ A₀) (VA₀ a) (WA₀ a))
  (hF₁ : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a, MPSTensor.IsBiorthogonalDecomposition (actTensor (O₁ a) A₁)
    (fun _ : Fin (m a) ↦ A₁) (VA₁ a) (WA₁ a))
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
example
    (a b : Fin r)
    (hL : actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0)
    (X : Matrix (Fin D₀) (Fin D₁) ℂ) :
    (∑ p : SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
      sequentialActionSynthesis (fun a _ _ ↦ WA₁ a) a b 0
          (sequentialActionPathEquiv a b 0 ⟨0, p⟩) * Xᵀ *
        sequentialActionAnalysis (fun a _ _ ↦ VA₀ a) a b 0
          (sequentialActionPathEquiv a b 0 ⟨0, p⟩)) =
    ∑ q : FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0,
      fusionThenActionSynthesis WF₁ (fun a _ _ ↦ WA₁ a) a b 0
          (fusionActionPathEquiv a b 0 ⟨0, q⟩) * Xᵀ *
        fusionThenActionAnalysis VF₀ (fun a _ _ ↦ VA₀ a) a b 0
          (fusionActionPathEquiv a b 0 ⟨0, q⟩) := by
  exact crossEndpoint_actionTree_contraction_of_actionLMatrix_eq
    VF₁ WF₁ VA₁ WA₁ VF₀ WF₀ VA₀ WA₀ hF₁ hA₁ hF₀ hA₀
    hInj₁ hInj₀ hD₁ hD₀ a b hL.symm Xᵀ

end MPOTensor

set_option linter.hashCommand false

/--
info: 'MPOTensor.actionLMatrix_synthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.actionLMatrix_synthesis

/--
info: 'MPOTensor.singleState_actionLMatrix_relations'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.singleState_actionLMatrix_relations

/--
info: 'MPOTensor.crossEndpoint_actionTree_contraction_of_actionLMatrix_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.crossEndpoint_actionTree_contraction_of_actionLMatrix_eq

/--
info: 'MPOTensor.crossEndpoint_actionTree_contraction_apply_of_actionLMatrix_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.crossEndpoint_actionTree_contraction_apply_of_actionLMatrix_eq
