/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusion

/-!
# Regression checks for exact mixed endpoint fusion

The endpoint-exchanged construction needs only the reversed raw L equality
for the selected pair. Its independently sized virtual bonds and labelled
fusion targets remain explicit. The axiom guards cover reconstruction,
biorthogonality, arbitrary boundaries, and periodic fusion.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (O₀ : ∀ a, MPOTensor (D₀ * D₀) (χ₀ a))
  (O₁ : ∀ a, MPOTensor (D₁ * D₁) (χ₁ a))
  (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)
  (hF₀ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a, IsBiorthogonalDecomposition (MPOTensor.actTensor (O₀ a) A₀)
    (fun _ : Fin (m a) ↦ A₀) (VA₀ a) (WA₀ a))
  (hF₁ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a, IsBiorthogonalDecomposition (MPOTensor.actTensor (O₁ a) A₁)
    (fun _ : Fin (m a) ↦ A₁) (VA₁ a) (WA₁ a))
  (hInj₀ : Kraus.IsInjective A₀) (hInj₁ : Kraus.IsInjective A₁)
  (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)


include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
example (a b : Fin r)
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor
        (mixedEndpointMPO (O₁ a) (O₀ a) (VA₁ a) (VA₀ a) (WA₁ a) (WA₀ a))
        (mixedEndpointMPO (O₁ b) (O₀ b) (VA₁ b) (VA₀ b) (WA₁ b) (WA₀ b))).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦
        (mixedEndpointMPO (O₁ q.1) (O₀ q.1) (VA₁ q.1) (VA₀ q.1)
          (WA₁ q.1) (WA₀ q.1)).toMPSTensor)
      (fun q ↦ mixedEndpointMPOFusionAnalysis (VF₁ a b q.1 q.2) (VF₀ a b q.1 q.2))
      (fun q ↦ mixedEndpointMPOFusionSynthesis (WF₁ a b q.1 q.2) (WF₀ a b q.1 q.2)) :=
  isBiorthogonalDecomposition_mixedEndpointMPO
    O₁ O₀ A₁ A₀ VF₁ WF₁ VA₁ WA₁ VF₀ WF₀ VA₀ WA₀
    hF₁ hA₁ hF₀ hA₀ hInj₁ hInj₀ hD₁ hD₀ a b hL.symm

end MPSTensor.MPOSymmetry

set_option linter.hashCommand false

/--
info: 'MPOTensor.crossEndpoint_fusion_entry_of_actionLMatrix_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.crossEndpoint_fusion_entry_of_actionLMatrix_eq

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOLetter_fusion'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOLetter_fusion

/--
info: 'MPSTensor.MPOSymmetry.isBiorthogonalDecomposition_mixedEndpointMPO'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isBiorthogonalDecomposition_mixedEndpointMPO

/--
info: 'MPSTensor.MPOSymmetry.mpoWithBoundary_mixedEndpointMPO_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mpoWithBoundary_mixedEndpointMPO_mul

/--
info: 'MPSTensor.MPOSymmetry.isMPOFusionAlgebra_mixedEndpointMPO'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isMPOFusionAlgebra_mixedEndpointMPO
