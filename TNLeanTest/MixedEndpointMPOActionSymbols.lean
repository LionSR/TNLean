/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOActionSymbols
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOAction

/-!
# Actual mixed L-symbol regressions

Independent endpoint dimensions, empty multiplicities, and the two actual
path endpoints are retained. All guarded proofs depend only on standard
kernel axioms.
-/

-- These regressions intentionally inspect kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPSTensor MPSTensor.MPOSymmetry

namespace MixedEndpointMPOActionSymbolsTest

section Symbols

variable {r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)

example (a b : Fin r) :
    MPOTensor.actionLMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) a b 0 0 =
      ((D₀ + D₁ : ℕ) : ℂ)⁻¹ •
        ((D₀ : ℂ) • MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
            (fun a _ _ ↦ WA₀ a) a b 0 0 +
          (D₁ : ℂ) • MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
            (fun a _ _ ↦ WA₁ a) a b 0 0) :=
  actionLMatrix_mixedEndpoint WF₀ VA₀ WA₀ WF₁ VA₁ WA₁ a b

-- Actual interpolation and inherited symbols use the same maps at every
-- real parameter, including zero and one, without endpoint-state injectivity.
example (a b : Fin r) (γ : ℝ)
    (O₀ : MPOTensor (D₀ * D₀) (χ₀ a)) (O₁ : MPOTensor (D₁ * D₁) (χ₁ a))
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor O₀ A₀)
      (fun _ : Fin (m a) ↦ A₀) (VA₀ a) (WA₀ a))
    (hA₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor O₁ A₁)
      (fun _ : Fin (m a) ↦ A₁) (VA₁ a) (WA₁ a))
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    IsBiorthogonalDecomposition
        (MPOTensor.actTensor
          (mixedEndpointMPO O₀ O₁ (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a))
          (mixedEndpointInterpolation A₀ A₁ γ))
        (fun _ : Fin (m a) ↦ mixedEndpointInterpolation A₀ A₁ γ)
        (fun i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i))
        (fun i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) ∧
      MPOTensor.actionLMatrix
          (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
          (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i))
          (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) a b 0 0 =
        MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
          (fun a _ _ ↦ WA₀ a) a b 0 0 :=
  ⟨isBiorthogonalDecomposition_mixedEndpointInterpolation
      O₀ O₁ A₀ A₁ (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a) hA₀ hA₁ γ,
    actionLMatrix_mixedEndpoint_eq_of_eq WF₀ VA₀ WA₀ WF₁ VA₁ WA₁ a b hL⟩

end Symbols

-- Empty endpoint final bonds satisfy the same weighted trace identity.
example (H₀ : Matrix (Fin 0) ((Fin 2 × Fin 3) × Fin 5) ℂ)
    (H₁ : Matrix (Fin 7) ((Fin 11 × Fin 13) × Fin 17) ℂ)
    (S₀ : Matrix ((Fin 2 × Fin 3) × Fin 5) (Fin 0) ℂ)
    (S₁ : Matrix ((Fin 11 × Fin 13) × Fin 17) (Fin 7) ℂ) :
    Matrix.trace (mixedEndpointTripleAnalysis H₀ H₁ *
      mixedEndpointTripleSynthesis S₀ S₁) = Matrix.trace (H₁ * S₁) := by
  rw [mixedEndpointTripleAnalysis_trace_mul_synthesis]
  simp

-- Zero action multiplicity leaves a genuinely empty row space.
example {r D : ℕ} {χ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (VA : ∀ a, Fin 0 → Matrix (Fin D) (Fin (χ a * D)) ℂ)
    (WA : ∀ a, Fin 0 → Matrix (Fin (χ a * D)) (Fin D) ℂ) (a b : Fin r) :
    MPOTensor.actionLMatrix WF (fun a (_ _ : Fin 1) ↦ VA a)
      (fun a _ _ ↦ WA a) a b 0 0 = 0 := by
  ext p q
  exact Fin.elim0 p.2.1

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointTripleAnalysis_mul_synthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointTripleAnalysis_mul_synthesis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointTripleAnalysis_trace_mul_synthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointTripleAnalysis_trace_mul_synthesis

/--
info: 'MPSTensor.MPOSymmetry.finDimension_mul_normalizedTrace'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.finDimension_mul_normalizedTrace

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointTripleAnalysis_normalizedTrace_mul_synthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointTripleAnalysis_normalizedTrace_mul_synthesis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpoint_sequentialActionAnalysis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpoint_sequentialActionAnalysis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpoint_fusionThenActionSynthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpoint_fusionThenActionSynthesis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpoint_actionTree_cross'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpoint_actionTree_cross

/--
info: 'MPSTensor.MPOSymmetry.actionLMatrix_mixedEndpoint'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.actionLMatrix_mixedEndpoint

/--
info: 'MPSTensor.MPOSymmetry.actionLMatrix_mixedEndpoint_eq_of_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.actionLMatrix_mixedEndpoint_eq_of_eq

end MixedEndpointMPOActionSymbolsTest
