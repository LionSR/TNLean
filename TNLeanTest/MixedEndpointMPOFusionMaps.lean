/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusionMaps

/-!
# Mixed endpoint fusion map regressions

The endpoint incoming and outgoing dimensions are independent. Rectangular
analysis-synthesis products permit different outgoing channels, and the
unmatched incoming sectors vanish without any completeness assumption.
-/

-- These regressions intentionally inspect kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPSTensor.MPOSymmetry

namespace MixedEndpointMPOFusionMapsTest

example (V₀ : Matrix (Fin 5) (Fin (2 * 3)) ℂ)
    (V₁ : Matrix (Fin 13) (Fin (7 * 11)) ℂ) :
    Matrix (Fin 18) (Fin 126) ℂ :=
  mixedEndpointMPOFusionAnalysis
    (χa₀ := 2) (χa₁ := 7) (χb₀ := 3) (χb₁ := 11) V₀ V₁

example (W₀ : Matrix (Fin (2 * 3)) (Fin 17) ℂ)
    (W₁ : Matrix (Fin (7 * 11)) (Fin 19) ℂ) :
    Matrix (Fin 126) (Fin 36) ℂ :=
  mixedEndpointMPOFusionSynthesis
    (χa₀ := 2) (χa₁ := 7) (χb₀ := 3) (χb₁ := 11) W₀ W₁

example (V₀ : Matrix (Fin 5) (Fin (2 * 3)) ℂ)
    (V₁ : Matrix (Fin 13) (Fin (7 * 11)) ℂ)
    (W₀ : Matrix (Fin (2 * 3)) (Fin 17) ℂ)
    (W₁ : Matrix (Fin (7 * 11)) (Fin 19) ℂ) :
    mixedEndpointMPOFusionAnalysis
        (χa₀ := 2) (χa₁ := 7) (χb₀ := 3) (χb₁ := 11) V₀ V₁ *
      mixedEndpointMPOFusionSynthesis W₀ W₁ =
        (Matrix.fromBlocks (V₀ * W₀) 0 0 (V₁ * W₁)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm :=
  mixedEndpointMPOFusionAnalysis_mul_synthesis V₀ V₁ W₀ W₁

section Unmatched

variable {χa₀ χa₁ χb₀ χb₁ χc₀ χc₁ χd₀ χd₁ : ℕ}
  (W₀ : Matrix (Fin (χa₀ * χb₀)) (Fin χc₀) ℂ)
  (W₁ : Matrix (Fin (χa₁ * χb₁)) (Fin χc₁) ℂ)
  (V₀ : Matrix (Fin χd₀) (Fin (χa₀ * χb₀)) ℂ)
  (V₁ : Matrix (Fin χd₁) (Fin (χa₁ * χb₁)) ℂ)

example (α : Fin χa₀) (β : Fin χb₁) (r : Fin χc₀ ⊕ Fin χc₁) :
    mixedEndpointFusionSynthesis W₀ W₁ (.inl α, .inr β) r = 0 := by
  cases r <;> rfl

example (α : Fin χa₁) (β : Fin χb₀) (r : Fin χd₀ ⊕ Fin χd₁) :
    mixedEndpointFusionAnalysis V₀ V₁ r (.inr α, .inl β) = 0 := by
  cases r <;> rfl

example (α : Fin χa₀) (β : Fin χb₁) (r : Fin (χc₀ + χc₁)) :
    mixedEndpointMPOFusionSynthesis W₀ W₁
      (mixedEndpointActedEquiv χa₀ χa₁ χb₀ χb₁ (.inl α, .inr β)) r = 0 := by
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective r
  cases r <;> simp [mixedEndpointMPOFusionSynthesis, mixedEndpointFusionSynthesis]

example (M : Matrix (Fin χc₀ ⊕ Fin χc₁) (Fin χd₀ ⊕ Fin χd₁) ℂ)
    (α : Fin χa₀) (β : Fin χb₁)
    (q : (Fin χa₀ ⊕ Fin χa₁) × (Fin χb₀ ⊕ Fin χb₁)) :
    (mixedEndpointFusionSynthesis W₀ W₁ * M * mixedEndpointFusionAnalysis V₀ V₁)
      (.inl α, .inr β) q = 0 := by
  rw [mixedEndpointFusion_sandwich_apply]

example (M : Matrix (Fin χc₀ ⊕ Fin χc₁) (Fin χd₀ ⊕ Fin χd₁) ℂ)
    (α : Fin χa₀) (β : Fin χb₀) (γ : Fin χa₁) (δ : Fin χb₁) :
    (mixedEndpointFusionSynthesis W₀ W₁ * M * mixedEndpointFusionAnalysis V₀ V₁)
        (.inl α, .inl β) (.inr γ, .inr δ) =
      (W₀ * M.submatrix Sum.inl Sum.inr * V₁)
        (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)) := by
  rw [mixedEndpointFusion_sandwich_apply]

end Unmatched

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointFusionAnalysis_mul_synthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointFusionAnalysis_mul_synthesis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusionAnalysis_mul_synthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusionAnalysis_mul_synthesis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointFusion_sandwich_apply'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointFusion_sandwich_apply

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_sandwich'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_sandwich

end MixedEndpointMPOFusionMapsTest
