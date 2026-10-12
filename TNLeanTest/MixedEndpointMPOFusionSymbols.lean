/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusionSymbols

/-!
# Mixed endpoint source F-symbol regressions

The tests use the actual chosen fusion maps, retain the source row/column
orientation, permit independent endpoint dimensions and zero multiplicities,
and check the endpoint-to-mixed F-move lift. Kernel-dependency guards reject
any additional proof assumption beyond the standard Lean axioms.
-/

set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPOTensor MPSTensor.MPOSymmetry

namespace MixedEndpointMPOFusionSymbolsTest

section General

variable {r : ℕ} {χ₀ χ₁ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}
  (V₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (W₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (V₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (W₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)

example (a b c d e : Fin r) (mu : Fin (N a b e)) (nu : Fin (N e c d))
    (z : Fin (χ₀ d)) (α : Fin (χ₀ a)) (β : Fin (χ₀ b)) (γ : Fin (χ₀ c)) :
    fusionLeftTreeAnalysis V₀ a b c d ⟨e, mu, nu⟩ z ((α, β), γ) =
      ∑ t : Fin (χ₀ e), V₀ e c d nu z (finProdFinEquiv (t, γ)) *
        V₀ a b e mu t (finProdFinEquiv (α, β)) := rfl

example (a b c d f : Fin r) (lambda : Fin (N b c f)) (sigma : Fin (N a f d))
    (z : Fin (χ₁ d)) (α : Fin (χ₁ a)) (β : Fin (χ₁ b)) (γ : Fin (χ₁ c)) :
    fusionRightTreeSynthesis W₁ a b c d ⟨f, lambda, sigma⟩ ((α, β), γ) z =
      ∑ t : Fin (χ₁ f), W₁ b c f lambda (finProdFinEquiv (β, γ)) t *
        W₁ a f d sigma (finProdFinEquiv (α, t)) z := rfl

example (a b c d : Fin r) (q : FusionLeftMultiplicity N a b c d)
    (t : FusionRightMultiplicity N a b c d) :
    fusionFMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
        a b c d q t =
      ((χ₀ d + χ₁ d : ℕ) : ℂ)⁻¹ *
        ((χ₀ d : ℂ) * fusionFMatrix V₀ W₀ a b c d q t +
          (χ₁ d : ℂ) * fusionFMatrix V₁ W₁ a b c d q t) :=
  mixedEndpointMPOFusion_fusionFMatrix_eq_weighted V₀ W₀ V₁ W₁ a b c d q t

example (a b c d : Fin r)
    (hF : fusionFMatrix V₀ W₀ a b c d = fusionFMatrix V₁ W₁ a b c d) :
    fusionFMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
        a b c d = fusionFMatrix V₀ W₀ a b c d :=
  mixedEndpointMPOFusion_fusionFMatrix_of_eq V₀ W₀ V₁ W₁ a b c d hF

example (a b c d : Fin r)
    (hF : fusionFMatrix V₀ W₀ a b c d = fusionFMatrix V₁ W₁ a b c d)
    (hMove₀ : ∀ q : FusionLeftMultiplicity N a b c d,
      fusionLeftTreeAnalysis V₀ a b c d q =
        ∑ t : FusionRightMultiplicity N a b c d,
          fusionFMatrix V₀ W₀ a b c d q t • fusionRightTreeAnalysis V₀ a b c d t)
    (hMove₁ : ∀ q : FusionLeftMultiplicity N a b c d,
      fusionLeftTreeAnalysis V₁ a b c d q =
        ∑ t : FusionRightMultiplicity N a b c d,
          fusionFMatrix V₁ W₁ a b c d q t • fusionRightTreeAnalysis V₁ a b c d t)
    (q : FusionLeftMultiplicity N a b c d) :
    fusionLeftTreeAnalysis
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        a b c d q =
      ∑ t : FusionRightMultiplicity N a b c d,
        fusionFMatrix
            (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
            (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
            a b c d q t •
          fusionRightTreeAnalysis
            (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
            a b c d t :=
  mixedEndpointMPOFusion_fusionFMatrix_analysis
    V₀ W₀ V₁ W₁ a b c d hF hMove₀ hMove₁ q

end General

section EmptyBonds

variable {r : ℕ} {χ₁ : Fin r → ℕ} {N : Fin r → Fin r → Fin r → ℕ}
  (V₀ : ∀ a b c : Fin r, Fin (N a b c) → Matrix (Fin 0) (Fin (0 * 0)) ℂ)
  (W₀ : ∀ a b c : Fin r, Fin (N a b c) → Matrix (Fin (0 * 0)) (Fin 0) ℂ)
  (V₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (W₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)

-- A zero-dimensional endpoint contributes zero without requiring its positivity.
example (a b c d : Fin r) (hχ : 0 < χ₁ d)
    (q : FusionLeftMultiplicity N a b c d) (t : FusionRightMultiplicity N a b c d) :
    fusionFMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
        a b c d q t = fusionFMatrix V₁ W₁ a b c d q t := by
  rw [mixedEndpointMPOFusion_fusionFMatrix_eq_weighted]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hχ), one_mul]

end EmptyBonds

-- Empty fusion channels are permitted even with different endpoint bond dimensions.
example
    (V₀ : ∀ (_ _ _ : Fin 1), Fin 0 → Matrix (Fin 2) (Fin (2 * 2)) ℂ)
    (W₀ : ∀ (_ _ _ : Fin 1), Fin 0 → Matrix (Fin (2 * 2)) (Fin 2) ℂ)
    (V₁ : ∀ (_ _ _ : Fin 1), Fin 0 → Matrix (Fin 3) (Fin (3 * 3)) ℂ)
    (W₁ : ∀ (_ _ _ : Fin 1), Fin 0 → Matrix (Fin (3 * 3)) (Fin 3) ℂ) :
    fusionFMatrix (N := fun _ _ _ ↦ 0)
        (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (V₀ a b c μ) (V₁ a b c μ))
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (W₀ a b c μ) (W₁ a b c μ))
        0 0 0 0 = fusionFMatrix V₀ W₀ 0 0 0 0 := by
  apply mixedEndpointMPOFusion_fusionFMatrix_of_eq V₀ W₀ V₁ W₁ 0 0 0 0
  ext q t
  exact Fin.elim0 q.2.1

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_leftTreeAnalysis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_leftTreeAnalysis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_rightTreeAnalysis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_rightTreeAnalysis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_rightTreeSynthesis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_rightTreeSynthesis

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_fusionFMatrix_eq_weighted'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_fusionFMatrix_eq_weighted

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_fusionFMatrix_of_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_fusionFMatrix_of_eq

/--
info: 'MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_fusionFMatrix_analysis'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpointMPOFusion_fusionFMatrix_analysis

end MixedEndpointMPOFusionSymbolsTest
