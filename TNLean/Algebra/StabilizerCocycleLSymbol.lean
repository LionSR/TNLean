/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CocycleCohomology
import TNLean.Algebra.LSymbol
import TNLean.Algebra.StabilizerTransition

/-!
# L-symbols induced from stabilizer cocycles

This file formalizes the scalar construction in arXiv:2502.20257, Lemma
`lemma:h1h2` and Equations `eq:Lcocycle`, `eq:h1h2` (lines 7028–7042), using
the corrected transition elements from `StabilizerTransition`. The same
construction is Equation (20) of arXiv:2203.12563.

For normalized representatives `k_x` and a scalar cocycle `ψ` on
`H = Stab_G(x₀)`, define

`Lˣ_{g,h} = ψ(t_k(g,h • x), t_k(h,x))`.

The transition-product identity reduces compatibility with the trivial scalar
three-cochain exactly to the cocycle equation for `ψ`. At the basepoint, the
restriction to `H × H` is `ψ`. A coboundary change of `ψ` is the action-tensor
gauge `γ^x_g = φ(t_k(g,x))⁻¹`.

No finiteness, normality, or tensor assumption is used.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X}

namespace StabilizerRepresentatives

/-- The L-symbol induced by a scalar cocycle on the stabilizer of the
basepoint:
`Lˣ_{g,h} = ψ(t_k(g,h • x), t_k(h,x))`. -/
def inducedLSymbol (K : StabilizerRepresentatives G X x₀)
    (ψ : ScalarCocycle (MulAction.stabilizer G x₀)) : LSymbol G X :=
  fun x g h ↦ ψ (K.transitionElement g (h • x)) (K.transitionElement h x)

/-- A stabilizer cocycle induces an L-symbol compatible with the trivial scalar
three-cochain. This is the transition-product/cocycle calculation underlying
arXiv:2502.20257, Equation `eq:Lcocycle`. -/
theorem inducedLSymbol_isCompatible (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} (hψ : ψ.IsCocycle) :
    LSymbol.IsCompatible (K.inducedLSymbol ψ) (fun _ _ _ ↦ 1) := by
  intro x g h k
  simp only [inducedLSymbol, one_mul]
  rw [K.transitionElement_mul h k x, K.transitionElement_mul g h (k • x)]
  simpa only [smul_smul] using
    (hψ (K.transitionElement g ((h * k) • x))
      (K.transitionElement h (k • x)) (K.transitionElement k x)).symm

/-- On a stabilizer element, the transition at the basepoint is that element
itself. -/
theorem transitionElement_stabilizer (K : StabilizerRepresentatives G X x₀)
    (h : MulAction.stabilizer G x₀) :
    K.transitionElement (h : G) x₀ = h := by
  apply Subtype.ext
  rw [K.coe_transitionElement, MulAction.mem_stabilizer_iff.mp h.property, K.k_x₀]
  simp

/-- Restricting the induced L-symbol to the basepoint and stabilizer arguments
recovers the original cocycle representative. -/
theorem inducedLSymbol_base (K : StabilizerRepresentatives G X x₀)
    (ψ : ScalarCocycle (MulAction.stabilizer G x₀))
    (h₁ h₂ : MulAction.stabilizer G x₀) :
    K.inducedLSymbol ψ x₀ (h₁ : G) (h₂ : G) = ψ h₁ h₂ := by
  simp only [inducedLSymbol]
  rw [show (h₂ : G) • x₀ = x₀ from MulAction.mem_stabilizer_iff.mp h₂.property]
  simp [K.transitionElement_stabilizer]

/-- A scalar cochain on the stabilizer determines the action-tensor gauge
`γ^x_g = φ(t_k(g,x))⁻¹`. -/
def inducedActionGauge (K : StabilizerRepresentatives G X x₀)
    (φ : MulAction.stabilizer G x₀ → Units ℂ) : ActionTensorGauge G X :=
  fun g x ↦ (φ (K.transitionElement g x))⁻¹

/-- The coboundary relation between stabilizer cocycles becomes exactly the
existing action-tensor gauge relation between their induced L-symbols. -/
theorem inducedLSymbol_eq_gauge (K : StabilizerRepresentatives G X x₀)
    {ψ₁ ψ₂ : ScalarCocycle (MulAction.stabilizer G x₀)}
    (φ : MulAction.stabilizer G x₀ → Units ℂ)
    (hφ : ∀ a b, ψ₁ a b = φ a * φ b * (φ (a * b))⁻¹ * ψ₂ a b) :
    K.inducedLSymbol ψ₁ =
      LSymbol.gauge (fun _ _ ↦ 1) (K.inducedActionGauge φ)
        (K.inducedLSymbol ψ₂) := by
  funext x g h
  simp only [inducedLSymbol, LSymbol.gauge, inducedActionGauge, mul_one]
  rw [hφ, K.transitionElement_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ac_rfl

/-- Cohomologous stabilizer cocycles induce action-gauge-equivalent L-symbols,
with no change of fusion gauge. -/
theorem exists_actionGauge_inducedLSymbol_eq_of_cohomologousTo
    (K : StabilizerRepresentatives G X x₀)
    {ψ₁ ψ₂ : ScalarCocycle (MulAction.stabilizer G x₀)}
    (hψ : ScalarCocycle.CohomologousTo ψ₁ ψ₂) :
    ∃ γ : ActionTensorGauge G X,
      K.inducedLSymbol ψ₁ =
        LSymbol.gauge (fun _ _ ↦ 1) γ (K.inducedLSymbol ψ₂) := by
  obtain ⟨φ, hφ⟩ := hψ
  exact ⟨K.inducedActionGauge φ, K.inducedLSymbol_eq_gauge φ hφ⟩

end StabilizerRepresentatives

end TNLean.Algebra
