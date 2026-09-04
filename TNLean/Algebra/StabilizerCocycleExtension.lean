/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StabilizerCocycleLSymbol
import TNLean.Algebra.LSymbolBlockIndependence

/-!
# Explicit extension-to-gauge identity

The forward scalar calculation in arXiv:2502.20257, Proposition `prop:BI_psi`
(lines 7042–7064), for a genuine cocycle representative extending the chosen
stabilizer representative. The displayed action gauge is retained verbatim.

**Scope restriction (scalar representatives):** This proves neither the tensor
statement nor the equivalence on cohomology classes; see
`docs/paper-gaps/fbc25_stabilizer_extension_representatives.tex`.
The corrected transition index is explained in
`docs/paper-gaps/fbc25_stabilizer_transition_index_typo.tex`.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X}

private theorem cocycle_transition_identity {Ψ : ScalarCocycle G} (hΨ : Ψ.IsCocycle)
    (a b c u v : G) :
    Ψ (a⁻¹ * u * b) (b⁻¹ * v * c) =
      Ψ u v * (Ψ a⁻¹ ((u * v) * c) * Ψ (u * v) c / (Ψ 1 1 * Ψ c c⁻¹)) /
        ((Ψ a⁻¹ (u * b) * Ψ u b / (Ψ 1 1 * Ψ b b⁻¹)) *
          (Ψ b⁻¹ (v * c) * Ψ v c / (Ψ 1 1 * Ψ c c⁻¹))) := by
  have hr (g : G) : Ψ g 1 = Ψ 1 1 := by
    have h := hΨ g 1 1
    simpa only [mul_one, mul_left_cancel_iff] using h
  have hl (g : G) : Ψ 1 g = Ψ 1 1 := by
    have h := hΨ 1 1 g
    simpa only [one_mul, mul_right_cancel_iff] using h.symm
  have hi : Ψ b⁻¹ b = Ψ b b⁻¹ := by
    have h := hΨ b b⁻¹ b
    simpa only [mul_inv_cancel, inv_mul_cancel, hr, hl, mul_comm, mul_right_cancel_iff] using h.symm
  have h₁ : Ψ (a⁻¹ * u * b) (b⁻¹ * v * c) =
      Ψ (a⁻¹ * u * b) b⁻¹ * Ψ (a⁻¹ * u) (v * c) / Ψ b⁻¹ (v * c) := by
    apply (eq_div_iff_mul_eq').2
    simpa [mul_assoc] using (hΨ (a⁻¹ * u * b) b⁻¹ (v * c)).symm
  have h₂ : Ψ (a⁻¹ * u * b) b⁻¹ =
      Ψ 1 1 * Ψ b b⁻¹ / Ψ (a⁻¹ * u) b := by
    apply (eq_div_iff_mul_eq').2
    simpa [mul_assoc, hr, hi] using hΨ (a⁻¹ * u * b) b⁻¹ b
  have h₃ : Ψ (a⁻¹ * u) (v * c) =
      Ψ a⁻¹ (u * (v * c)) * Ψ u (v * c) / Ψ a⁻¹ u := by
    exact eq_div_of_mul_eq'' (hΨ a⁻¹ u (v * c))
  have h₄ : Ψ (a⁻¹ * u) b = Ψ a⁻¹ (u * b) * Ψ u b / Ψ a⁻¹ u := by
    exact eq_div_of_mul_eq'' (hΨ a⁻¹ u b)
  have h₅ : Ψ u (v * c) = Ψ u v * Ψ (u * v) c / Ψ v c := by
    exact (eq_div_iff_mul_eq').2 (hΨ u v c).symm
  rw [h₁, h₂, h₃, h₄, h₅]
  simp only [← mul_assoc]
  apply Units.ext
  push_cast
  field_simp

namespace StabilizerRepresentatives

/-- The exact displayed gauge in arXiv:2502.20257, `prop:BI_psi`, line 7055.
No normalization of the cocycle is assumed. -/
def extensionActionGauge (K : StabilizerRepresentatives G X x₀)
    (Ψ : ScalarCocycle G) : ActionTensorGauge G X :=
  fun g x ↦ Ψ (K.k (g • x))⁻¹ (g * K.k x) * Ψ g (K.k x) /
    (Ψ 1 1 * Ψ (K.k x) (K.k x)⁻¹)

/-- The explicit extension-to-gauge scalar identity in arXiv:2502.20257,
`prop:BI_psi`, lines 7047–7056, with the corrected transition elements. -/
theorem inducedLSymbol_eq_extensionActionGauge
    (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} {Ψ : ScalarCocycle G}
    (hΨ : Ψ.IsCocycle) (hext : ∀ a b : MulAction.stabilizer G x₀, Ψ (a : G) (b : G) = ψ a b)
    (g₁ g₂ : G) (x : X) :
    K.inducedLSymbol ψ x g₁ g₂ = Ψ g₁ g₂ * K.extensionActionGauge Ψ (g₁ * g₂) x /
      (K.extensionActionGauge Ψ g₁ (g₂ • x) * K.extensionActionGauge Ψ g₂ x) := by
  rw [inducedLSymbol, ← hext]
  simpa only [coe_transitionElement, extensionActionGauge, mul_smul] using
    cocycle_transition_identity hΨ (K.k (g₁ • (g₂ • x))) (K.k (g₂ • x))
      (K.k x) g₁ g₂

/-- Inverting the printed forward gauges trivializes the induced scalar
L-symbol, the forward implication of arXiv:2502.20257, `prop:BI_psi`
at the representative level. -/
theorem inducedLSymbol_hasTrivialGauge_of_extension
    (K : StabilizerRepresentatives G X x₀)
    {ψ : ScalarCocycle (MulAction.stabilizer G x₀)} {Ψ : ScalarCocycle G}
    (hΨ : Ψ.IsCocycle)
    (hext : ∀ a b : MulAction.stabilizer G x₀, Ψ (a : G) (b : G) = ψ a b) :
    LSymbol.HasTrivialGauge (K.inducedLSymbol ψ) := by
  refine ⟨Ψ⁻¹, (K.extensionActionGauge Ψ)⁻¹, fun x g h ↦ ?_⟩
  rw [LSymbol.gauge, K.inducedLSymbol_eq_extensionActionGauge hΨ hext]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end StabilizerRepresentatives
end TNLean.Algebra
