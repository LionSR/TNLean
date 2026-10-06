import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointRightOpenGap

/-! Source-scope regressions for the derived actual endpoint open gaps. -/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open MPSTensor MPSTensor.MPOSymmetry

variable {D₀ D₁ : ℕ}

example (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N v‖ :=
  exists_uniform_mixedEndpoint_open_zero_gap A₀ A₁ hA₀

example (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₁ : Kraus.IsInjective A₁) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N v‖ :=
  exists_uniform_mixedEndpoint_open_one_gap A₀ A₁ hA₁

example (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁) :
    ∃ W : ℕ, 3 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ N : ℕ, W ≤ N →
        ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N))ᗮ,
          δ * ‖v‖ ≤ ‖openInteractionHamiltonianES
            (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N v‖ :=
  exists_uniform_mixedEndpoint_open_endpoints_gap A₀ A₁ hA₀ hA₁
