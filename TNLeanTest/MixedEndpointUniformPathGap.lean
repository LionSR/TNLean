import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointUniformPathGap

/-! Scope regressions for the actual closed mixed path. These introduce no
finite-window, endpoint-gap, or kernel-continuity hypotheses. -/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open MPSTensor MPSTensor.MPOSymmetry

variable {D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]

example (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : unitInterval, ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N v‖ :=
  exists_uniform_mixedEndpoint_periodic_path_gap A₀ A₁ h₀ h₁

example (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)) = 1 :=
  mixedEndpoint_periodic_groundSpace_finrank_closedInterval A₀ A₁ h₀ h₁ γ hN

/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_periodic_path_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_periodic_path_gap
/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_open_endpoints_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_open_endpoints_gap
/--
info: 'MPSTensor.MPOSymmetry.continuous_mixedEndpoint_periodic_ker_starProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.continuous_mixedEndpoint_periodic_ker_starProjection
