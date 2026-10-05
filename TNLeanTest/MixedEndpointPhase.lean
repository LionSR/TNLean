/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.RingEndpointRightComparison
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenKernel

/-! Source-scope regressions for actual mixed endpoints and extended supports.
There is no supplied endpoint gap, projector limit, open kernel identity,
fixed-point tensor form, or whole-path thermodynamic gap. -/

-- These reports audit the kernel dependencies of the endpoint capstones.
set_option linter.hashCommand false

open MPSTensor MPSTensor.MPOSymmetry
open scoped ComplexOrder

variable {D₀ D₁ N : ℕ}
variable (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)

example (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    Kraus.IsInjective (mixedEndpointInterpolation A₀ A₁ γ) :=
  isInjective_mixedEndpointInterpolation A₀ A₁ h₀ h₁ hγ

example (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) :
    Continuous (mixedEndpointParentInteraction A₀ A₁) :=
  continuous_mixedEndpointParentInteraction A₀ A₁ h₀ h₁ hD₀ hD₁

example (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N ≤
        parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N ∧
      parentHamiltonianES (mixedEndpointLeftTensor A₀ D₁) 2 N ≤
        (3 : ℂ) • periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap N :=
  mixedEndpoint_periodic_comparison A₀ A₁ hN

example (hN : 2 ≤ N) :
    periodicInteractionHamiltonianES (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N ≤
        parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N ∧
      parentHamiltonianES (mixedEndpointRightTensor A₁ D₀) 2 N ≤
        (3 : ℂ) • periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ 1).toLinearMap N :=
  mixedEndpoint_periodic_one_comparison A₀ A₁ hN

example [NeZero D₀] [NeZero D₁]
    (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ, p = 0 ∨ p = 1 → ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (mixedEndpointParentInteraction A₀ A₁ p).toLinearMap N v‖ :=
  exists_uniform_mixedEndpoint_periodic_endpoints_gap A₀ A₁ h₀ h₁

example (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N) =
      (insertedBoundaryMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ γ) N).range :=
  mixedEndpoint_open_ker_eq A₀ A₁ h₀ h₁ hD₀ hD₁ γ hN

example (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (γ : ℝ) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)) =
        (D₀ + D₁) * (D₀ + D₁) :=
  mixedEndpoint_open_ker_finrank A₀ A₁ h₀ h₁ hD₀ hD₁ γ hN

example (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)
    (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hN : 2 ≤ N) :
    Continuous fun γ : ℝ => (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ γ).toLinearMap N)).starProjection :=
  continuous_mixedEndpoint_open_ker_starProjection A₀ A₁ h₀ h₁ hD₀ hD₁ hN

/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_periodic_endpoints_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_periodic_endpoints_gap
/--
info: 'MPSTensor.MPOSymmetry.mixedEndpoint_open_ker_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mixedEndpoint_open_ker_eq
/--
info: 'MPSTensor.MPOSymmetry.continuous_mixedEndpoint_open_ker_starProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.continuous_mixedEndpoint_open_ker_starProjection
