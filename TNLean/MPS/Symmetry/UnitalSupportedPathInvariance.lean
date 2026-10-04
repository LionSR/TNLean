/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StationarySupportedDensityPhaseInvariance
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UnitInterval

/-!
# Virtual cohomology along a supplied unital stationary-support family

The local cohomology result for normalized stationary support data extends to
the unit interval when the ambient adjoint fixed space is one-dimensional and
each support compression is injective. The stationary density may change rank.

These are conditional auxiliary results for SPC11, Appendix C, lines 2653–2717.
Construction of the supplied ambient data from a gapped physical path remains
open; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix ComplexOrder Topology

namespace TNLean.Algebra

/-- On a preconnected parameter space, locally constant scalar cohomology
classes are constant. Applied to the unit interval, this is the local-to-global
step in SPC11, Appendix C. -/
theorem ScalarCocycle.cohomologousTo_of_eventually_at_all_points
    {G : Type} [Group G] {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (ω : T → ScalarCocycle G)
    (hω : ∀ t₀, ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀))
    (t₁ t₀ : T) : (ω t₁).CohomologousTo (ω t₀) := by
  let f : T → Quotient (scalarCocycleSetoid (G := G)) := fun t ↦ Quotient.mk' (ω t)
  have hf : IsLocallyConstant f :=
    (IsLocallyConstant.iff_eventually_eq f).mpr
      (fun t₀ ↦ (hω t₀).mono (fun t ht ↦ Quotient.sound ht))
  exact Quotient.exact (hf.apply_eq_of_preconnectedSpace t₁ t₀)

end TNLean.Algebra

open TNLean.Algebra

namespace MPSTensor

/-- The endpoint virtual factor systems are cohomologous for a continuous unital
supported family whose ambient adjoint fixed space is one-dimensional and whose
support compression is injective at every parameter.

This completes the local-to-global step in SPC11, Appendix C, for the explicitly
supplied unital stationary-support data. -/
theorem cohomologousTo_of_continuous_unital_supported_family
    {G : Type} [Group G] {d k : ℕ}
    (D : unitInterval → ℕ) (ω : unitInterval → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (B : unitInterval → MPSTensor d k) (hB : Continuous B)
    (hUnital : ∀ t, Kraus.IsUnital (B t))
    (σ : unitInterval → Matrix (Fin k) (Fin k) ℂ)
    (hσ : ∀ t, (σ t).PosSemidef) (htrace : ∀ t, (σ t).trace = 1)
    (hfix : ∀ t, Kraus.adjointMap (B t) (σ t) = σ t)
    (K : ∀ t, Matrix (Fin k) (Fin (D t)) ℂ)
    (hK : ∀ t, (K t).IsIsometry)
    (hsupport : ∀ t, K t * (K t)ᴴ = (hσ t).supportProj)
    (A : ∀ t, MPSTensor d (D t))
    (hA : ∀ t i, A t i = (K t)ᴴ * B t i * K t)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (hdim : ∀ t, Module.finrank ℂ
      (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM (B t))) = 1)
    (hInj : ∀ t, Kraus.IsInjective (A t)) :
    (ω 1).CohomologousTo (ω 0) := by
  exact ScalarCocycle.cohomologousTo_of_eventually_at_all_points ω
    (fun t₀ ↦ eventually_cohomologousTo_of_continuous_unital_supported_family
      D ω ρ B hB hUnital σ hσ htrace hfix K hK hsupport A hA hUnitary U hCov
        t₀ (hdim t₀) (hInj t₀)) 1 0

end MPSTensor
