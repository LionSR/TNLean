/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOAction

/-!
# Mixed endpoint action regressions

The signatures retain arbitrary multiplicity, arbitrary real parameter,
and the actual mixed endpoint tensor. Endpoint specializations require
neither nonzero weights nor injectivity. The unmatched acted-bond sector
also gives an explicit obstruction to ambient completeness.
-/

-- These regressions intentionally inspect kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPSTensor MPSTensor.MPOSymmetry

namespace MixedEndpointMPOActionTest

variable {D₀ D₁ χ₀ χ₁ m : ℕ}
  (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
  (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
    (fun _ : Fin m => A₀) V₀ W₀)
  (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
    (fun _ : Fin m => A₁) V₁ W₁)

example (γ : ℝ) :
    IsBiorthogonalDecomposition
      (MPOTensor.actTensor (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
        (mixedEndpointInterpolation A₀ A₁ γ))
      (fun _ : Fin m => mixedEndpointInterpolation A₀ A₁ γ)
      (fun μ => mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ))
      (fun μ => mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ)) :=
  isBiorthogonalDecomposition_mixedEndpointInterpolation
    T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ γ

example : MPOTensor.IsBoundaryCompatible (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
    (mixedEndpointInterpolation A₀ A₁ 0) :=
  isBoundaryCompatible_mixedEndpointInterpolation T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ 0

example : MPOTensor.IsBoundaryCompatible (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁)
    (mixedEndpointInterpolation A₀ A₁ 1) :=
  isBoundaryCompatible_mixedEndpointInterpolation T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ 1

example (γ : ℝ) {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁) L *ᵥ
        (fun σ : Fin L → Fin ((D₀ + D₁) * (D₀ + D₁)) =>
          mpv (mixedEndpointInterpolation A₀ A₁ γ) σ) =
      (m : ℂ) • (fun σ => mpv (mixedEndpointInterpolation A₀ A₁ γ) σ) :=
  mpo_mulVec_mixedEndpointInterpolation T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁ h₀ h₁ γ hL

/-- The unused acted-bond corner is zero even if the endpoint maps are not
assumed biorthogonal. This prevents an accidental completeness premise. -/
private theorem unmatched_synthesis (μ : Fin m) (α : Fin χ₀) (k : Fin D₁)
    (r : Fin (D₀ + D₁)) :
    mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ)
      (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁ (.inl α, .inr k)) r = 0 := by
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective r
  cases r <;> simp [mixedEndpointMPOSynthesis, mixedEndpointSynthesis]

example (α : Fin χ₀) (k : Fin D₁) :
    (∑ μ, mixedEndpointMPOSynthesis (W₀ μ) (W₁ μ) *
      mixedEndpointMPOAnalysis (V₀ μ) (V₁ μ)) ≠
        (1 : Matrix (Fin ((χ₀ + χ₁) * (D₀ + D₁)))
          (Fin ((χ₀ + χ₁) * (D₀ + D₁))) ℂ) := by
  classical
  intro h
  have he := congrArg (fun M => M
    (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁ (.inl α, .inr k))
    (mixedEndpointActedEquiv χ₀ χ₁ D₀ D₁ (.inl α, .inr k))) h
  simp [Matrix.sum_apply, Matrix.mul_apply, unmatched_synthesis] at he

/--
info: 'MPSTensor.MPOSymmetry.isBiorthogonalDecomposition_mixedEndpointInterpolation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isBiorthogonalDecomposition_mixedEndpointInterpolation

/--
info: 'MPSTensor.MPOSymmetry.isBoundaryCompatible_mixedEndpointInterpolation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isBoundaryCompatible_mixedEndpointInterpolation

/--
info: 'MPSTensor.MPOSymmetry.mpo_mulVec_mixedEndpointInterpolation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mpo_mulVec_mixedEndpointInterpolation

end MixedEndpointMPOActionTest
