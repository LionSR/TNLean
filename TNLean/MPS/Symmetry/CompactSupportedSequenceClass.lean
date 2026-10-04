/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StationarySupportedDensityPhaseInvariance
import TNLean.MPS.Symmetry.StationarySupportLimitIdentification
import TNLean.MPS.Symmetry.CompactSupportVirtualTransport
import TNLean.MPS.Symmetry.UnitaryVirtualGauge
import TNLean.MPS.Overlap.PeriodicRayUnitOverlap
import Mathlib.Topology.Compactification.OnePoint.Basic
import QICLean.Analysis.MatrixSqrt

/-!
# Virtual class stability along a convergent unital sequence

The one-point compactification of the natural numbers turns a convergent
sequence of ambient tensors into a continuous family. At the finite points,
the stationary support may be the entire bond space; at infinity it may have
smaller dimension. The supported-family theorem requires no convergence of
virtual representatives or support frames.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. The transfer
spectral bound remains an explicit hypothesis in the eventual application.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder Topology OnePoint
open Filter TNLean.Algebra

namespace MPSTensor

private theorem eventually_class_of_unital_sequence_supported_limit
    {G : Type} [Group G] {d k E : ℕ}
    (B : ℕ → MPSTensor d k) (b : MPSTensor d k)
    (hB : Tendsto B atTop (𝓝 b)) (hUnital : ∀ n, Kraus.IsUnital (B n))
    (hbUnital : Kraus.IsUnital b)
    (σ : ℕ → Matrix (Fin k) (Fin k) ℂ) (hσ : ∀ n, (σ n).PosDef)
    (hTrace : ∀ n, (σ n).trace = 1)
    (hFix : ∀ n, Kraus.adjointMap (B n) (σ n) = σ n)
    (τ : Matrix (Fin k) (Fin k) ℂ) (hτ : τ.PosSemidef)
    (hτTrace : τ.trace = 1) (hτFix : Kraus.adjointMap b τ = τ)
    (K : Matrix (Fin k) (Fin E) ℂ) (hK : K.IsIsometry)
    (hSupport : K * Kᴴ = hτ.supportProj)
    (C : MPSTensor d E) (hC : ∀ i, C i = Kᴴ * b i * K)
    (hCInj : Kraus.IsInjective C)
    (hDim : Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM b)) = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : ℕ → ScalarCocycle G) (ω₀ : ScalarCocycle G)
    (ρ : ∀ n, ProjectiveRepresentation (D := k) (ω n))
    (ρ₀ : ProjectiveRepresentation (D := E) ω₀)
    (hρ : ∀ n g, ((ρ n).X g : Matrix (Fin k) (Fin k) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin E) (Fin E) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ n g, rotatePhysical (U g) (B n) = fun i =>
      ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ) * B n i *
        ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ)ᴴ)
    (hCov₀ : ∀ g, rotatePhysical (U g) C = fun i =>
      (ρ₀.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ) * C i *
        (ρ₀.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ)ᴴ) :
    ∀ᶠ n in atTop, (ω n).CohomologousTo ω₀ := by
  let ambient := OnePoint.continuousMapMkNat B b hB
  let dim : OnePoint ℕ → ℕ := OnePoint.rec E (fun _ => k)
  let factor : OnePoint ℕ → ScalarCocycle G := OnePoint.rec ω₀ ω
  let action : ∀ t, ProjectiveRepresentation (D := dim t) (factor t) :=
    OnePoint.rec ρ₀ ρ
  let density : OnePoint ℕ → Matrix (Fin k) (Fin k) ℂ := OnePoint.rec τ σ
  let frame : ∀ t : OnePoint ℕ, Matrix (Fin k) (Fin (dim t)) ℂ :=
    OnePoint.rec K (fun _ => (1 : Matrix (Fin k) (Fin k) ℂ))
  let tensor : ∀ t, MPSTensor d (dim t) := OnePoint.rec C B
  have hClass := eventually_cohomologousTo_of_continuousAt_unital_supported_family
    dim factor action ambient ∞ ambient.continuous.continuousAt
    (OnePoint.rec hbUnital hUnital) density
    (OnePoint.rec hτ (fun n => (hσ n).posSemidef))
    (OnePoint.rec hτTrace hTrace) (OnePoint.rec hτFix hFix) frame
    (OnePoint.rec hK (fun _ => by
      change (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ *
        (1 : Matrix (Fin k) (Fin k) ℂ) = (1 : Matrix (Fin k) (Fin k) ℂ)
      simp only [Matrix.conjTranspose_one, Matrix.one_mul]))
    (OnePoint.rec hSupport (fun n => by
      change (1 : Matrix (Fin k) (Fin k) ℂ) *
        (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ = (hσ n).posSemidef.supportProj
      rw [Matrix.conjTranspose_one, Matrix.one_mul, (hσ n).supportProj_eq_one]))
    tensor (OnePoint.rec hC (fun n i => by
      change B n i = (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ * B n i *
        (1 : Matrix (Fin k) (Fin k) ℂ)
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]))
    (OnePoint.rec hρ₀ hρ) U (OnePoint.rec hCov₀ hCov) hDim hCInj
  have hTendsto : Tendsto ((↑) : ℕ → OnePoint ℕ) atTop (𝓝 ∞) := by
    simpa only [coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
      Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
  exact hTendsto.eventually hClass

/-- A convergent sequence of unital tensors eventually has the base virtual class
when its limiting periodic lines agree eventually with those of a unital
injective reference. The limiting transfer spectral bound is supplied. The
normality and the limiting virtual action are derived inside the argument;
no continuity of virtual representatives is assumed. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_cohomologousTo_of_tendsto_unital_periodic_lines
    {G : Type} [Group G] {d D k E : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hAU : Kraus.IsUnital A)
    (B : ℕ → MPSTensor d k) (b : MPSTensor d k)
    (hB : Tendsto B atTop (𝓝 b)) (hBU : ∀ n, Kraus.IsUnital (B n))
    (hbU : Kraus.IsUnital b)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap b) 1) = 1)
    (σ : ℕ → Matrix (Fin k) (Fin k) ℂ) (hσ : ∀ n, (σ n).PosDef)
    (hσTrace : ∀ n, (σ n).trace = 1)
    (hσFix : ∀ n, Kraus.adjointMap (B n) (σ n) = σ n)
    (τ : Matrix (Fin k) (Fin k) ℂ) (hτ : τ.PosSemidef)
    (hτTrace : τ.trace = 1) (hτFix : Kraus.adjointMap b τ = τ)
    (K : Matrix (Fin k) (Fin E) ℂ) (hK : K.IsIsometry)
    (hSupport : K * Kᴴ = hτ.supportProj)
    (C : MPSTensor d E) (hC : ∀ i, C i = Kᴴ * b i * K)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hSpecA : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q)
    (hSpecb : ∀ z ∈ spectrum ℂ (Kraus.transferMap b), z ≠ 1 → ‖z‖ ≤ q)
    (hSpan : ∀ᶠ N in atTop,
      Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} =
        Submodule.span ℂ {(mpv b : (Fin N → Fin d) → ℂ)})
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : ℕ → ScalarCocycle G) (ω₀ : ScalarCocycle G)
    (ρ : ∀ n, ProjectiveRepresentation (D := k) (ω n))
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (hρ : ∀ n g, ((ρ n).X g : Matrix (Fin k) (Fin k) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ n g, rotatePhysical (U g) (B n) = fun i =>
      ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ) * B n i *
        ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ)ᴴ)
    (hCov₀ : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∀ᶠ n in atTop, (ω n).CohomologousTo ω₀ := by
  have hk : k ≠ 0 := by
    intro hzero
    subst k
    simp only [Matrix.trace_fin_zero, zero_ne_one] at hτTrace
  let : NeZero k := ⟨hk⟩
  have hAirr := Kraus.injective_implies_irreducibleCP A hA
  have hAdim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1 :=
    finrank_eigenspace_eq_one_of_irreducible_positive
      (Kraus.mapLM A) (Kraus.isPositiveMap_mapLM A) hAirr (r := 1) zero_le_one
      Matrix.PosDef.one (by simpa only [Kraus.mapLM_apply, Complex.ofReal_one, one_smul]
        using Kraus.map_one_of_isUnital A hAU)
  have hAnorm := norm_mpvState_tendsto_one_of_transfer_spectrum
    A hAU hAdim q hq hqOne hSpecA
  have hbnorm := norm_mpvState_tendsto_one_of_transfer_spectrum
    b hbU hDim q hq hqOne hSpecb
  have hBound : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ (2 : ℝ) :=
    ((tendsto_order.mp hAnorm).2 2 (by norm_num)).mono fun _ h => h.le
  have hOverlap := norm_mpvOverlap_tendsto_one_of_eventual_span_eq A b hSpan hAnorm hbnorm
  obtain ⟨Λ, hΛ, hΛfix⟩ := exists_posDef_adjoint_fixedPoint_of_isInjective_unital
    hA (Kraus.map_one_of_isUnital A hAU)
  have hΛfix' : Kraus.adjointMap A Λ = Λ := by
    simpa only [Kraus.transferMap, Kraus.mapLM_apply, Kraus.map_apply,
      Matrix.conjTranspose_conjTranspose, Kraus.adjointMap_apply] using hΛfix
  obtain ⟨_, hEq, hGauge⟩ := exists_dim_eq_gaugePhase_of_unital_stationary_support_overlap
    A b C (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hAirr)
    Λ hΛ hΛfix' hbU hDim τ hτ hτFix hτTrace K hK hSupport hC
    q hq hqOne hSpecb 2 hBound hOverlap
  subst E
  have hGauge' : GaugePhaseEquiv A C := by simpa using hGauge
  have hUniq := normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one
    b hDim τ hτFix hτTrace
  have hCU := (prepare_stationary_support_compression
    b C K hK hC hbU τ hτ hSupport hτFix hτTrace hUniq).1
  obtain ⟨ρLimit, hρLimit, hCovLimit⟩ := exists_unitary_virtualRep_of_unital_gaugePhaseEquiv
    hA hAU hCU hGauge' U ρ₀ hρ₀ hCov₀
  obtain ⟨X, c, hc, hX⟩ := hGauge'
  have hCInj : Kraus.IsInjective C := isInjective_of_gaugeEquiv (hA.smul hc)
    ⟨X, fun i => by simpa only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul] using hX i⟩
  exact eventually_class_of_unital_sequence_supported_limit
    B b hB hBU hbU σ hσ hσTrace hσFix τ hτ hτTrace hτFix K hK hSupport C hC hCInj
    ((finrank_adjointFixedSpace_eq_transferFixedSpace b).trans hDim)
    U ω ω₀ ρ ρLimit hρ hρLimit hCov hCovLimit

end MPSTensor
