/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.AdjointFixedSpaceDimension
import TNLean.MPS.Symmetry.StationarySupportPreparation
import TNLean.MPS.Symmetry.SupportPeriodicDecomposition
import TNLean.MPS.Symmetry.TransientSupportGaugeIdentification
import TNLean.MPS.Symmetry.TransientCornerSpectrum

/-!
# Identification of a stationary support from a limiting overlap

For a unital tensor with a one-dimensional transfer fixed space and a supplied
strict bound on the remaining spectrum, compression to the entire support of
an adjoint stationary density gives a normal tensor. The complementary periodic
component tends to zero. A unit limiting overlap with an irreducible reference
tensor then identifies the supported bond dimension and its bond gauge up to a
nonzero scalar.

This is a conditional finite-dimensional auxiliary for arXiv:1010.3732,
Appendix C, lines 2653–2717. The transfer spectral bound and limiting overlap
are explicit hypotheses. No physical-gap implication or exact equality of
ambient and supported finite-ring rays is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder Topology
open Filter

namespace MPSTensor

private theorem normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one
    {d k : ℕ} (B : MPSTensor d k)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap B) 1) = 1)
    (σ : Matrix (Fin k) (Fin k) ℂ)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (Z : Matrix (Fin k) (Fin k) ℂ)
    (hZfix : Kraus.adjointMap B Z = Z) (hZtrace : Z.trace = 1) : Z = σ := by
  have hσne : σ ≠ 0 := by
    intro hzero
    simp only [hzero, Matrix.trace_zero, zero_ne_one] at htrace
  have hσker : σ ∈ (LinearMap.id - Kraus.adjointMapLM B).ker := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      Kraus.adjointMapLM_apply, hfix, sub_self]
  have hZker : Z ∈ (LinearMap.id - Kraus.adjointMapLM B).ker := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      Kraus.adjointMapLM_apply, hZfix, sub_self]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    ((finrank_adjointFixedSpace_eq_transferFixedSpace B).trans hDim) hσker hσne
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hZker)
  have hcOne : c = 1 := by
    simpa only [← hc, Matrix.trace_smul, htrace, smul_eq_mul, mul_one] using hZtrace
  simpa only [hcOne, one_smul] using hc.symm

/-- A full stationary support compression of a unital tensor with simple
fixed space and strictly contracting remaining spectrum is normal. A unit
limiting overlap identifies this compression with an irreducible reference
up to a scalar and a bond gauge, including equality of their bond dimensions.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717, using
arXiv:1606.00608, Lemma equalMPS. The spectral bound and overlap limit are
supplied hypotheses; no physical-gap implication is asserted. -/
theorem exists_dim_eq_gaugePhase_of_unital_stationary_support_overlap
    {d D E k : ℕ} [NeZero D]
    (A : MPSTensor d D) (B : MPSTensor d k) (C : MPSTensor d E)
    (hA : Kraus.IsIrreducibleFamily A)
    (τ : Matrix (Fin D) (Fin D) ℂ) (hτ : τ.PosDef)
    (hτfix : Kraus.adjointMap A τ = τ)
    (hB : Kraus.IsUnital B)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap B) 1) = 1)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (K : Matrix (Fin k) (Fin E) ℂ) (hK : K.IsIsometry)
    (hsupport : K * Kᴴ = hσ.supportProj) (hC : ∀ i, C i = Kᴴ * B i * K)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap B), z ≠ 1 → ‖z‖ ≤ q)
    (M : ℝ) (hBound : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ M)
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A B N‖) atTop (𝓝 (1 : ℝ))) :
    IsNormalTensor C ∧
      ∃ h : D = E, GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) A) C := by
  have hk : k ≠ 0 := by
    intro hzero
    subst k
    simp only [Matrix.trace_fin_zero, zero_ne_one] at htrace
  let : NeZero k := ⟨hk⟩
  let : NeZero E := ⟨Nat.ne_of_gt
    (Matrix.supportFrame_dimension_pos_of_trace_one K σ hσ hsupport htrace)⟩
  have huniq := normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one
    B hDim σ hfix htrace
  obtain ⟨_, hCIrr, hρPD, _, hρfix⟩ := prepare_stationary_support_compression
    B C K hK hC hB σ hσ hsupport hfix htrace huniq
  have hNormal := isNormalTensor_of_unital_stationary_support_compression
    B C K hK hC hB σ hσ hsupport hfix htrace huniq q hqOne hspec
  have hfix' : Kraus.map (fun i => (B i)ᴴ) σ = σ := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using hfix
  have hInv := Kraus.lowerZero_of_posSemidef_fixedPoint
    (fun i => (B i)ᴴ) σ hσ hfix'
  have hP : IsOrthogonalProjection (K * Kᴴ) := by
    simpa only [Kraus.stationaryProj, ← hsupport] using hInv.1
  have hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0 := fun i => by
    simpa only [Kraus.stationaryProj, ← hsupport, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.mul_assoc]
      using congrArg Matrix.conjTranspose (hInv.2 i)
  have hσne : σ ≠ 0 := by
    intro hzero
    simp only [hzero, Matrix.trace_zero, zero_ne_one] at htrace
  have hPne : K * Kᴴ ≠ 0 := by
    rw [hsupport]
    exact hσ.supportProj_ne_zero_of_ne_zero hσne
  have hR := norm_mpvState_transientCorner_tendsto_zero_of_transfer_spectrum
    B hB hDim (K * Kᴴ) hP hPne hUpper q hq hqOne hspec
  have hdecomp : ∀ᶠ N in atTop, ∀ x : Fin N → Fin d,
      mpv B x = mpv C x + mpv (fun i => (1 - K * Kᴴ) * B i * (1 - K * Kᴴ)) x := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact mpv_eq_compression_add_transient_of_upperZero B C K hK hC hUpper hN
  refine ⟨hNormal, ?_⟩
  exact exists_dim_eq_gaugePhase_of_vanishing_periodic_remainder
    A B C (fun i => (1 - K * Kᴴ) * B i * (1 - K * Kᴴ)) hA
    (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM C hCIrr)
    τ (Kᴴ * σ * K) hτ hρPD hτfix hρfix M hBound hdecomp hR hOverlap

end MPSTensor
