/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.UnitaryVirtualGauge
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Preparation.NormalGauge

/-!
# Trace-preserving gauges of unital injective tensors

The faithful adjoint fixed point of an actual unital injective tensor
supplies the existing square-root TP gauge. It preserves one-site
injectivity, every positive-length periodic ray and the actual transfer
spectrum. The resulting TP injective tensor has an actual normalized
positive-definite stationary density, derived by primitive Perron--Frobenius
theory rather than supplied as extra input.

Source: arXiv:quant-ph/0608197, Theorem Th:TIcanonical, proof lines 827–832;
arXiv:2307.01696, the canonical gauge preceding equation (5);
SPC11, arXiv:1010.3732, Section II.F, lines 929–953.
-/

noncomputable section

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-- A one-site injective TP tensor has a normalized faithful stationary
density, obtained from its actual primitive transfer map. No density or
spectral-gap hypothesis is supplied. Source: arXiv:2307.01696, the gauge
preceding equation (5); arXiv:0909.5347, Proposition 3. -/
theorem exists_posDef_fixedPoint_trace_one_of_isInjective_isTP
    {B : MPSTensor d D} (hB : Kraus.IsInjective B)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosDef ∧ Kraus.transferMap B ρ = ρ ∧ Matrix.trace ρ = 1 := by
  obtain ⟨ρ, hρ, hfix, _⟩ :=
    isNormal_implies_stronglyIrreducible B hTP hB.isNormal
  have htr : 0 < Matrix.trace ρ := hρ.trace_pos
  refine ⟨(Matrix.trace ρ)⁻¹ • ρ, hρ.smul (inv_pos.mpr htr), ?_, ?_⟩
  · rw [map_smul, hfix]
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr.ne']

/-- Unital injectivity gives an actual TP bond gauge with a derived
normalized faithful stationary density. The gauge preserves one-site
injectivity, all positive-length periodic rays and the transfer spectrum,
without rescaling the tensor or assuming any of these conclusions.
Source: arXiv:quant-ph/0608197, Theorem Th:TIcanonical, proof lines 827–832;
arXiv:2307.01696, the gauge preceding equation (5); SPC11,
arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem exists_tpGauge_of_isInjective_unital
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) (hUnital : Kraus.IsUnital A) :
    ∃ (B : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ),
      GaugeEquiv A B ∧ Kraus.IsInjective B ∧
        (∑ i, (B i)ᴴ * B i = 1) ∧
        ρ.PosDef ∧ Kraus.transferMap B ρ = ρ ∧ Matrix.trace ρ = 1 ∧
        SamePositiveMpvRay A B ∧
        spectrum ℂ (Kraus.transferMap A) = spectrum ℂ (Kraus.transferMap B) := by
  have hNorm : Kraus.transferMap A 1 = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using
      (show ∑ i, A i * (A i)ᴴ = 1 from hUnital)
  obtain ⟨Λ, hΛ, hΛfix⟩ := exists_posDef_adjoint_fixedPoint_of_isInjective_unital hA hNorm
  let B := Kraus.tpGauge A Λ
  have hTP : ∑ i, (B i)ᴴ * B i = 1 :=
    Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint A Λ hΛ hΛfix
  have hGauge : GaugeEquiv A B := gaugeEquiv_tpGauge A Λ hΛ
  have hB : Kraus.IsInjective B := isInjective_of_gaugeEquiv hA hGauge
  obtain ⟨ρ, hρ, hfix, htr⟩ :=
    exists_posDef_fixedPoint_trace_one_of_isInjective_isTP hB hTP
  refine ⟨B, ρ, hGauge, hB, hTP, hρ, hfix, htr, ?_, ?_⟩
  · intro N _hN
    have hmpv : (mpv A : Cfg d N → ℂ) = mpv B :=
      funext fun σ ↦ hGauge.sameMPV N σ
    rw [hmpv]
  · ext μ
    simpa only [Module.End.hasEigenvalue_iff_mem_spectrum] using
      hasEigenvalue_transferMap_iff_of_gaugeEquiv hGauge μ

end MPSTensor
