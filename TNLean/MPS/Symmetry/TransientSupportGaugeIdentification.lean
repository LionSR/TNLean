/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.AsymptoticDecomposition
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.Core.TPGauge
import QICLean.Channel.Irreducible.KrausGauge

/-!
# Identification after removal of a transient periodic component

A periodic tensor with a norm-vanishing remainder can be compared asymptotically
with its retained component. A limiting overlap of modulus one identifies the
bond dimensions and gives gauge equivalence up to a scalar between irreducible
retained tensors. Faithful adjoint stationary densities provide trace-preserving
normalizations by pure bond gauges, so all periodic coefficients are unchanged.

These are finite-dimensional auxiliary statements for arXiv:1010.3732,
Appendix C, lines 2653–2717, using arXiv:1606.00608, Lemma equalMPS. They do not
assert exact equality of the full and retained finite-ring rays, or deduce
transfer contraction from a physical Hamiltonian gap.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder Topology
open Filter

namespace MPSTensor

private theorem exists_gaugePhase_of_unit_overlap_of_faithful_adjoint_fixedPoints
    {d D E : ℕ} [NeZero D] [NeZero E]
    (A : MPSTensor d D) (C : MPSTensor d E)
    (hA : Kraus.IsIrreducibleFamily A) (hC : Kraus.IsIrreducibleFamily C)
    (σ : Matrix (Fin D) (Fin D) ℂ) (τ : Matrix (Fin E) (Fin E) ℂ)
    (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hσfix : Kraus.adjointMap A σ = σ) (hτfix : Kraus.adjointMap C τ = τ)
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A C N‖) atTop (𝓝 (1 : ℝ))) :
    ∃ h : D = E, GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) A) C := by
  let A' := Kraus.tpGauge A σ
  let C' := Kraus.tpGauge C τ
  have hATP : ∑ i, (A' i)ᴴ * A' i = 1 :=
    Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint A σ hσ (by
      simpa only [Kraus.mapLM_apply, Kraus.map_apply, Kraus.adjointMap_apply,
        Matrix.conjTranspose_conjTranspose] using hσfix)
  have hCTP : ∑ i, (C' i)ᴴ * C' i = 1 :=
    Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint C τ hτ (by
      simpa only [Kraus.mapLM_apply, Kraus.map_apply, Kraus.adjointMap_apply,
        Matrix.conjTranspose_conjTranspose] using hτfix)
  have hAIrr : Kraus.IsIrreducibleFamily A' :=
    (Kraus.isIrreducibleFamily_tpGauge_iff A σ hσ).mpr hA
  have hCIrr : Kraus.IsIrreducibleFamily C' :=
    (Kraus.isIrreducibleFamily_tpGauge_iff C τ hτ).mpr hC
  have hGaugeA := gaugeEquiv_tpGauge A σ hσ
  have hGaugeC := gaugeEquiv_tpGauge C τ hτ
  have hSame : ∀ N, mpvOverlap A' C' N = mpvOverlap A C N := by
    intro N
    unfold mpvOverlap
    apply Finset.sum_congr rfl
    intro x _
    rw [← hGaugeA.sameMPV N x, ← hGaugeC.sameMPV N x]
  have hOverlap' : Tendsto (fun N => ‖mpvOverlap A' C' N‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hSame] using hOverlap
  have hdim := dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP
    A' C' hAIrr hCIrr hATP hCTP hOverlap'
  subst E
  have hCore := gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
    A' C' hAIrr hCIrr hATP hCTP hOverlap'
  exact ⟨rfl, gaugePhaseEquiv_trans_same_dim hGaugeA.toGaugePhaseEquiv
    (gaugePhaseEquiv_trans_same_dim hCore hGaugeC.symm.toGaugePhaseEquiv)⟩

/-- A norm-vanishing periodic remainder can be removed before the rectangular
fundamental theorem identifies the actual retained tensors and bond dimensions.
Faithful adjoint stationary matrices give pure trace-preserving gauges. This
conditional auxiliary statement is used in arXiv:1010.3732, Appendix C,
lines 2653–2717; gauge recovery is arXiv:1606.00608, Lemma equalMPS. -/
theorem exists_dim_eq_gaugePhase_of_vanishing_periodic_remainder
    {d D E k l : ℕ} [NeZero D] [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor d k)
    (C : MPSTensor d E) (R : MPSTensor d l)
    (hA : Kraus.IsIrreducibleFamily A) (hC : Kraus.IsIrreducibleFamily C)
    (σ : Matrix (Fin D) (Fin D) ℂ) (τ : Matrix (Fin E) (Fin E) ℂ)
    (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hσfix : Kraus.adjointMap A σ = σ) (hτfix : Kraus.adjointMap C τ = τ)
    (M : ℝ) (hBound : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ M)
    (hdecomp : ∀ᶠ N in atTop, ∀ x : Fin N → Fin d,
      mpv B x = mpv C x + mpv R x)
    (hR : Tendsto (fun N => ‖mpvState R N‖) atTop (𝓝 (0 : ℝ)))
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A B N‖) atTop (𝓝 (1 : ℝ))) :
    ∃ h : D = E, GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) A) C := by
  have hRetained := mpvOverlap_norm_tendsto_one_of_eventual_decomposition
    A B C R M hBound hdecomp hR hOverlap
  exact exists_gaugePhase_of_unit_overlap_of_faithful_adjoint_fixedPoints
    A C hA hC σ τ hσ hτ hσfix hτfix hRetained

end MPSTensor
