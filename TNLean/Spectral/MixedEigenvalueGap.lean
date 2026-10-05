/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CanonicalNormalization
import TNLean.Spectral.TransferOperatorGapNT
import TNLean.Wielandt.Primitivity.EasyDirections
import TNLean.Wielandt.Primitivity.ImpliesStronglyIrreducible

/-!
# Strict mixed eigenvalue bounds for inequivalent normal blocks

The mixed-transfer spectral gap of inequivalent normal left-canonical blocks bounds every
mixed eigenvalue strictly below one. The bond dimensions may differ; gauge-phase
inequivalence is required only when the dimensions agree.

## References

* arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii), mixed transfer rate.
* arXiv:2011.12127, normal-block mixed-transfer characterization.
-/

open Matrix
open scoped BigOperators TNOperatorSpace

namespace MPSTensor

/-- A strict mixed-transfer spectral radius bounds every mixed eigenvalue. -/
theorem mixedMap_eigenvalue_norm_lt_one_of_spectralRadius_lt_one
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hgap : Kraus.mixedMapSpectralRadius A B < 1) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Kraus.mixedMapLM A B) μ) : ‖μ‖ < 1 := by
  let V := Matrix (Fin D₁) (Fin D₂) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  have hmem : μ ∈ spectrum ℂ (Φ (Kraus.mixedMapLM A B)) := by
    rw [AlgEquiv.spectrum_eq]
    exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
  have hle : (‖μ‖₊ : ENNReal) ≤ Kraus.mixedMapSpectralRadius A B := by
    change (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (Φ (Kraus.mixedMapLM A B))
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le μ (le_iSup_of_le hmem le_rfl)
  exact_mod_cast hle.trans_lt hgap

/-- Inequivalent normal left-canonical blocks have all mixed eigenvalues of norm below one,
including rectangular mixed maps between blocks of different bond dimensions. -/
theorem mixedMap_eigenvalue_norm_lt_one_of_normal_inequivalent
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B)
    (hAleft : IsLeftCanonical A) (hBleft : IsLeftCanonical B)
    (hneq : ∀ h : D₁ = D₂, ¬ GaugePhaseEquiv (h ▸ A) B) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Kraus.mixedMapLM A B) μ) : ‖μ‖ < 1 := by
  apply mixedMap_eigenvalue_norm_lt_one_of_spectralRadius_lt_one A B _ hμ
  have hAi := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A
    (isIrreducibleTensor_of_isPrimitivePaper A (isPrimitivePaper_of_isNormal A hA))
  have hBi := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B
    (isIrreducibleTensor_of_isPrimitivePaper B (isPrimitivePaper_of_isNormal B hB))
  by_cases hD : D₁ = D₂
  · subst D₁
    exact Kraus.mixedMapSpectralRadius_lt_one_of_irreducible_TP A B hAi hBi hAleft hBleft
      (fun h => hneq rfl (gaugePhaseEquiv_of_krausGaugePhaseEquiv h))
  · exact Kraus.mixedMapSpectralRadius_lt_one_of_dim_ne_of_irreducible_TP
      A B hAi hBi hAleft hBleft hD

end MPSTensor
