/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.MixedMap.Gap
import QICLean.Channel.Irreducible.InvariantProjection
import QICLean.Kraus.MixedMap.GaugeConstruction
import TNLean.MPS.Transfer.Spectrum.MPVOverlapTrace
import QICLean.Kraus.MixedMap.TransferOperatorGapNormalized
import TNLean.MPS.Tensor.BondReindex
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.Transfer.Primitivity.ImpliesStronglyIrreducible

/-!
# Transfer-operator gap for normal tensor blocks

The operator statements in this file are compatibility results for matrix-product tensors. Their
finite-family forms are proved in `QICLean.Kraus.MixedMap.Gap`; only transfer-map and overlap
notation remains here.

It also contains the following results.

* `MPSTensor.tendsto_mpvOverlap_uncast_left`,
  `MPSTensor.mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`: cast-aware
  overlap-decay lemmas.
* `MPSTensor.mixedMap_eigenvalue_norm_lt_one_of_spectralRadius_lt_one`,
  `MPSTensor.mixedMap_eigenvalue_norm_lt_one_of_normal_inequivalent`: strict mixed eigenvalue bounds
  for inequivalent normal blocks.
-/

open MPTensor

section TransferOperatorGapNT

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal Kraus

namespace MPSTensor

variable {d D D₁ D₂ : ℕ}

theorem gaugePhaseEquiv_of_krausGaugePhaseEquiv
    {A B : MPSTensor d D} (h : Kraus.GaugePhaseEquiv A B) :
    GaugePhaseEquiv A B := by
  rcases eq_or_ne D 0 with rfl | hD
  · exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  let _ : NeZero D := ⟨hD⟩
  rcases h with ⟨X, Xinv, μ, hXXinv, hXinvX, hμ, hInter⟩
  have hμ_ne0 : μ ≠ 0 := Complex.ne_zero_of_norm_eq_one hμ
  let Y : GL (Fin D) ℂ := ⟨Xinv, X, hXinvX, hXXinv⟩
  refine ⟨Y, μ⁻¹, inv_ne_zero hμ_ne0, fun i => ?_⟩
  have hstep : Xinv * A i * X = μ • B i := by
    calc
      Xinv * A i * X = Xinv * (A i * X) := Matrix.mul_assoc _ _ _
      _ = Xinv * (μ • X * B i) := by rw [hInter i]
      _ = Xinv * (μ • (X * B i)) := by rw [smul_mul_assoc]
      _ = μ • (Xinv * (X * B i)) := by rw [mul_smul_comm]
      _ = μ • (Xinv * X * B i) := by rw [Matrix.mul_assoc]
      _ = μ • (1 * B i) := by rw [hXinvX]
      _ = μ • B i := by rw [Matrix.one_mul]
  change B i = μ⁻¹ • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i *
    ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
  change B i = μ⁻¹ • (Xinv * A i * X)
  rw [hstep, smul_smul, inv_mul_cancel₀ hμ_ne0, one_smul]

/-- Intertwining after invertible gauges yields gauge-phase equivalence of the original tensors. -/
theorem gaugePhaseEquiv_of_gauged_intertwining
    (A B : MPSTensor d D)
    (SA SB X' : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hSA_det : SA.det ≠ 0) (hSB_det : SB.det ≠ 0)
    (hX'_u : IsUnit X'.det) (hμ : ‖μ‖ = 1)
    (hInter :
      ∀ i : Fin d, Kraus.gaugeTensor SA A i * X' = μ • X' * Kraus.gaugeTensor SB B i) :
    GaugePhaseEquiv A B := by
  rcases eq_or_ne D 0 with rfl | hD
  · exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  let _ : NeZero D := ⟨hD⟩
  exact gaugePhaseEquiv_of_krausGaugePhaseEquiv <|
    Kraus.gaugePhaseEquiv_of_gauged_intertwining
      A B SA SB X' μ hSA_det hSB_det hX'_u hμ hInter

/-- If the mixed transfer spectral radius of two irreducible left-canonical tensors is at least
`1`, then the tensors are gauge-phase equivalent. -/
theorem modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : Kraus.mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B :=
  gaugePhaseEquiv_of_krausGaugePhaseEquiv <|
    Kraus.modulus_one_mixedMapSpectralRadius_implies_gauge A B
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA_irr)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB_irr)
      hA_left hB_left (by
        simpa [Kraus.mixedTransferSpectralRadius, Kraus.mixedMapLM,
          Kraus.mixedMapSpectralRadius] using hsr)

/-- Strict mixed-transfer-operator gap for distinct irreducible left-canonical blocks of the
same bond dimension. -/
theorem spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Kraus.mixedTransferSpectralRadius A B < 1 := by
  have hK : ¬ Kraus.GaugePhaseEquiv A B :=
    fun h => hAB (gaugePhaseEquiv_of_krausGaugePhaseEquiv h)
  simpa [Kraus.mixedTransferSpectralRadius, Kraus.mixedMapLM,
    Kraus.mixedMapSpectralRadius] using
    Kraus.mixedMapSpectralRadius_lt_one_of_irreducible_TP A B
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA_irr)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB_irr)
      hA_left hB_left hK

/-- Mixed transfer iterates decay for distinct irreducible left-canonical blocks. -/
theorem mixedTransfer_pow_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((Kraus.mixedMapLM A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  have hK : ¬ Kraus.GaugePhaseEquiv A B :=
    fun h => hAB (gaugePhaseEquiv_of_krausGaugePhaseEquiv h)
  simpa [Kraus.mixedMapLM] using
    Kraus.mixedMapLM_pow_tendsto_zero_of_irreducible_TP A B
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA_irr)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB_irr)
      hA_left hB_left hK X

/-- Overlap decay for distinct irreducible left-canonical blocks of the same bond dimension. -/
theorem mpvOverlap_tendsto_zero_of_irreducible_TP [NeZero D]
    (A B : MPSTensor d D)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap A B N) Filter.atTop (nhds 0) :=
  mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <|
    by simpa [Kraus.mixedTransferSpectralRadius] using
      spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hAB

/-- Rectangular strict transfer-operator gap for irreducible left-canonical blocks of different
bond sizes. -/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Kraus.mixedTransferSpectralRadius₂ A B < 1 := by
  simpa [Kraus.mixedTransferSpectralRadius₂, Kraus.mixedMapLM,
    Kraus.mixedMapSpectralRadius] using
    Kraus.mixedMapSpectralRadius_lt_one_of_dim_ne_of_irreducible_TP A B
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA_irr)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB_irr)
      hA_left hB_left hD

/-- Overlap decay for irreducible left-canonical blocks of different bond dimensions. -/
theorem mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap A B N) Filter.atTop (nhds 0) := by
  apply mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B)
  simpa only [Kraus.mixedTransferSpectralRadius₂] using
    mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
      A B hA_irr hB_irr hA_left hB_left hD

end MPSTensor

end TransferOperatorGapNT

section CastDecay

/-!
## Cast-aware overlap-decay lemmas

This module records the recurring pattern where an equal-dimension hypothesis is used to cast the
left tensor before applying an overlap-decay theorem, and the resulting limit is transported back to
the original uncasted overlap.
-/

open scoped BigOperators Matrix
open Filter

namespace MPSTensor

/-- Transport an overlap-decay limit from a casted left tensor back to the original tensor. -/
theorem tendsto_mpvOverlap_uncast_left
    {d D₁ D₂ : ℕ} (hdim : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hcast :
      Tendsto (fun N => mpvOverlap (α := Fin d) (cast (congr_arg (MPSTensor d) hdim) A) B N)
        atTop (nhds 0)) :
    Tendsto (fun N => mpvOverlap (α := Fin d) A B N) atTop (nhds 0) :=
  hcast.congr fun N => mpvOverlap_cast_dim_left hdim A B N

/-- If the left tensor is cast along a dimension equality, then the irreducible / TP
overlap-decay theorem still yields decay for the original uncasted overlap. -/
theorem mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂] (hdim : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (hNot :
      ¬ GaugePhaseEquiv (α := Fin d) (cast (congr_arg (MPSTensor d) hdim) A) B) :
    Tendsto (fun N => mpvOverlap (α := Fin d) A B N) atTop (nhds 0) := by
  have hAcst_irr : Kraus.IsIrreducibleFamily (cast (congr_arg (MPSTensor d) hdim) A) :=
    (isIrreducibleFamily_cast_dim hdim A).mpr hA_irr
  have hAcst_norm :
      ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) A i)ᴴ *
          (cast (congr_arg (MPSTensor d) hdim) A i) = 1 :=
    (leftCanonical_cast_dim hdim A).mpr hA_norm
  exact tendsto_mpvOverlap_uncast_left hdim A B <| mpvOverlap_tendsto_zero_of_irreducible_TP
    (cast (congr_arg (MPSTensor d) hdim) A) B hAcst_irr hB_irr hAcst_norm hB_norm hNot

end MPSTensor

end CastDecay

section MixedEigenvalueGap

/-!
## Strict mixed eigenvalue bounds for inequivalent normal blocks

The mixed-transfer spectral gap of inequivalent normal left-canonical blocks bounds every
mixed eigenvalue strictly below one. The bond dimensions may differ; gauge-phase
inequivalence is required only when the dimensions agree.

### References

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
    (isIrreducibleFamily_of_isNormal A hA)
  have hBi := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B
    (isIrreducibleFamily_of_isNormal B hB)
  by_cases hD : D₁ = D₂
  · subst D₁
    exact Kraus.mixedMapSpectralRadius_lt_one_of_irreducible_TP A B hAi hBi hAleft hBleft
      (fun h => hneq rfl (gaugePhaseEquiv_of_krausGaugePhaseEquiv h))
  · exact Kraus.mixedMapSpectralRadius_lt_one_of_dim_ne_of_irreducible_TP
      A B hAi hBi hAleft hBleft hD

end MPSTensor

end MixedEigenvalueGap
