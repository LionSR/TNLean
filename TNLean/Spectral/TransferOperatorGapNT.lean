/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.MixedMap.Gap
import TNLean.MPS.Core.TransferChannel
import TNLean.Spectral.GaugeConstruction
import TNLean.Spectral.MPVOverlapDecayRect
import TNLean.Spectral.TransferOperatorGapNormalized

/-!
# Transfer-operator gap for normal tensor blocks

The operator statements in this file are compatibility results for matrix-product tensors. Their
finite-family forms are proved in `TNLean.Kraus.MixedMap.Gap`; only transfer-map and overlap
notation remains here.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D D₁ D₂ : ℕ}

theorem gaugePhaseEquiv_of_krausGaugePhaseEquiv
    {A B : MPSTensor d D} (h : Kraus.GaugePhaseEquiv A B) :
    GaugePhaseEquiv A B := by
  rcases eq_or_ne D 0 with rfl | hD
  · exact ⟨1, 1, one_ne_zero, fun i => by ext a; exact a.elim0⟩
  let _ : NeZero D := ⟨hD⟩
  rcases h with ⟨X, Xinv, μ, hmul, _, hμ, hInter⟩
  have hX_u : IsUnit X.det := Matrix.isUnit_det_of_right_inverse hmul
  exact MPSTensor.gaugePhaseEquiv_of_gauged_intertwining
    (A := A) (B := B) (SA := 1) (SB := 1) (X' := X) (μ := μ)
    (by simp) (by simp) hX_u hμ (by simpa [gaugeTensor] using hInter)

private theorem irreducibleMap_of_irreducibleTensor
    (A : MPSTensor d D) (hA : IsIrreducibleTensor A) :
    IsIrreducibleMap (Kraus.mapLM A) :=
  Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA

/-- If the mixed transfer spectral radius of two irreducible left-canonical tensors is at least
`1`, then the tensors are gauge-phase equivalent. -/
theorem modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B :=
  gaugePhaseEquiv_of_krausGaugePhaseEquiv <|
    Kraus.modulus_one_mixedMapSpectralRadius_implies_gauge A B
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
      hA_left hB_left (by
        simpa [mixedTransferSpectralRadius, mixedTransferMap,
          Kraus.mixedMapSpectralRadius] using hsr)

/-- Strict mixed-transfer-operator gap for distinct irreducible left-canonical blocks of the
same bond dimension. -/
theorem spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 := by
  have hK : ¬ Kraus.GaugePhaseEquiv A B :=
    fun h => hAB (gaugePhaseEquiv_of_krausGaugePhaseEquiv h)
  simpa [mixedTransferSpectralRadius, mixedTransferMap,
    Kraus.mixedMapSpectralRadius] using
    Kraus.mixedMapSpectralRadius_lt_one_of_irreducible_TP A B
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
      hA_left hB_left hK

/-- Mixed transfer iterates decay for distinct irreducible left-canonical blocks. -/
theorem mixedTransfer_pow_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  have hK : ¬ Kraus.GaugePhaseEquiv A B :=
    fun h => hAB (gaugePhaseEquiv_of_krausGaugePhaseEquiv h)
  simpa [mixedTransferMap] using
    Kraus.mixedMapLM_pow_tendsto_zero_of_irreducible_TP A B
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
      hA_left hB_left hK X

/-- Overlap decay for distinct irreducible left-canonical blocks of the same bond dimension. -/
theorem mpvOverlap_tendsto_zero_of_irreducible_TP [NeZero D]
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap A B N) Filter.atTop (nhds 0) :=
  mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <|
    by simpa only [mixedTransferMap₂_same_dim, mixedTransferSpectralRadius] using
      spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hAB

/-- Rectangular strict transfer-operator gap for irreducible left-canonical blocks of different
bond sizes. -/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    mixedTransferSpectralRadius₂ A B < 1 := by
  simpa [mixedTransferSpectralRadius₂, mixedTransferMap₂,
    Kraus.mixedMapSpectralRadius] using
    Kraus.mixedMapSpectralRadius_lt_one_of_dim_ne_of_irreducible_TP A B
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
      hA_left hB_left hD

/-- Overlap decay for irreducible left-canonical blocks of different bond dimensions. -/
theorem mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap A B N) Filter.atTop (nhds 0) := by
  apply mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B)
  simpa only [mixedTransferSpectralRadius₂] using
    mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
      A B hA_irr hB_irr hA_left hB_left hD

end MPSTensor
