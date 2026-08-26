/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.MixedMap.Gap
import QICLean.Kraus.InvariantProjection
import QICLean.Spectral.GaugeConstruction
import TNLean.Spectral.MPVOverlapDecayRect
import QICLean.Spectral.TransferOperatorGapNormalized

/-!
# Transfer-operator gap for normal tensor blocks

The operator statements in this file are compatibility results for matrix-product tensors. Their
finite-family forms are proved in `QICLean.Kraus.MixedMap.Gap`; only transfer-map and overlap
notation remains here.
-/

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

private theorem irreducibleMap_of_irreducibleTensor
    (A : MPSTensor d D) (hA : Kraus.IsIrreducibleFamily A) :
    IsIrreducibleMap (Kraus.mapLM A) :=
  Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA

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
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
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
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
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
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
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
      (irreducibleMap_of_irreducibleTensor A hA_irr)
      (irreducibleMap_of_irreducibleTensor B hB_irr)
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
