/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.MixedMap.Gap
import TNLean.Kraus.MixedMap.SpectralRadius
import TNLean.Spectral.MixedTransfer

/-!
# Normalized rectangular transfer-operator bounds

This module proves the normalized bound $ρ(F_{AB}) ≤ 1$ for the rectangular mixed
transfer operator and pointwise decay of its powers when the spectral radius is
strictly below one. The strict dimension-mismatch and overlap-decay theorems are
proved separately from the normalized estimate.

## Main results

* `spectralRadius_mixedTransfer₂_le_one`: the rectangular mixed transfer
  operator of normalized tensors has spectral radius at most one.
* `mixedTransferMap₂_pow_tendsto_zero_of_spectralRadius_lt_one`: a rectangular
  mixed transfer operator with spectral radius below one has pointwise-vanishing
  powers.

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007, Lemma 5.
* CPSV16: Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and Boundary
  Theories*, arXiv:1606.00608, Appendix B, equations `EasEkk`--`Ekk`.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators NNReal ENNReal Matrix.Norms.Operator

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ## Rectangular spectral radius abbreviation -/

/-- The **spectral radius** of the rectangular mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius₂
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
      (mixedTransferMap₂ A B))

theorem mixedTransferSpectralRadius₂_eq
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    mixedTransferSpectralRadius₂ A B =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
          (mixedTransferMap₂ A B)) := rfl

/-! ## Eigenvalue and spectral-radius bounds -/

/-- Every eigenvalue of the rectangular mixed transfer operator has modulus ≤ 1. -/
theorem eigenvalue_norm_le_one₂
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ) :
    ‖μ‖ ≤ 1 :=
  Kraus.eigenvalue_norm_le_one_mixedMapLM_of_isTP A B hA_norm hB_norm μ hμ

/-- **Spectral radius bound**: `ρ(F₂) ≤ 1` for normalized tensors. -/
theorem spectralRadius_mixedTransfer₂_le_one
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius₂ A B ≤ 1 :=
  Kraus.mixedMapSpectralRadius_le_one_of_isTP A B hA_norm hB_norm

/-! ## Power decay -/

/--
If the rectangular mixed transfer operator has spectral radius strictly below one, then its
powers converge pointwise to zero.

This is the decay step for the off-diagonal operators in CPSV16, Appendix B,
equations `EasEkk`--`Ekk` and line 1243.
-/
theorem mixedTransferMap₂_pow_tendsto_zero_of_spectralRadius_lt_one
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : mixedTransferSpectralRadius₂ A B < 1)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap₂ A B) ^ n) X)
      Filter.atTop (nhds 0) :=
  Kraus.mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one A B h X

/-!
Strict dimension-mismatch consequences are intentionally downstream in
`TransferOperatorGapNT` and `TransferOperatorGapInjective`.  This module contains
only the shared rectangular spectral-radius bound and its analytic decay consequence.
-/

end MPSTensor
