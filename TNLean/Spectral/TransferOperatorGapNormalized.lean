/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Spectral.TransferOperatorGapRectNormalized

/-!
# Normalized square transfer-operator bounds

This file specializes the mixed-map spectral bounds in
`TNLean.Kraus.MixedMap.SpectralRadius` to the square case `D₁ = D₂ = D`.

## Main results

* `eigenvalue_norm_le_one`: every eigenvalue of `F_{AB}` has modulus at most one.
* `spectralRadius_mixedTransfer_le_one`: $ρ(F_{AB}) ≤ 1$ for normalized tensors.

## References

* CPGSV21: Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product States and Projected Entangled Pair States*,
  Rev. Mod. Phys. 93 (2021), arXiv:2011.12127, Sections 2.3 and 4.
* [Wolf2012Quantum] Wolf, *Quantum Channels & Operations: Guided Tour*,
  Proposition 6.1, Theorem 6.6, Section 6.2.
* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007, Lemma 5.
-/

open scoped Matrix TNOperatorSpace ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

/-- The spectral radius of the mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
      (mixedTransferMap A B))

theorem mixedTransferSpectralRadius_eq (A B : MPSTensor d D) :
    mixedTransferSpectralRadius A B =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (mixedTransferMap A B)) := rfl

/-- In equal bond dimension, the rectangular and square spectral radii agree. -/
@[simp]
theorem mixedTransferSpectralRadius₂_same_dim (A B : MPSTensor d D) :
    mixedTransferSpectralRadius₂ A B = mixedTransferSpectralRadius A B := by
  rw [mixedTransferSpectralRadius₂_eq, mixedTransferSpectralRadius_eq,
    mixedTransferMap₂_same_dim]

/-- Every eigenvalue of the mixed transfer operator has modulus at most one. -/
theorem eigenvalue_norm_le_one
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap A B) μ) :
    ‖μ‖ ≤ 1 :=
  Kraus.eigenvalue_norm_le_one_mixedMapLM_of_isTP A B hA_norm hB_norm μ hμ

/-- The mixed transfer operator of normalized tensors has spectral radius at most one. -/
theorem spectralRadius_mixedTransfer_le_one
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius A B ≤ 1 := by
  rw [mixedTransferSpectralRadius_eq]
  simpa [Kraus.mixedMapSpectralRadius, mixedTransferMap] using
    Kraus.mixedMapSpectralRadius_le_one_of_isTP A B hA_norm hB_norm

end MPSTensor
