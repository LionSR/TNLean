/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGapRect
import TNLean.Channel.PerronFrobeniusExistence
import TNLean.MPS.IrreducibleFormII

/-!
# Spectral gap for normal tensor (irreducible + TP) blocks

This file proves the overlap dichotomy for irreducible trace-preserving / left-canonical
blocks without assuming injectivity, following the Cauchy--Schwarz argument from
Cirac et al., arXiv:1606.00608, Appendix A, Lemma A.1.

The key new rigidity statement is
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`: if two irreducible
left-canonical tensors have mixed-transfer spectral radius at least `1`, then they are
already gauge-phase equivalent.

At the moment, the downstream strict-gap and overlap-decay consequences are fully wired
through the existing spectral-radius and overlap infrastructure, while the core
Cauchy--Schwarz rigidity step itself is left as a `sorry` placeholder.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D D₁ D₂ : ℕ}

section SameDimension

/--
**Rigidity for irreducible left-canonical blocks**.

This is the non-injective replacement for
`modulus_one_eigenvalue_implies_gauge` from `SpectralGap.lean`.

Informally, the intended proof is:

1. Use irreducibility plus left-canonical normalization to obtain positive-definite fixed
   points for the relevant transfer maps.
2. Pass to the CFII / weighted-KS gauge in which both tensors are still left-canonical and
   admit positive-definite fixed points.
3. Use the weighted Kadison--Schwarz equality for a peripheral mixed-transfer eigenvector.
4. Replace the injective kernel-spanning argument by the Cauchy--Schwarz equality case from
   Lemma A.1 of arXiv:1606.00608, yielding a Kraus-by-Kraus intertwining relation.
5. Conclude that the intertwiner is unitary and hence that the tensors are gauge-phase
   equivalent.
-/
theorem modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B := by
  sorry

/--
**Strict mixed-transfer spectral gap** for distinct irreducible left-canonical blocks of the
same bond dimension.
-/
theorem spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 := by
  refine lt_of_le_of_ne (spectralRadius_mixedTransfer_le_one A B hA_left hB_left) ?_
  intro hEq
  exact hAB <| modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    A B hA_irr hB_irr hA_left hB_left hEq.ge

/--
**Power decay** for the mixed transfer operator of distinct irreducible left-canonical
blocks of the same bond dimension.
-/
theorem mixedTransfer_pow_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  have h_clm : Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F' <| by
      simpa [F', Φ, mixedTransferSpectralRadius] using
        spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
          A B hA_irr hB_irr hA_left hB_left hAB
  have h_eval := (ContinuousLinearMap.apply ℂ V X).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at h_eval
  suffices hpow : ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X by
    simp_rw [hpow]
    exact h_eval.comp h_clm
  intro n
  have h_pow : F' ^ n = Φ ((mixedTransferMap A B) ^ n) := (map_pow Φ _ n).symm
  simp only [h_pow]
  rfl

end SameDimension

section SameDimensionOverlap

variable [NeZero D]

/--
**Overlap decay** for distinct irreducible left-canonical blocks of the same bond dimension.
-/
theorem mpvOverlap_tendsto_zero_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <| by
    simpa [mixedTransferSpectralRadius] using
      spectralRadius_mixedTransfer_lt_one_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hAB

end SameDimensionOverlap

section DifferentDimensions

/--
**Rectangular strict spectral gap** for irreducible left-canonical blocks of different bond
sizes.

The intended proof follows the same Cauchy--Schwarz rigidity mechanism as
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`, but in the rectangular setting:
a modulus-one peripheral eigenvector produces an isometry `X`, swapping the roles of `A`
and `B` upgrades this to a unitary, and hence forces equality of bond dimensions.
-/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    mixedTransferSpectralRadius₂ A B < 1 := by
  sorry

/--
**Overlap decay** for irreducible left-canonical blocks of different bond dimensions.
-/
theorem mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_left : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_left : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one (A := A) (B := B) <| by
    simpa [mixedTransferSpectralRadius₂] using
      mixedTransferSpectralRadius₂_lt_one_of_dim_ne_of_irreducible_TP
        A B hA_irr hB_irr hA_left hB_left hD

end DifferentDimensions

end MPSTensor
