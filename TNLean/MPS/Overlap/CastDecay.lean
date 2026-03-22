/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Overlap.CastLemmas
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.SpectralGapNT

/-!
# Cast-aware overlap-decay helpers

This module packages the recurring pattern where an equal-dimension hypothesis is used to cast the
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
      Tendsto (fun N => mpvOverlap (d := d) (cast (congr_arg (MPSTensor d) hdim) A) B N)
        atTop (nhds 0)) :
    Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0) :=
  hcast.congr fun N => mpvOverlap_cast_dim_left hdim A B N

/-- If the left tensor is cast along a dimension equality, then the injective overlap-decay theorem
still yields decay for the original uncasted overlap. -/
theorem mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂] (hdim : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (hNot :
      ¬ GaugePhaseEquiv (d := d) (cast (congr_arg (MPSTensor d) hdim) A) B) :
    Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0) := by
  have hAcst_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) A) :=
    (isInjective_cast_dim hdim A).mpr hA_inj
  have hAcst_norm :
      ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) A i)ᴴ *
          (cast (congr_arg (MPSTensor d) hdim) A i) = 1 :=
    (leftCanonical_cast_dim hdim A).mpr hA_norm
  exact tendsto_mpvOverlap_uncast_left hdim A B <| mpvOverlap_tendsto_zero
    (cast (congr_arg (MPSTensor d) hdim) A) B hAcst_inj hB_inj hAcst_norm hB_norm hNot

/-- If the left tensor is cast along a dimension equality, then the irreducible / TP
overlap-decay theorem still yields decay for the original uncasted overlap. -/
theorem mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂] (hdim : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * (A i) = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * (B i) = 1)
    (hNot :
      ¬ GaugePhaseEquiv (d := d) (cast (congr_arg (MPSTensor d) hdim) A) B) :
    Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0) := by
  have hAcst_irr : IsIrreducibleTensor (cast (congr_arg (MPSTensor d) hdim) A) :=
    (isIrreducibleTensor_cast_dim hdim A).mpr hA_irr
  have hAcst_norm :
      ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) A i)ᴴ *
          (cast (congr_arg (MPSTensor d) hdim) A i) = 1 :=
    (leftCanonical_cast_dim hdim A).mpr hA_norm
  exact tendsto_mpvOverlap_uncast_left hdim A B <| mpvOverlap_tendsto_zero_of_irreducible_TP
    (cast (congr_arg (MPSTensor d) hdim) A) B hAcst_irr hB_irr hAcst_norm hB_norm hNot

end MPSTensor
