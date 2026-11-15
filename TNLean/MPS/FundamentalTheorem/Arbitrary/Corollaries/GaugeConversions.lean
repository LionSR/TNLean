/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks
import TNLean.MPS.Periodic.EqualCaseGlobal.Canonical

/-!
# From gauge relations to the library's gauge equivalences

The fundamental theorem for arbitrary tensors concludes `IsGaugeRelated` (an invertible
rectangular matrix intertwining the letters). The library's fundamental theorems use
`GaugeEquiv`, `GaugePhaseEquiv` and `ScalarGaugeEquiv`, all with a witness in `GL`. This file
states the conversions.

## Main results

* `MPSTensor.isGaugeRelated_iff_gaugeEquiv`: equal bond dimension, no scalar.
* `MPSTensor.gaugePhaseEquiv_iff_exists_ne_zero_and_isGaugeRelated_smul`: a nonzero scalar.
* `MPSTensor.scalarGaugeEquiv_iff_isGaugeRelated_smul`: a named scalar, possibly different bond
  dimensions.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **No scalar.** At equal bond dimension, a gauge relation is a gauge equivalence with a
`GL` witness. -/
theorem isGaugeRelated_iff_gaugeEquiv {D : ℕ} {A B : MPSTensor d D} :
    IsGaugeRelated A B ↔ GaugeEquiv A B := by
  constructor
  · rintro ⟨X, Y, hXY, hYX, hint⟩
    refine ⟨⟨Y, X, hYX, hXY⟩, fun i => ?_⟩
    change B i = Y * A i * X
    rw [Matrix.mul_assoc, hint, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
  · rintro ⟨G, hG⟩
    refine ⟨((G⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), (G : Matrix (Fin D) (Fin D) ℂ),
      Units.inv_mul G, Units.mul_inv G, fun i => ?_⟩
    rw [hG i, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- **Nonzero scalar.** Gauge-phase equivalence of `A` and `B` is a gauge relation between a
nonzero multiple of `A` and `B`. -/
theorem gaugePhaseEquiv_iff_exists_ne_zero_and_isGaugeRelated_smul {D : ℕ}
    {A B : MPSTensor d D} :
    GaugePhaseEquiv A B ↔ ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (c • A) B := by
  constructor
  · rintro ⟨X, ζ, hζ, h⟩
    refine ⟨ζ, hζ, isGaugeRelated_iff_gaugeEquiv.2 ⟨X, fun i => ?_⟩⟩
    rw [h i, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
  · rintro ⟨c, hc, h⟩
    obtain ⟨X, hX⟩ := isGaugeRelated_iff_gaugeEquiv.1 h
    refine ⟨X, c, hc, fun i => ?_⟩
    rw [hX i, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- **Named scalar.** `ScalarGaugeEquiv ζ A B`, that is `A = ζ • Y B Y⁻¹` after identifying
the bond dimensions, is the gauge relation between `A` and `ζ • B`. -/
theorem scalarGaugeEquiv_iff_isGaugeRelated_smul {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {B : MPSTensor d D₂} {ζ : ℂ} :
    ScalarGaugeEquiv ζ A B ↔ IsGaugeRelated A (ζ • B) := by
  constructor
  · rintro ⟨hD, Y, hY⟩
    subst hD
    refine (isGaugeRelated_iff_gaugeEquiv.2 ⟨Y, fun i => ?_⟩).symm
    have h := hY i
    rw [cast_eq] at h
    rw [h, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
  · intro h
    obtain rfl := h.dim_eq
    obtain ⟨Y, hY⟩ := isGaugeRelated_iff_gaugeEquiv.1 h.symm
    refine ⟨rfl, Y, fun i => ?_⟩
    rw [cast_eq, hY i, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]

end MPSTensor
