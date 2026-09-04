/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint
import QICLean.Kraus.Transfer

/-!
# MPS vocabulary for primitive fixed points

This module exposes the finite-Kraus complementary fixed-point-gap certificates from
QICLean under the established matrix-product-state vocabulary. The abbreviations are
reducible, so the QIC fields and generic methods remain available definitionally, without
a separate MPS-facing forwarding declaration or conversion theorem.

## Main definitions

* `IsPrimitiveMPS`: MPS-facing name for `Kraus.HasComplementaryFixedPointGap`.
* `HasPrimitiveFixedPoint`: MPS-facing name for `Kraus.HasPrimitiveFixedPoint`.

## Main results

* `fixedPointProj_smul`: the fixed-point projection depends only on the ray through the
  fixed point.
* `MPSTensor.IsPrimitiveMPS.smul_inv_trace`: rescaling a positive-definite primitive fixed
  point to unit trace preserves the complementary fixed-point gap.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators Kraus

/-- The rank-one fixed-point projection \(X\mapsto(\operatorname{tr}X/\operatorname{tr}
\rho)\rho\) is unchanged when the fixed point is rescaled by a nonzero scalar. -/
theorem fixedPointProj_smul {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) {c : ℂ}
    (hcρ : Matrix.trace (c • ρ) ≠ 0) (hρ : Matrix.trace ρ ≠ 0) :
    fixedPointProj (c • ρ) hcρ = fixedPointProj ρ hρ := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hcρ
  ext X i j
  simp only [fixedPointProj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_smul,
    smul_eq_mul, Matrix.smul_apply, smul_eq_mul]
  field_simp

namespace MPSTensor

/-- An MPS tensor is **primitive** (with witness `ρ`) when its finite Kraus family has a
complementary fixed-point gap at `ρ`.

This reducible abbreviation preserves the public MPS vocabulary while exposing
`Kraus.HasComplementaryFixedPointGap` and all of its field projections definitionally. -/
abbrev IsPrimitiveMPS {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  Kraus.HasComplementaryFixedPointGap A ρ

/-- An MPS tensor **has a primitive fixed point** when its finite Kraus family has one.

This reducible abbreviation preserves the existential MPS vocabulary while reusing
`Kraus.HasPrimitiveFixedPoint` directly. -/
abbrev HasPrimitiveFixedPoint {d D : ℕ} [NeZero D] (A : MPSTensor d D) : Prop :=
  Kraus.HasPrimitiveFixedPoint A

/-- Rescaling a positive-definite primitive fixed point to unit trace preserves the
complementary fixed-point gap. Only the ray through the fixed point enters the gap
certificate, so the normalized witness carries the same primitivity data. -/
theorem IsPrimitiveMPS.smul_inv_trace {d D : ℕ} [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) :
    IsPrimitiveMPS A ((Matrix.trace ρ)⁻¹ • ρ) := by
  have htr_pos : 0 < Matrix.trace ρ := hρ.trace_pos
  have htr_ne : Matrix.trace ρ ≠ 0 := ne_of_gt htr_pos
  have hinv_pos : 0 < (Matrix.trace ρ)⁻¹ := inv_pos.mpr htr_pos
  have hpd : ((Matrix.trace ρ)⁻¹ • ρ).PosDef := hρ.smul hinv_pos
  have hne : Matrix.trace ((Matrix.trace ρ)⁻¹ • ρ) ≠ 0 := ne_of_gt hpd.trace_pos
  refine ⟨hP.norm, fun h ↦ hne (by rw [h, Matrix.trace_zero]), hpd.posSemidef, ?_, ?_⟩
  · rw [LinearMap.map_smul, hP.fixedPoint_is_fixed]
  · simpa only [fixedPointProj_smul ρ hne htr_ne] using
      hP.complementary_transfer_map_gap

end MPSTensor
