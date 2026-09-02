/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWOverlapEstimate

/-!
# FNW aggregate orthogonality estimates

This module proves the quadratic aggregate contribution in Fannes--
Nachtergaele--Werner, *Communications in Mathematical Physics* 144 (1992),
Lemma 6.2. Orthogonality to the full boundary range is first tested against the
special full-ground spectator families. Equation (5.9) then gives the two dual
aggregate estimates before any lower-boundary conversion. The one-sided square
root estimates convert these to the sharp coefficient
\(a(m)/\sqrt{a_-(m)}\), whose product is \(a(m)^2/a_-(m)\).

The quadratic contribution remains separate from equation (6.5) until the final
theorem in this module, where the two coefficients are added without factoring.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The range of the full FNW boundary map at a fixed chain length. -/
noncomputable def fnwBoundaryRange
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (N : ℕ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  exact LinearMap.range (fnwBoundaryMapCLM ρ hρ A N).toLinearMap

/-- Testing a left overlap vector orthogonal to the full boundary range against
one special full-ground family gives the unconverted dual estimate for its
aggregate. -/
theorem norm_inner_fnwLeftOverlapAggregate_le_familyNorm [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (horth : fnwLeftOverlapMap ρ hρ A ℓ m r Φ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapAggregate ρ A r Φ) B‖ ≤
      fnwMixingQuantity ρ hρ A htr m * ‖Φ‖ * ‖B‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have hfull :
      inner ℂ (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B)
        (fnwLeftOverlapMap ρ hρ A ℓ m r Φ) = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _
      (LinearMap.mem_range_self
        (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r)).toLinearMap B)
  have hfull' :
      inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B) = 0 := by
    rw [← inner_conj_symm, hfull, map_zero]
  have hbound := norm_inner_overlap_sub_inner_aggregates_le_familyNorms
    ρ hρ htr A hA hρfix ℓ m r Φ (fnwRightFullGroundFamily A ℓ B)
  rw [fnwRightOverlapMap_fullGroundFamily,
    fnwRightOverlapAggregate_fullGroundFamily ρ hρ A hA,
    norm_fnwRightFullGroundFamily ρ hρ A hA, hfull', zero_sub, norm_neg] at hbound
  exact hbound

/-- Testing a right overlap vector orthogonal to the full boundary range against
one special full-ground family gives the unconverted dual estimate for its
aggregate. -/
theorem norm_inner_fnwRightOverlapAggregate_le_familyNorm [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (horth : fnwRightOverlapMap ρ hρ A ℓ m r Ψ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (B : Mat) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ B (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      fnwMixingQuantity ρ hρ A htr m * ‖B‖ * ‖Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have hfull :
      inner ℂ (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r) B)
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _
      (LinearMap.mem_range_self
        (fnwBoundaryMapCLM ρ hρ A ((ℓ + m) + r)).toLinearMap B)
  have hbound := norm_inner_overlap_sub_inner_aggregates_le_familyNorms
    ρ hρ htr A hA hρfix ℓ m r (fnwLeftFullGroundFamily A r B) Ψ
  rw [fnwLeftOverlapMap_fullGroundFamily,
    fnwLeftOverlapAggregate_fullGroundFamily ρ hρ A hρfix,
    norm_fnwLeftFullGroundFamily ρ hρ A hρfix, hfull, zero_sub, norm_neg] at hbound
  exact hbound

/-- Before lower-boundary conversion, the left aggregate norm is controlled by
\(a(m)\) times its spectator-family norm. -/
theorem norm_fnwLeftOverlapAggregate_le_familyNorm [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (horth : fnwLeftOverlapMap ρ hρ A ℓ m r Φ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖fnwLeftOverlapAggregate ρ A r Φ‖ ≤
      fnwMixingQuantity ρ hρ A htr m * ‖Φ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have hdual := norm_inner_fnwLeftOverlapAggregate_le_familyNorm
    ρ hρ htr A hA hρfix ℓ m r Φ horth (fnwLeftOverlapAggregate ρ A r Φ)
  rw [inner_self_eq_norm_sq_to_K] at hdual
  have hdualReal :
      ‖fnwLeftOverlapAggregate ρ A r Φ‖ ^ 2 ≤
        fnwMixingQuantity ρ hρ A htr m * ‖Φ‖ *
          ‖fnwLeftOverlapAggregate ρ A r Φ‖ := by
    exact_mod_cast hdual
  have hdual' :
      ‖fnwLeftOverlapAggregate ρ A r Φ‖ * ‖fnwLeftOverlapAggregate ρ A r Φ‖ ≤
        (fnwMixingQuantity ρ hρ A htr m * ‖Φ‖) *
          ‖fnwLeftOverlapAggregate ρ A r Φ‖ := by
    simpa only [pow_two, mul_assoc] using hdualReal
  rcases (norm_nonneg (fnwLeftOverlapAggregate ρ A r Φ)).eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg
      (mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _))
      (norm_nonneg Φ)
  · exact le_of_mul_le_mul_right hdual' hpos

/-- Before lower-boundary conversion, the right aggregate norm is controlled by
\(a(m)\) times its spectator-family norm. -/
theorem norm_fnwRightOverlapAggregate_le_familyNorm [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (horth : fnwRightOverlapMap ρ hρ A ℓ m r Ψ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖fnwRightOverlapAggregate A ℓ Ψ‖ ≤
      fnwMixingQuantity ρ hρ A htr m * ‖Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have hdual := norm_inner_fnwRightOverlapAggregate_le_familyNorm
    ρ hρ htr A hA hρfix ℓ m r Ψ horth (fnwRightOverlapAggregate A ℓ Ψ)
  rw [inner_self_eq_norm_sq_to_K] at hdual
  have hdualReal :
      ‖fnwRightOverlapAggregate A ℓ Ψ‖ ^ 2 ≤
        fnwMixingQuantity ρ hρ A htr m *
          ‖fnwRightOverlapAggregate A ℓ Ψ‖ * ‖Ψ‖ := by
    exact_mod_cast hdual
  have hdual' :
      ‖fnwRightOverlapAggregate A ℓ Ψ‖ * ‖fnwRightOverlapAggregate A ℓ Ψ‖ ≤
        (fnwMixingQuantity ρ hρ A htr m * ‖Ψ‖) *
          ‖fnwRightOverlapAggregate A ℓ Ψ‖ := by
    calc
      ‖fnwRightOverlapAggregate A ℓ Ψ‖ * ‖fnwRightOverlapAggregate A ℓ Ψ‖ =
          ‖fnwRightOverlapAggregate A ℓ Ψ‖ ^ 2 := by ring
      _ ≤ fnwMixingQuantity ρ hρ A htr m *
          ‖fnwRightOverlapAggregate A ℓ Ψ‖ * ‖Ψ‖ := hdualReal
      _ = (fnwMixingQuantity ρ hρ A htr m * ‖Ψ‖) *
          ‖fnwRightOverlapAggregate A ℓ Ψ‖ := by ring
  rcases (norm_nonneg (fnwRightOverlapAggregate A ℓ Ψ)).eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg
      (mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _))
      (norm_nonneg Ψ)
  · exact le_of_mul_le_mul_right hdual' hpos

/-- The sharp left aggregate estimate uses only the one-sided square-root lower
bound for the corresponding left overlap map. -/
theorem norm_fnwLeftOverlapAggregate_le_div_sqrt_lowerBoundary [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (horth : fnwLeftOverlapMap ρ hρ A ℓ m r Φ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖fnwLeftOverlapAggregate ρ A r Φ‖ ≤
      (fnwMixingQuantity ρ hρ A htr m /
        Real.sqrt (fnwLowerBoundaryConstant ρ hρ A m)) *
        ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let a := fnwMixingQuantity ρ hρ A htr m
  let c := fnwLowerBoundaryConstant ρ hρ A m
  let s := Real.sqrt c
  have ha : 0 ≤ a :=
    mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)
  have hs : 0 < s := Real.sqrt_pos.2 hminus
  have hfamily := sqrt_fnwLowerBoundaryConstant_mul_familyNorm_le_leftOverlap
    ρ hρ A hρfix ℓ m r Φ hminus
  calc
    ‖fnwLeftOverlapAggregate ρ A r Φ‖ ≤ a * ‖Φ‖ :=
      norm_fnwLeftOverlapAggregate_le_familyNorm
        ρ hρ htr A hA hρfix ℓ m r Φ horth
    _ = (a / s) * (s * ‖Φ‖) := by
      rw [← mul_assoc, div_mul_cancel₀ a hs.ne']
    _ ≤ (a / s) * ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ :=
      mul_le_mul_of_nonneg_left hfamily (div_nonneg ha hs.le)

/-- The sharp right aggregate estimate uses only the one-sided square-root lower
bound for the corresponding right overlap map. -/
theorem norm_fnwRightOverlapAggregate_le_div_sqrt_lowerBoundary [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (horth : fnwRightOverlapMap ρ hρ A ℓ m r Ψ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖fnwRightOverlapAggregate A ℓ Ψ‖ ≤
      (fnwMixingQuantity ρ hρ A htr m /
        Real.sqrt (fnwLowerBoundaryConstant ρ hρ A m)) *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let a := fnwMixingQuantity ρ hρ A htr m
  let c := fnwLowerBoundaryConstant ρ hρ A m
  let s := Real.sqrt c
  have ha : 0 ≤ a :=
    mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)
  have hs : 0 < s := Real.sqrt_pos.2 hminus
  have hfamily := sqrt_fnwLowerBoundaryConstant_mul_familyNorm_le_rightOverlap
    ρ hρ A hρfix ℓ m r Ψ hminus
  calc
    ‖fnwRightOverlapAggregate A ℓ Ψ‖ ≤ a * ‖Ψ‖ :=
      norm_fnwRightOverlapAggregate_le_familyNorm
        ρ hρ htr A hA hρfix ℓ m r Ψ horth
    _ = (a / s) * (s * ‖Ψ‖) := by
      rw [← mul_assoc, div_mul_cancel₀ a hs.ne']
    _ ≤ (a / s) * ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ :=
      mul_le_mul_of_nonneg_left hfamily (div_nonneg ha hs.le)

/-- Orthogonality of both overlap vectors to the full boundary range gives the
quadratic aggregate pairing coefficient \(a(m)^2/a_-(m)\). -/
theorem norm_inner_fnwOverlapAggregates_le_sq_div_lowerBoundary [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (horthΦ : fnwLeftOverlapMap ρ hρ A ℓ m r Φ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (horthΨ : fnwRightOverlapMap ρ hρ A ℓ m r Ψ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
        (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      (fnwMixingQuantity ρ hρ A htr m ^ 2 /
        fnwLowerBoundaryConstant ρ hρ A m) *
        ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let a := fnwMixingQuantity ρ hρ A htr m
  let c := fnwLowerBoundaryConstant ρ hρ A m
  let s := Real.sqrt c
  have hsquare : s ^ 2 = c := Real.sq_sqrt hminus.le
  have hleft := norm_fnwLeftOverlapAggregate_le_div_sqrt_lowerBoundary
    ρ hρ htr A hA hρfix ℓ m r Φ horthΦ hminus
  have hright := norm_fnwRightOverlapAggregate_le_div_sqrt_lowerBoundary
    ρ hρ htr A hA hρfix ℓ m r Ψ horthΨ hminus
  calc
    ‖inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
        (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
        ‖fnwLeftOverlapAggregate ρ A r Φ‖ *
          ‖fnwRightOverlapAggregate A ℓ Ψ‖ :=
      norm_inner_le_norm _ _
    _ ≤ ((a / s) * ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖) *
        ((a / s) * ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖) :=
      mul_le_mul hleft hright (norm_nonneg _)
        (mul_nonneg (div_nonneg
          (mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _))
          (Real.sqrt_nonneg c)) (norm_nonneg _))
    _ = (a ^ 2 / c) * ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
      rw [← hsquare, ← div_pow]
      ring

/-- The linear equation (6.5) contribution and the quadratic aggregate
contribution combine with the unfactored coefficient
\(a(m)/a_-(m)+a(m)^2/a_-(m)\). -/
theorem norm_inner_fnwOverlapMaps_le_linear_add_quadratic [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (horthΦ : fnwLeftOverlapMap ρ hρ A ℓ m r Φ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (horthΨ : fnwRightOverlapMap ρ hρ A ℓ m r Ψ ∈
      (fnwBoundaryRange ρ hρ A ((ℓ + m) + r))ᗮ)
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
        (fnwRightOverlapMap ρ hρ A ℓ m r Ψ)‖ ≤
      (fnwMixingQuantity ρ hρ A htr m /
          fnwLowerBoundaryConstant ρ hρ A m +
        fnwMixingQuantity ρ hρ A htr m ^ 2 /
          fnwLowerBoundaryConstant ρ hρ A m) *
        ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  let x := fnwLeftOverlapMap ρ hρ A ℓ m r Φ
  let y := fnwRightOverlapMap ρ hρ A ℓ m r Ψ
  let u := fnwLeftOverlapAggregate ρ A r Φ
  let v := fnwRightOverlapAggregate A ℓ Ψ
  let a := fnwMixingQuantity ρ hρ A htr m
  let c := fnwLowerBoundaryConstant ρ hρ A m
  have hlinear := norm_inner_overlap_sub_inner_aggregates_le_div_lowerBoundary
    ρ hρ htr A hA hρfix ℓ m r Φ Ψ hminus
  have hquadratic := norm_inner_fnwOverlapAggregates_le_sq_div_lowerBoundary
    ρ hρ htr A hA hρfix ℓ m r Φ Ψ horthΦ horthΨ hminus
  calc
    ‖inner ℂ x y‖ = ‖(inner ℂ x y - inner ℂ u v) + inner ℂ u v‖ := by ring_nf
    _ ≤ ‖inner ℂ x y - inner ℂ u v‖ + ‖inner ℂ u v‖ := norm_add_le _ _
    _ ≤ (a / c) * ‖x‖ * ‖y‖ + (a ^ 2 / c) * ‖x‖ * ‖y‖ :=
      add_le_add hlinear hquadratic
    _ = (a / c + a ^ 2 / c) * ‖x‖ * ‖y‖ := by ring

end

end MPSTensor
