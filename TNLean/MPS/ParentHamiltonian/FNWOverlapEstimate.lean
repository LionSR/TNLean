/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWOverlapCoordinates

/-!
# FNW overlap estimates

This module applies the FNW boundary estimate and lower-boundary constant to the
three-block overlap coordinates. It proves the linear contribution in Fannes--
Nachtergaele--Werner, *Communications in Mathematical Physics* 144 (1992),
equation (6.5), without introducing the later quadratic contribution.
-/

open scoped BigOperators ComplexOrder Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Equation (5.9), applied to every pair of spectator configurations and
combined by finite Cauchy--Schwarz. This is the analytic numerator in FNW
1992, equation (6.5), before the lower-boundary estimate is used. -/
theorem norm_inner_overlap_sub_inner_aggregates_le [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      fnwMixingQuantity ρ hρ A htr m *
        (Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwLeftMiddleBoundary A Φ p‖ ^ 2) *
        Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwRightMiddleBoundary A Ψ p‖ ^ 2)) := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  rw [inner_overlap_sub_inner_aggregates]
  calc
    ‖∑ p : Cfg d ℓ × Cfg d r,
        (inner ℂ
            (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
            (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
          inner ℂ (fnwLeftMiddleBoundary A Φ p)
            (fnwRightMiddleBoundary A Ψ p))‖
        ≤ ∑ p : Cfg d ℓ × Cfg d r,
          ‖inner ℂ
              (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
              (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
            inner ℂ (fnwLeftMiddleBoundary A Φ p)
              (fnwRightMiddleBoundary A Ψ p)‖ := by
          simpa using norm_sum_le (Finset.univ : Finset (Cfg d ℓ × Cfg d r))
            (fun p =>
              inner ℂ
                  (fnwBoundaryMapCLM ρ hρ A m (fnwLeftMiddleBoundary A Φ p))
                  (fnwBoundaryMapCLM ρ hρ A m (fnwRightMiddleBoundary A Ψ p)) -
                inner ℂ (fnwLeftMiddleBoundary A Φ p)
                  (fnwRightMiddleBoundary A Ψ p))
    _ ≤ ∑ p : Cfg d ℓ × Cfg d r,
        fnwMixingQuantity ρ hρ A htr m *
          ‖fnwLeftMiddleBoundary A Φ p‖ * ‖fnwRightMiddleBoundary A Ψ p‖ :=
      Finset.sum_le_sum fun p _ =>
        norm_inner_fnwBoundaryMapCLM_sub_rhoWeighted_le_fnwMixingQuantity
          ρ hρ htr A m (fnwLeftMiddleBoundary A Φ p)
            (fnwRightMiddleBoundary A Ψ p)
    _ = fnwMixingQuantity ρ hρ A htr m *
        ∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwLeftMiddleBoundary A Φ p‖ * ‖fnwRightMiddleBoundary A Ψ p‖ := by
      simpa only [mul_assoc] using
        (Finset.mul_sum (s := (Finset.univ : Finset (Cfg d ℓ × Cfg d r)))
          (f := fun p =>
            ‖fnwLeftMiddleBoundary A Φ p‖ * ‖fnwRightMiddleBoundary A Ψ p‖)
          (a := fnwMixingQuantity ρ hρ A htr m)).symm
    _ ≤ fnwMixingQuantity ρ hρ A htr m *
        (Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwLeftMiddleBoundary A Φ p‖ ^ 2) *
        Real.sqrt (∑ p : Cfg d ℓ × Cfg d r,
          ‖fnwRightMiddleBoundary A Ψ p‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (Cfg d ℓ × Cfg d r))
          (fun p => ‖fnwLeftMiddleBoundary A Φ p‖)
          (fun p => ‖fnwRightMiddleBoundary A Ψ p‖)
      · exact mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)

/-- The squared norm of the left overlap vector is the sum of the squared
boundary-map norms of its right-spectator family. -/
theorem norm_fnwLeftOverlapMap_sq
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ ^ 2 =
      ∑ μr : Cfg d r, ‖fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr)‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2]
  trans ∑ p : (Cfg d ℓ × Cfg d m) × Cfg d r,
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ (fnwThreeBlockConfigEquiv d ℓ m r p)‖ ^ 2
  · symm
    apply Fintype.sum_equiv (fnwThreeBlockConfigEquiv d ℓ m r)
    intro p
    rfl
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro μr _
    rw [PiLp.norm_sq_eq_of_L2]
    apply Fintype.sum_equiv (Fin.appendEquiv ℓ m)
    intro q
    rw [fnwThreeBlockConfigEquiv_apply, fnwLeftOverlapMap_apply_append]
    change ‖fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr)
      (Fin.append q.1 q.2)‖ ^ 2 =
        ‖fnwBoundaryMapCLM ρ hρ A (ℓ + m) (Φ.ofLp μr)
          (Fin.append q.1 q.2)‖ ^ 2
    rfl

/-- The squared norm of the right overlap vector is the sum of the squared
boundary-map norms of its left-spectator family. -/
theorem norm_fnwRightOverlapMap_sq
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ ^ 2 =
      ∑ μℓ : Cfg d ℓ, ‖fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ)‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2]
  trans ∑ p : (Cfg d ℓ × Cfg d m) × Cfg d r,
      ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ (fnwThreeBlockConfigEquiv d ℓ m r p)‖ ^ 2
  · symm
    apply Fintype.sum_equiv (fnwThreeBlockConfigEquiv d ℓ m r)
    intro p
    rfl
  · simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro μℓ _
    trans ∑ q : Cfg d m × Cfg d r,
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ
          (fnwThreeBlockConfigEquiv d ℓ m r ((μℓ, q.1), q.2))‖ ^ 2
    · rw [Fintype.sum_prod_type]
    · rw [PiLp.norm_sq_eq_of_L2]
      apply Fintype.sum_equiv (Fin.appendEquiv m r)
      intro q
      rw [fnwThreeBlockConfigEquiv_apply, fnwRightOverlapMap_apply_append]
      change ‖fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ)
        (Fin.append q.1 q.2)‖ ^ 2 =
          ‖fnwBoundaryMapCLM ρ hρ A (m + r) (Ψ.ofLp μℓ)
            (Fin.append q.1 q.2)‖ ^ 2
      rfl

/-- The source lower-boundary constant controls the left spectator-family
norm through the left overlap vector. -/
theorem fnwLowerBoundaryConstant_mul_familyNorm_sq_le_leftOverlap [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLowerBoundaryConstant ρ hρ A (ℓ + m) * ‖Φ‖ ^ 2 ≤
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, norm_fnwLeftOverlapMap_sq]
  exact Finset.sum_le_sum fun μr _ =>
    fnwLowerBoundaryConstant_mul_norm_sq_le ρ hρ A (ℓ + m) (Φ.ofLp μr)

/-- The source lower-boundary constant controls the right spectator-family
norm through the right overlap vector. -/
theorem fnwLowerBoundaryConstant_mul_familyNorm_sq_le_rightOverlap [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLowerBoundaryConstant ρ hρ A (m + r) * ‖Ψ‖ ^ 2 ≤
      ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ ^ 2 := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, norm_fnwRightOverlapMap_sq]
  exact Finset.sum_le_sum fun μℓ _ =>
    fnwLowerBoundaryConstant_mul_norm_sq_le ρ hρ A (m + r) (Ψ.ofLp μℓ)

/-- The square root of the middle lower-boundary constant controls the left
spectator-family norm by the left physical overlap norm. -/
theorem sqrt_fnwLowerBoundaryConstant_mul_familyNorm_le_leftOverlap [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    Real.sqrt (fnwLowerBoundaryConstant ρ hρ A m) * ‖Φ‖ ≤
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let c := fnwLowerBoundaryConstant ρ hρ A m
  have hc : c * ‖Φ‖ ^ 2 ≤ ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (fnwLowerBoundaryConstant_mono ρ hρ A hρfix (Nat.le_add_left m ℓ))
      (sq_nonneg ‖Φ‖)).trans
        (fnwLowerBoundaryConstant_mul_familyNorm_sq_le_leftOverlap
          ρ hρ A ℓ m r Φ)
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg Φ))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hminus.le]
  exact hc

/-- The square root of the middle lower-boundary constant controls the right
spectator-family norm by the right physical overlap norm. -/
theorem sqrt_fnwLowerBoundaryConstant_mul_familyNorm_le_rightOverlap [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    Real.sqrt (fnwLowerBoundaryConstant ρ hρ A m) * ‖Ψ‖ ≤
      ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let c := fnwLowerBoundaryConstant ρ hρ A m
  have hc : c * ‖Ψ‖ ^ 2 ≤ ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (fnwLowerBoundaryConstant_mono ρ hρ A hρfix (Nat.le_add_right m r))
      (sq_nonneg ‖Ψ‖)).trans
        (fnwLowerBoundaryConstant_mul_familyNorm_sq_le_rightOverlap
          ρ hρ A ℓ m r Ψ)
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg Ψ))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hminus.le]
  exact hc

/-- Monotonicity of the lower-boundary constant converts both spectator
family norms into the two physical overlap norms at the common middle length. -/
theorem fnwLowerBoundaryConstant_mul_familyNorms_le_overlapNorms [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (A : MPSTensor d D)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    fnwLowerBoundaryConstant ρ hρ A m * ‖Φ‖ * ‖Ψ‖ ≤
      ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let c := fnwLowerBoundaryConstant ρ hρ A m
  have hsqrt : Real.sqrt c ^ 2 = c := Real.sq_sqrt hminus.le
  have hleft : Real.sqrt c * ‖Φ‖ ≤ ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ :=
    sqrt_fnwLowerBoundaryConstant_mul_familyNorm_le_leftOverlap
      ρ hρ A hρfix ℓ m r Φ hminus
  have hright : Real.sqrt c * ‖Ψ‖ ≤ ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ :=
    sqrt_fnwLowerBoundaryConstant_mul_familyNorm_le_rightOverlap
      ρ hρ A hρfix ℓ m r Ψ hminus
  calc
    c * ‖Φ‖ * ‖Ψ‖ = Real.sqrt c ^ 2 * ‖Φ‖ * ‖Ψ‖ := by rw [hsqrt]
    _ = (Real.sqrt c * ‖Φ‖) * (Real.sqrt c * ‖Ψ‖) := by ring
    _ ≤ ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ :=
      mul_le_mul hleft hright
        (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg Ψ)) (norm_nonneg _)

/-- The linear numerator estimate after the two spectator-family norm
identities are inserted. The two factors remain the genuine rho-weighted
\(\ell^2\) family norms. -/
theorem norm_inner_overlap_sub_inner_aggregates_le_familyNorms [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ)) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      fnwMixingQuantity ρ hρ A htr m * ‖Φ‖ * ‖Ψ‖ := by
  let : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ Mat :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  let : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  have h := norm_inner_overlap_sub_inner_aggregates_le ρ hρ htr A ℓ m r Φ Ψ
  rw [sum_norm_sq_fnwLeftMiddleBoundary ρ hρ A hA ℓ r Φ,
    sum_norm_sq_fnwRightMiddleBoundary ρ hρ A hρfix ℓ r Ψ,
    Real.sqrt_sq (norm_nonneg Φ), Real.sqrt_sq (norm_nonneg Ψ)] at h
  simpa only [mul_assoc] using h

/-- FNW 1992, equation (6.5). The middle-block overlap defect carries exactly
the linear coefficient \(a(m)/a_-(m)\). Positivity of the actual source
lower-boundary constant is assumed directly, without replacing it by
\(1-a(m)\) or assuming \(a(m)<1\). -/
theorem norm_inner_overlap_sub_inner_aggregates_le_div_lowerBoundary [NeZero D]
    (ρ : Mat) (hρ : ρ.PosDef) (htr : Matrix.trace ρ = 1)
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (hρfix : Kraus.transferMap A ρ = ρ) (ℓ m r : ℕ)
    (Φ : FNWBoundaryFamilySpace (D := D) (Cfg d r))
    (Ψ : FNWBoundaryFamilySpace (D := D) (Cfg d ℓ))
    (hminus : 0 < fnwLowerBoundaryConstant ρ hρ A m) :
    letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup Mat :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ Mat :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤
      (fnwMixingQuantity ρ hρ A htr m /
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
  have ha : 0 ≤ a := by
    exact mul_nonneg (fnwTraceInverseFactor_pos hρ).le (norm_nonneg _)
  have hc : c ≠ 0 := ne_of_gt hminus
  have hfamilies := fnwLowerBoundaryConstant_mul_familyNorms_le_overlapNorms
    ρ hρ A hρfix ℓ m r Φ Ψ hminus
  calc
    ‖inner ℂ (fnwLeftOverlapMap ρ hρ A ℓ m r Φ)
          (fnwRightOverlapMap ρ hρ A ℓ m r Ψ) -
        inner ℂ (fnwLeftOverlapAggregate ρ A r Φ)
          (fnwRightOverlapAggregate A ℓ Ψ)‖ ≤ a * ‖Φ‖ * ‖Ψ‖ :=
      norm_inner_overlap_sub_inner_aggregates_le_familyNorms
        ρ hρ htr A hA hρfix ℓ m r Φ Ψ
    _ = (a / c) * (c * ‖Φ‖ * ‖Ψ‖) := by
      calc
        a * ‖Φ‖ * ‖Ψ‖ = ((a / c) * c) * ‖Φ‖ * ‖Ψ‖ := by
          rw [div_mul_cancel₀ a hc]
        _ = (a / c) * (c * ‖Φ‖ * ‖Ψ‖) := by ring
    _ ≤ (a / c) *
        (‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
          ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖) :=
      mul_le_mul_of_nonneg_left hfamilies (div_nonneg ha hminus.le)
    _ = (a / c) * ‖fnwLeftOverlapMap ρ hρ A ℓ m r Φ‖ *
        ‖fnwRightOverlapMap ρ hρ A ℓ m r Ψ‖ := by ring


end

end MPSTensor
