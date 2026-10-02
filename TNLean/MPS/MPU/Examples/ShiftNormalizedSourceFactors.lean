/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftSourceGateFormulas

/-!
# Trace-normalized source factors for the two counterpropagating shifts

Rescale the first cut by the one-spin dimension. Its weight becomes the
trace-one matrix on the product bond, while the second cut stays isometric.
Source: CPSV17, `Y1Y1X1X1`, lines 487--495, and `eq:uv2_U2`, `eq:uv2_U3`.
-/

open scoped Matrix

namespace MPOTensor

private noncomputable def normalizeProductShiftSourceFactors {p d : ℕ} [NeZero d]
    {U : MPOTensor p (d * d)} (S : SourceFactors U 1) :
    SourceFactors U (shiftPaperWeightSquared d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hw : sourceWeight (d := p) (shiftPaperWeightSquared d) =
      ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) •
        sourceWeight (d := p) (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) := by
    simp [shiftPaperWeightSquared, shiftPaperWeight, sourceWeight, Matrix.kronecker_smul]
  refine {
    X₁ := (d : ℂ) • S.X₁
    Y₁ := (d : ℂ)⁻¹ • S.Y₁
    Z₁ := (d : ℂ) • S.Z₁
    X₂ := S.X₂
    Y₂ := S.Y₂
    Z₂ := S.Z₂
    sourceCutM₁_eq := ?_
    sourceCutM₂_eq := S.sourceCutM₂_eq
    X₁_weighted_isometry := ?_
    X₂_isometry := S.X₂_isometry
    Y₁_mul_Z₁ := ?_
    Y₂_mul_Z₂ := S.Y₂_mul_Z₂
  }
  · simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd] using S.sourceCutM₁_eq
  · simp only [hw, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simpa [mul_assoc, hd] using S.X₁_weighted_isometry
  · simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd] using S.Y₁_mul_Z₁

private theorem normalized_sourceU {p d : ℕ} [NeZero d]
    {U : MPOTensor p (d * d)} (S : SourceFactors U 1) :
    SourceFactors.sourceU U (normalizeProductShiftSourceFactors S) =
      (d : ℂ)⁻¹ • SourceFactors.sourceU U S := by
  ext ⟨l, r⟩ ⟨i, j⟩
  simp [SourceFactors.sourceU, normalizeProductShiftSourceFactors,
    Finset.mul_sum, mul_assoc, mul_comm]

private theorem normalized_sourceV {p d : ℕ} [NeZero d]
    {U : MPOTensor p (d * d)} (S : SourceFactors U 1) :
    SourceFactors.sourceV U (normalizeProductShiftSourceFactors S) =
      (d : ℂ) • SourceFactors.sourceV U S := by
  ext ⟨i, j⟩ ⟨r, l⟩
  simp [SourceFactors.sourceV, normalizeProductShiftSourceFactors,
    Finset.mul_sum, mul_assoc]

/-- Trace-normalized source factors for the second shift family.
Source: CPSV17, `Erightleft`, `Y1Y1X1X1`, and `eq:uv2_U2`. -/
noncomputable def shiftExampleU₂PaperSourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (shiftExampleU₂ d) (shiftPaperWeightSquared d) :=
  normalizeProductShiftSourceFactors (shiftExampleU₂SourceFactors d)

/-- Trace-normalized source factors for the third shift family.
Source: CPSV17, `Erightleft`, `Y1Y1X1X1`, and `eq:uv2_U3`. -/
noncomputable def shiftExampleU₃PaperSourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (shiftExampleU₃ d) (shiftPaperWeightSquared d) :=
  normalizeProductShiftSourceFactors (shiftExampleU₃SourceFactors d)

/-- The trace-normalized first source gate is the printed four-spin permutation.
Source: CPSV17, equation `eq:uv2_U2`. -/
theorem shiftExampleU₂Paper_sourceU_fourSpin_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₂ d) (shiftExampleU₂PaperSourceFactors d)
        (shiftExampleU₂SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      identitySwapIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [shiftExampleU₂PaperSourceFactors, normalized_sourceU]
  change (d : ℂ)⁻¹ * _ = _
  rw [shiftExampleU₂_sourceU_fourSpin_apply]
  simp [smul_eq_mul, Nat.cast_ne_zero.mpr (NeZero.ne d)]

/-- The trace-normalized second source gate is the printed four-spin permutation.
Source: CPSV17, equation `eq:uv2_U2`. -/
theorem shiftExampleU₂Paper_sourceV_fourSpin_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₂ d) (shiftExampleU₂PaperSourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₂SourceVColumnEquiv d ((a, b), (c, e))) =
      (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
        ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [shiftExampleU₂PaperSourceFactors, normalized_sourceV]
  exact shiftExampleU₂_sourceV_fourSpin_apply d i j k l a b c e

/-- The trace-normalized first source gate is the printed four-spin permutation.
Source: CPSV17, equation `eq:uv2_U3`. -/
theorem shiftExampleU₃Paper_sourceU_fourSpin_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃PaperSourceFactors d)
        (shiftExampleU₃SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [shiftExampleU₃PaperSourceFactors, normalized_sourceU]
  change (d : ℂ)⁻¹ * _ = _
  rw [shiftExampleU₃_sourceU_fourSpin_apply]
  simp [smul_eq_mul, Nat.cast_ne_zero.mpr (NeZero.ne d)]

/-- The trace-normalized second source gate is the printed four-spin permutation.
Source: CPSV17, equation `eq:uv2_U3`. -/
theorem shiftExampleU₃Paper_sourceV_fourSpin_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₃ d) (shiftExampleU₃PaperSourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₃SourceVColumnEquiv d ((a, b), (c, e))) =
      identitySwapIdentityMatrix d ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [shiftExampleU₃PaperSourceFactors, normalized_sourceV]
  exact shiftExampleU₃_sourceV_fourSpin_apply d i j k l a b c e

end MPOTensor
