/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MatrixPolar
import TNLean.Algebra.CStarSqrtLipschitz
import QICLean.Analysis.MatrixFramePerturbation

/-!
# Phase-sensitive perturbation of polar frames

Let `V` be an injective column matrix and `W` an isometry on the same coordinate spaces.
The polar isometry of `V` is close to `W` when the Gram matrix `Vᴴ V` and the complex
cross matrix `Wᴴ V` are close to the identity. The cross matrix retains relative phases
between columns; bounds on absolute overlaps alone cannot imply this conclusion.

## Main results

* `Matrix.norm_polarPos_sub_one_le` bounds the positive polar factor by the Gram error.
* `Matrix.norm_polarIso_sub_isometry_le` compares the fixed polar frame with an isometry.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, discussion and outlook. The estimates
  here are finite-dimensional additions for coherent transport of complete sector spans;
  the paper does not state this operator-norm conclusion.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The positive factor of a rectangular matrix is within its Gram error of the identity.
The comparison uses the square-root Lipschitz bound at the identity. -/
theorem norm_polarPos_sub_one_le (V : Matrix m n ℂ) :
    ‖polarPos V - 1‖ ≤ ‖Vᴴ * V - 1‖ := by
  have h := CFC.norm_sqrt_sub_sqrt_le_div
    (Matrix.posSemidef_conjTranspose_mul_self V).nonneg (c := 1) zero_lt_one
    (b := (1 : Matrix n n ℂ)) (by simp)
  simpa only [polarPos, CFC.sqrt_one, Real.sqrt_one, div_one] using h

/-- The fixed polar isometry of an injective column matrix approximates an isometry with
error `sqrt(η + 2ζ) + η`, where `η` is the Gram error and `ζ` the complex cross error. -/
theorem norm_polarIso_sub_isometry_le (V : Matrix m n ℂ)
    (hV : Function.Injective V.mulVec) {W : Matrix m n ℂ} (hW : W.IsIsometry) :
    ‖polarIso V - W‖ ≤ Real.sqrt (‖Vᴴ * V - 1‖ + 2 * ‖Wᴴ * V - 1‖) +
      ‖Vᴴ * V - 1‖ := by
  have hF : ‖polarIso V‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one (isIsometry_polarIso_of_injective V hV)
  have hFV : ‖polarIso V - V‖ ≤ ‖Vᴴ * V - 1‖ := by
    calc
      ‖polarIso V - V‖ = ‖polarIso V * (1 - polarPos V)‖ := by
        rw [Matrix.mul_sub, Matrix.mul_one, polarIso_mul_polarPos]
      _ ≤ ‖polarIso V‖ * ‖1 - polarPos V‖ := l2_opNorm_mul _ _
      _ ≤ 1 * ‖1 - polarPos V‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ ≤ ‖Vᴴ * V - 1‖ := by rw [one_mul, norm_sub_rev]; exact norm_polarPos_sub_one_le V
  have hVW : ‖V - W‖ ≤ Real.sqrt (‖Vᴴ * V - 1‖ + 2 * ‖Wᴴ * V - 1‖) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (norm_sub_isometry_sq_le V hW)
  calc
    ‖polarIso V - W‖ ≤ ‖polarIso V - V‖ + ‖V - W‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

end Matrix
