/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Reindex
import TNLean.MPS.MPU.Examples.ShiftSourceFormulas
import TNLean.MPS.MPU.StandardForm

/-!
# Blocked supplied source formulas for the cyclic-shift examples

This module inserts explicit evaluations of the auxiliary $Y_1$--$X_2$ and
$X_1$--$Y_2$ mixed kernels into algebraic open-leg factorizations of a two-site
block. These are not the source gates printed in CPSV17 equations `eq:uv2_U2`
and `eq:uv2_U3`.
-/

open scoped Matrix BigOperators

namespace MPOTensor

private theorem shiftExampleU₂_sourceY₁X₂_eq_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (lr : Fin ℓ[shiftExampleU₂ d] × Fin r[shiftExampleU₂ d])
    (ij : Fin (d * d) × Fin (d * d)) :
    SourceFactors.sourceY₁X₂ (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        lr ij =
      identitySwapIdentityMatrix d
        ((shiftExampleU₂SourceY₁X₂RowEquiv d).symm lr)
        ((shiftTwoSitePhysicalEquiv d).symm ij) := by
  have h := congrFun (congrFun
    (shiftExampleU₂_sourceY₁X₂_reindex_eq_identitySwapIdentity d)
    ((shiftExampleU₂SourceY₁X₂RowEquiv d).symm lr))
    ((shiftTwoSitePhysicalEquiv d).symm ij)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The auxiliary $Y_1$--$X_2$ kernel in the $U_2$ block evaluates to
$\Id\otimes\mathbb S\otimes\Id$ in the explicit four-spin order.
The statement retains the two open source-factor boundaries $X_1$ and $Y_2$.

Auxiliary mixed-kernel evaluation; not the CPSV17 standard-form gate. -/
theorem shiftExampleU₂_blockTwo_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₂ d) I J α γ =
      ∑ r : Fin r[shiftExampleU₂ d], ∑ l : Fin ℓ[shiftExampleU₂ d],
        (shiftExampleU₂SourceFactors d).X₁
            (α, (finProdFinEquiv.symm J).1) r *
          identitySwapIdentityMatrix d
            ((shiftExampleU₂SourceY₁X₂RowEquiv d).symm (l, r))
            ((shiftTwoSitePhysicalEquiv d).symm
              (finProdFinEquiv.symm I)) *
            (shiftExampleU₂SourceFactors d).Y₂ l
              ((finProdFinEquiv.symm J).2, γ) := by
  simpa only [shiftExampleU₂_sourceY₁X₂_eq_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂
      (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d) I J α γ

private theorem shiftExampleU₂_sourceX₁Y₂_eq_swapSwap_mul_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (ij : Fin (d * d) × Fin (d * d))
    (rl : Fin r[shiftExampleU₂ d] × Fin ℓ[shiftExampleU₂ d]) :
    SourceFactors.sourceX₁Y₂ (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        ij rl =
      (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
        ((shiftTwoSitePhysicalEquiv d).symm ij)
        ((shiftExampleU₂SourceX₁Y₂ColumnEquiv d).symm rl) := by
  have h := congrFun (congrFun
    (shiftExampleU₂_sourceX₁Y₂_reindex_eq_swapSwap_mul_identitySwapIdentity d)
    ((shiftTwoSitePhysicalEquiv d).symm ij))
    ((shiftExampleU₂SourceX₁Y₂ColumnEquiv d).symm rl)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The auxiliary $X_1$--$Y_2$ kernel in the reflected $U_2$ block evaluates to
$(\mathbb S\otimes\mathbb S)
(\Id\otimes\mathbb S\otimes\Id)$ in the explicit four-spin order.  The
statement retains the two open source-factor boundaries $X_2$ and $Y_1$.

Auxiliary mixed-kernel evaluation; not the CPSV17 standard-form gate. -/
theorem shiftExampleU₂_blockTwo_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₂ d) I J α γ =
      ∑ l : Fin ℓ[shiftExampleU₂ d], ∑ r : Fin r[shiftExampleU₂ d],
        (shiftExampleU₂SourceFactors d).X₂
            (α, (finProdFinEquiv.symm I).1) l *
          (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
            ((shiftTwoSitePhysicalEquiv d).symm
              ((finProdFinEquiv.symm J).2,
                (finProdFinEquiv.symm J).1))
            ((shiftExampleU₂SourceX₁Y₂ColumnEquiv d).symm (r, l)) *
            (shiftExampleU₂SourceFactors d).Y₁ r
              ((finProdFinEquiv.symm I).2, γ) := by
  simpa only [shiftExampleU₂_sourceX₁Y₂_eq_swapSwap_mul_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁
      (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d) I J α γ

private theorem shiftExampleU₃_sourceY₁X₂_eq_identitySwapIdentity_mul_swapSwap_apply
    (d : ℕ) [NeZero d]
    (lr : Fin ℓ[shiftExampleU₃ d] × Fin r[shiftExampleU₃ d])
    (ij : Fin (d * d) × Fin (d * d)) :
    SourceFactors.sourceY₁X₂ (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        lr ij =
      (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((shiftExampleU₃SourceY₁X₂RowEquiv d).symm lr)
        ((shiftTwoSitePhysicalEquiv d).symm ij) := by
  have h := congrFun (congrFun
    (shiftExampleU₃_sourceY₁X₂_reindex_eq_identitySwapIdentity_mul_swapSwap d)
    ((shiftExampleU₃SourceY₁X₂RowEquiv d).symm lr))
    ((shiftTwoSitePhysicalEquiv d).symm ij)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The auxiliary $Y_1$--$X_2$ kernel in the $U_3$ block evaluates to
$(\Id\otimes\mathbb S\otimes\Id)
(\mathbb S\otimes\mathbb S)$ in the explicit four-spin order.  The statement
retains the two open source-factor boundaries $X_1$ and $Y_2$.

Auxiliary mixed-kernel evaluation; not the CPSV17 standard-form gate. -/
theorem shiftExampleU₃_blockTwo_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₃ d) I J α γ =
      ∑ r : Fin r[shiftExampleU₃ d], ∑ l : Fin ℓ[shiftExampleU₃ d],
        (shiftExampleU₃SourceFactors d).X₁
            (α, (finProdFinEquiv.symm J).1) r *
          (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
            ((shiftExampleU₃SourceY₁X₂RowEquiv d).symm (l, r))
            ((shiftTwoSitePhysicalEquiv d).symm
              (finProdFinEquiv.symm I)) *
            (shiftExampleU₃SourceFactors d).Y₂ l
              ((finProdFinEquiv.symm J).2, γ) := by
  simpa only [shiftExampleU₃_sourceY₁X₂_eq_identitySwapIdentity_mul_swapSwap_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₁_mul_sourceY₁X₂_mul_Y₂
      (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d) I J α γ

private theorem shiftExampleU₃_sourceX₁Y₂_eq_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (ij : Fin (d * d) × Fin (d * d))
    (rl : Fin r[shiftExampleU₃ d] × Fin ℓ[shiftExampleU₃ d]) :
    SourceFactors.sourceX₁Y₂ (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        ij rl =
      identitySwapIdentityMatrix d
        ((shiftTwoSitePhysicalEquiv d).symm ij)
        ((shiftExampleU₃SourceX₁Y₂ColumnEquiv d).symm rl) := by
  have h := congrFun (congrFun
    (shiftExampleU₃_sourceX₁Y₂_reindex_eq_identitySwapIdentity d)
    ((shiftTwoSitePhysicalEquiv d).symm ij))
    ((shiftExampleU₃SourceX₁Y₂ColumnEquiv d).symm rl)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The auxiliary $X_1$--$Y_2$ kernel in the reflected $U_3$ block evaluates to
$\Id\otimes\mathbb S\otimes\Id$ in the explicit four-spin order.
The statement retains the two open source-factor boundaries $X_2$ and $Y_1$.

Auxiliary mixed-kernel evaluation; not the CPSV17 standard-form gate. -/
theorem shiftExampleU₃_blockTwo_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₃ d) I J α γ =
      ∑ l : Fin ℓ[shiftExampleU₃ d], ∑ r : Fin r[shiftExampleU₃ d],
        (shiftExampleU₃SourceFactors d).X₂
            (α, (finProdFinEquiv.symm I).1) l *
          identitySwapIdentityMatrix d
            ((shiftTwoSitePhysicalEquiv d).symm
              ((finProdFinEquiv.symm J).2,
                (finProdFinEquiv.symm J).1))
            ((shiftExampleU₃SourceX₁Y₂ColumnEquiv d).symm (r, l)) *
            (shiftExampleU₃SourceFactors d).Y₁ r
              ((finProdFinEquiv.symm I).2, γ) := by
  simpa only [shiftExampleU₃_sourceX₁Y₂_eq_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceX₁Y₂_reflected_mul_Y₁
      (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d) I J α γ

end MPOTensor
