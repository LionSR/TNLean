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

This module inserts the explicit supplied source matrices of
`ShiftSourceFormulas` into the two open-leg factorizations of an actual
two-site block.  It thereby realizes the superscript `(2)` in
arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3` (lines 2018--2034),
through the paper's definition `SF` (lines 603--622).
-/

open scoped Matrix BigOperators

namespace MPOTensor

private theorem shiftExampleU₂_sourceU_eq_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (lr : Fin ℓ[shiftExampleU₂ d] × Fin r[shiftExampleU₂ d])
    (ij : Fin (d * d) × Fin (d * d)) :
    SourceFactors.sourceU (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        lr ij =
      identitySwapIdentityMatrix d
        ((shiftExampleU₂SourceURowEquiv d).symm lr)
        ((shiftTwoSitePhysicalEquiv d).symm ij) := by
  have h := congrFun (congrFun
    (shiftExampleU₂_sourceU_reindex_eq_identitySwapIdentity d)
    ((shiftExampleU₂SourceURowEquiv d).symm lr))
    ((shiftTwoSitePhysicalEquiv d).symm ij)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The supplied two-site block of $U_2$ has central gate
$u_2^{(2)}=\Id\otimes\mathbb S\otimes\Id$ in the paper's four-spin order.
The statement retains the two open source-factor boundaries $X_1$ and $Y_2$.

Source: arXiv:1703.09188, definition `SF` and equation `eq:uv2_U2`
(lines 603--622 and 2018--2026). -/
theorem shiftExampleU₂_blockTwo_apply_eq_sum_X₁_mul_u₂_two_mul_Y₂
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₂ d) I J α γ =
      ∑ r : Fin r[shiftExampleU₂ d], ∑ l : Fin ℓ[shiftExampleU₂ d],
        (shiftExampleU₂SourceFactors d).X₁
            (α, (finProdFinEquiv.symm J).1) r *
          identitySwapIdentityMatrix d
            ((shiftExampleU₂SourceURowEquiv d).symm (l, r))
            ((shiftTwoSitePhysicalEquiv d).symm
              (finProdFinEquiv.symm I)) *
            (shiftExampleU₂SourceFactors d).Y₂ l
              ((finProdFinEquiv.symm J).2, γ) := by
  simpa only [shiftExampleU₂_sourceU_eq_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₁_mul_sourceU_mul_Y₂
      (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d) I J α γ

private theorem shiftExampleU₂_sourceV_eq_swapSwap_mul_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (ij : Fin (d * d) × Fin (d * d))
    (rl : Fin r[shiftExampleU₂ d] × Fin ℓ[shiftExampleU₂ d]) :
    SourceFactors.sourceV (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        ij rl =
      (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
        ((shiftTwoSitePhysicalEquiv d).symm ij)
        ((shiftExampleU₂SourceVColumnEquiv d).symm rl) := by
  have h := congrFun (congrFun
    (shiftExampleU₂_sourceV_reindex_eq_swapSwap_mul_identitySwapIdentity d)
    ((shiftTwoSitePhysicalEquiv d).symm ij))
    ((shiftExampleU₂SourceVColumnEquiv d).symm rl)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The reflected supplied two-site block of $U_2$ has central gate
$v_2^{(2)}=(\mathbb S\otimes\mathbb S)
(\Id\otimes\mathbb S\otimes\Id)$ in the paper's four-spin order.  The
statement retains the two open source-factor boundaries $X_2$ and $Y_1$.

Source: arXiv:1703.09188, definition `SF` and equation `eq:uv2_U2`
(lines 603--622 and 2018--2026). -/
theorem shiftExampleU₂_blockTwo_apply_eq_sum_X₂_mul_v₂_two_reflected_mul_Y₁
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
            ((shiftExampleU₂SourceVColumnEquiv d).symm (r, l)) *
            (shiftExampleU₂SourceFactors d).Y₁ r
              ((finProdFinEquiv.symm I).2, γ) := by
  simpa only [shiftExampleU₂_sourceV_eq_swapSwap_mul_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceV_reflected_mul_Y₁
      (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d) I J α γ

private theorem shiftExampleU₃_sourceU_eq_identitySwapIdentity_mul_swapSwap_apply
    (d : ℕ) [NeZero d]
    (lr : Fin ℓ[shiftExampleU₃ d] × Fin r[shiftExampleU₃ d])
    (ij : Fin (d * d) × Fin (d * d)) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        lr ij =
      (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((shiftExampleU₃SourceURowEquiv d).symm lr)
        ((shiftTwoSitePhysicalEquiv d).symm ij) := by
  have h := congrFun (congrFun
    (shiftExampleU₃_sourceU_reindex_eq_identitySwapIdentity_mul_swapSwap d)
    ((shiftExampleU₃SourceURowEquiv d).symm lr))
    ((shiftTwoSitePhysicalEquiv d).symm ij)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The supplied two-site block of $U_3$ has central gate
$u_3^{(2)}=(\Id\otimes\mathbb S\otimes\Id)
(\mathbb S\otimes\mathbb S)$ in the paper's four-spin order.  The statement
retains the two open source-factor boundaries $X_1$ and $Y_2$.

Source: arXiv:1703.09188, definition `SF` and equation `eq:uv2_U3`
(lines 603--622 and 2028--2034). -/
theorem shiftExampleU₃_blockTwo_apply_eq_sum_X₁_mul_u₃_two_mul_Y₂
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₃ d) I J α γ =
      ∑ r : Fin r[shiftExampleU₃ d], ∑ l : Fin ℓ[shiftExampleU₃ d],
        (shiftExampleU₃SourceFactors d).X₁
            (α, (finProdFinEquiv.symm J).1) r *
          (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
            ((shiftExampleU₃SourceURowEquiv d).symm (l, r))
            ((shiftTwoSitePhysicalEquiv d).symm
              (finProdFinEquiv.symm I)) *
            (shiftExampleU₃SourceFactors d).Y₂ l
              ((finProdFinEquiv.symm J).2, γ) := by
  simpa only [shiftExampleU₃_sourceU_eq_identitySwapIdentity_mul_swapSwap_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₁_mul_sourceU_mul_Y₂
      (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d) I J α γ

private theorem shiftExampleU₃_sourceV_eq_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (ij : Fin (d * d) × Fin (d * d))
    (rl : Fin r[shiftExampleU₃ d] × Fin ℓ[shiftExampleU₃ d]) :
    SourceFactors.sourceV (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        ij rl =
      identitySwapIdentityMatrix d
        ((shiftTwoSitePhysicalEquiv d).symm ij)
        ((shiftExampleU₃SourceVColumnEquiv d).symm rl) := by
  have h := congrFun (congrFun
    (shiftExampleU₃_sourceV_reindex_eq_identitySwapIdentity d)
    ((shiftTwoSitePhysicalEquiv d).symm ij))
    ((shiftExampleU₃SourceVColumnEquiv d).symm rl)
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using h

/-- The reflected supplied two-site block of $U_3$ has central gate
$v_3^{(2)}=\Id\otimes\mathbb S\otimes\Id$ in the paper's four-spin order.
The statement retains the two open source-factor boundaries $X_2$ and $Y_1$.

Source: arXiv:1703.09188, definition `SF` and equation `eq:uv2_U3`
(lines 603--622 and 2028--2034). -/
theorem shiftExampleU₃_blockTwo_apply_eq_sum_X₂_mul_v₃_two_reflected_mul_Y₁
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
            ((shiftExampleU₃SourceVColumnEquiv d).symm (r, l)) *
            (shiftExampleU₃SourceFactors d).Y₁ r
              ((finProdFinEquiv.symm I).2, γ) := by
  simpa only [shiftExampleU₃_sourceV_eq_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceV_reflected_mul_Y₁
      (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d) I J α γ

end MPOTensor
