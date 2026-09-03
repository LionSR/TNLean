/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftSourceFactors

/-!
# Supplied source gates for the cyclic-shift examples

This module evaluates the paper gates $u=Y_2Y_1$ and $v=X_1X_2$ for the three
shift families of arXiv:1703.09188. For the identity-weight tensor-product
witnesses, the gates differ from the paper-normalized permutation matrices by
reciprocal factors $d$ and $d^{-1}$; the entry theorems state and balance
those factors explicitly.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

/-- Four-spin row coordinates for the paper gate $u_2=Y_2\mathbin{-}Y_1$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
noncomputable def shiftExampleU₂SourceURowEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin ℓ[shiftExampleU₂ d] × Fin r[shiftExampleU₂ d]) :=
  Equiv.prodCongr (shiftExampleU₂LeftRankEquiv d)
    (shiftExampleU₂RightRankEquiv d)

/-- Four-spin column coordinates for the paper gate $v_2=X_1\mathbin{-}X_2$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
noncomputable def shiftExampleU₂SourceVColumnEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin r[shiftExampleU₂ d] × Fin ℓ[shiftExampleU₂ d]) :=
  Equiv.prodCongr (shiftExampleU₂RightRankEquiv d)
    (shiftExampleU₂LeftRankEquiv d)

/-- Entry formula for the unbalanced supplied $u_2$ gate. Dividing by $d$
gives the paper matrix $\Id\otimes\mathbb S\otimes\Id$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_sourceU_fourSpin_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        (shiftExampleU₂SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      (d : ℂ) • identitySwapIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [show shiftExampleU₂SourceURowEquiv d ((a, b), (c, e)) =
      (tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftLeftRankEquiv d (a, b), rightShiftLeftRankEquiv d 0),
        tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (c, e))) by rfl,
    show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl]
  calc
    _ = SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0) (i, k) *
        SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, e)) (j, l) := by
      simpa only [shiftExampleU₂, shiftExampleU₂SourceFactors] using
        SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
          (leftShiftSourceFactors d) (rightShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b)) (rightShiftLeftRankEquiv d 0)
          (leftShiftRightRankEquiv d 0) (rightShiftRightRankEquiv d (c, e)) i k j l
    _ = _ := by
      rw [sourceU_leftShiftSourceFactors_apply,
        sourceU_rightShiftSourceFactors_apply]
      by_cases ha : a = i <;> by_cases hb : b = k <;>
        by_cases hc : c = j <;> by_cases he : e = l <;>
        simp [identitySwapIdentityMatrix, ha, hb, hc, he]
      all_goals
        linear_combination (d : ℂ) * shiftSourceScale_cancel d

/-- Entry formula for the balanced paper gate
$v_2^{(2)}=(\mathbb S\otimes\mathbb S)
(\Id\otimes\mathbb S\otimes\Id)$.

The scalar $d$ balances the explicit tensor-product factor witness.
Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_sourceV_fourSpin_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    (d : ℂ) * SourceFactors.sourceV (shiftExampleU₂ d)
        (shiftExampleU₂SourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₂SourceVColumnEquiv d ((a, b), (c, e))) =
      (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
        ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl,
    show shiftExampleU₂SourceVColumnEquiv d ((a, b), (c, e)) =
      (tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (a, b)),
        tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftLeftRankEquiv d (c, e), rightShiftLeftRankEquiv d 0)) by rfl]
  calc
    _ = (d : ℂ) *
        (SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (i, k) (leftShiftRightRankEquiv d 0, leftShiftLeftRankEquiv d (c, e)) *
        SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (j, l) (rightShiftRightRankEquiv d (a, b), rightShiftLeftRankEquiv d 0)) := by
      congr 1
      simpa only [shiftExampleU₂, shiftExampleU₂SourceFactors] using
        SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
          (leftShiftSourceFactors d) (rightShiftSourceFactors d) i k j l
          (leftShiftRightRankEquiv d 0) (rightShiftRightRankEquiv d (a, b))
          (leftShiftLeftRankEquiv d (c, e)) (rightShiftLeftRankEquiv d 0)
    _ = _ := by
      rw [sourceV_leftShiftSourceFactors_apply,
        sourceV_rightShiftSourceFactors_apply]
      by_cases ha : a = j <;> by_cases hb : b = l <;>
        by_cases hc : c = i <;> by_cases he : e = k <;>
        simp_all only [mul_ite, ite_mul, zero_mul, mul_zero,
          swapTensorSwapMatrix_mul_identitySwapIdentityMatrix_apply]
      all_goals try grind
      all_goals
        simpa [mul_assoc] using shiftSourceScale_cancel d

/-- Four-spin row coordinates for the paper gate $u_3=Y_2\mathbin{-}Y_1$.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
noncomputable def shiftExampleU₃SourceURowEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin ℓ[shiftExampleU₃ d] × Fin r[shiftExampleU₃ d]) :=
  Equiv.prodCongr (shiftExampleU₃LeftRankEquiv d)
    (shiftExampleU₃RightRankEquiv d)

/-- Four-spin column coordinates for the paper gate $v_3=X_1\mathbin{-}X_2$.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
noncomputable def shiftExampleU₃SourceVColumnEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin r[shiftExampleU₃ d] × Fin ℓ[shiftExampleU₃ d]) :=
  Equiv.prodCongr (shiftExampleU₃RightRankEquiv d)
    (shiftExampleU₃LeftRankEquiv d)

/-- Entry formula for the unbalanced supplied $u_3$ gate. Dividing by $d$
gives the paper matrix
$(\Id\otimes\mathbb S\otimes\Id)(\mathbb S\otimes\mathbb S)$.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_sourceU_fourSpin_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (shiftExampleU₃SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      (d : ℂ) • (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [show shiftExampleU₃SourceURowEquiv d ((a, b), (c, e)) =
      (tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (a, b)),
        tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftRightRankEquiv d (c, e), leftShiftRightRankEquiv d 0)) by rfl,
    show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl]
  calc
    _ = SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, e)) (i, k) *
        SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0) (j, l) := by
      simpa only [shiftExampleU₃, shiftExampleU₃SourceFactors] using
        SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
          (rightShiftSourceFactors d) (leftShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0) (leftShiftLeftRankEquiv d (a, b))
          (rightShiftRightRankEquiv d (c, e)) (leftShiftRightRankEquiv d 0) i k j l
    _ = _ := by
      rw [sourceU_rightShiftSourceFactors_apply,
        sourceU_leftShiftSourceFactors_apply]
      by_cases ha : a = j <;> by_cases hb : b = l <;>
        by_cases hc : c = i <;> by_cases he : e = k <;>
        simp [ha, hb, hc, he]
      all_goals
        linear_combination (d : ℂ) * shiftSourceScale_cancel d

/-- Entry formula for the balanced paper gate
$v_3^{(2)}=\Id\otimes\mathbb S\otimes\Id$.

The scalar $d$ balances the explicit tensor-product factor witness.
Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_sourceV_fourSpin_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    (d : ℂ) * SourceFactors.sourceV (shiftExampleU₃ d)
        (shiftExampleU₃SourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₃SourceVColumnEquiv d ((a, b), (c, e))) =
      identitySwapIdentityMatrix d ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl,
    show shiftExampleU₃SourceVColumnEquiv d ((a, b), (c, e)) =
      (tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftRightRankEquiv d (a, b), leftShiftRightRankEquiv d 0),
        tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (c, e))) by rfl]
  calc
    _ = (d : ℂ) *
        (SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (i, k) (rightShiftRightRankEquiv d (a, b), rightShiftLeftRankEquiv d 0) *
        SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (j, l) (leftShiftRightRankEquiv d 0, leftShiftLeftRankEquiv d (c, e))) := by
      congr 1
      simpa only [shiftExampleU₃, shiftExampleU₃SourceFactors] using
        SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
          (rightShiftSourceFactors d) (leftShiftSourceFactors d) i k j l
          (rightShiftRightRankEquiv d (a, b)) (leftShiftRightRankEquiv d 0)
          (rightShiftLeftRankEquiv d 0) (leftShiftLeftRankEquiv d (c, e))
    _ = _ := by
      rw [sourceV_rightShiftSourceFactors_apply,
        sourceV_leftShiftSourceFactors_apply]
      by_cases ha : a = i <;> by_cases hb : b = k <;>
        by_cases hc : c = j <;> by_cases he : e = l <;>
        simp_all only [mul_ite, ite_mul, zero_mul, mul_zero,
          identitySwapIdentityMatrix_apply]
      all_goals try grind
      all_goals
        simpa [mul_assoc] using shiftSourceScale_cancel d

/-- Four-spin row coordinates for the paper gate $u_1=Y_2\mathbin{-}Y_1$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁SourceURowEquiv (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin ℓ[shiftExampleU₁ d] × Fin r[shiftExampleU₁ d]) :=
  Equiv.prodCongr (shiftExampleU₁LeftRankEquiv d)
    (shiftExampleU₁RightRankEquiv d)

/-- Four-spin column coordinates for the paper gate $v_1=X_1\mathbin{-}X_2$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁SourceVColumnEquiv (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin r[shiftExampleU₁ d] × Fin ℓ[shiftExampleU₁ d]) :=
  Equiv.prodCongr (shiftExampleU₁RightRankEquiv d)
    (shiftExampleU₁LeftRankEquiv d)

/-- Entry formula for $u_1=\Id\otimes\Id$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₁_sourceU_fourSpin_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₁ d) (shiftExampleU₁SourceFactors d)
        (shiftExampleU₁SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      identityTensorIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [show shiftExampleU₁SourceURowEquiv d ((a, b), (c, e)) =
      (tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityLeftRankEquiv d a, identityLeftRankEquiv d b),
        tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityRightRankEquiv d c, identityRightRankEquiv d e)) by rfl,
    show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl]
  calc
    _ = SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
          (identityLeftRankEquiv d a, identityRightRankEquiv d c) (i, k) *
        SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
          (identityLeftRankEquiv d b, identityRightRankEquiv d e) (j, l) := by
      simpa only [shiftExampleU₁, shiftExampleU₁SourceFactors] using
        SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
          (identitySourceFactors d) (identitySourceFactors d)
          (identityLeftRankEquiv d a) (identityLeftRankEquiv d b)
          (identityRightRankEquiv d c) (identityRightRankEquiv d e) i k j l
    _ = _ := by
      rw [sourceU_identitySourceFactors_apply,
        sourceU_identitySourceFactors_apply]
      by_cases ha : a = i <;> by_cases hb : b = j <;>
        by_cases hc : c = k <;> by_cases he : e = l <;>
        simp [identityTensorIdentityMatrix_apply, ha, hb, hc, he]

/-- Entry formula for $v_1=\Id\otimes\Id$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₁_sourceV_fourSpin_apply (d : ℕ)
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₁ d) (shiftExampleU₁SourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₁SourceVColumnEquiv d ((a, b), (c, e))) =
      identityTensorIdentityMatrix d ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl,
    show shiftExampleU₁SourceVColumnEquiv d ((a, b), (c, e)) =
      (tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityRightRankEquiv d a, identityRightRankEquiv d b),
        tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityLeftRankEquiv d c, identityLeftRankEquiv d e)) by rfl]
  calc
    _ = SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
          (i, k) (identityRightRankEquiv d a, identityLeftRankEquiv d c) *
        SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
          (j, l) (identityRightRankEquiv d b, identityLeftRankEquiv d e) := by
      simpa only [shiftExampleU₁, shiftExampleU₁SourceFactors] using
        SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
          (identitySourceFactors d) (identitySourceFactors d) i k j l
          (identityRightRankEquiv d a) (identityRightRankEquiv d b)
          (identityLeftRankEquiv d c) (identityLeftRankEquiv d e)
    _ = _ := by
      rw [sourceV_identitySourceFactors_apply,
        sourceV_identitySourceFactors_apply]
      by_cases ha : a = i <;> by_cases hb : b = j <;>
        by_cases hc : c = k <;> by_cases he : e = l <;>
        simp [identityTensorIdentityMatrix_apply, ha, hb, hc, he]
      all_goals grind

end MPOTensor
