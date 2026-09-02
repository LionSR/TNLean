/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Reindex
import TNLean.MPS.MPU.Examples.ShiftSourceGateFormulas
import TNLean.MPS.MPU.StandardForm

/-!
# Blocked supplied source formulas for the cyclic-shift examples

This module inserts the explicit shift gates into the two source-faithful
factorizations of a two-site block. The auxiliary $Y_1$--$X_2$ and
$X_1$--$Y_2$ mixed kernels do not occur in these formulas.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- The supplied $U_2$ source-$u$ gate in the paper's four-spin coordinates.

Source: CPSV17 equation `eq:uv2_U2`, lines 2018--2026. -/
private theorem shiftExampleU₂_sourceU_eq_scaled_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (lr : Fin ℓ[shiftExampleU₂ d] × Fin r[shiftExampleU₂ d])
    (ij : Fin (d * d) × Fin (d * d)) :
    SourceFactors.sourceU (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        lr ij =
      (d : ℂ) • identitySwapIdentityMatrix d
        ((shiftExampleU₂SourceURowEquiv d).symm lr)
        ((shiftTwoSitePhysicalEquiv d).symm ij) := by
  obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ :=
    (shiftExampleU₂SourceURowEquiv d).surjective lr
  obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ :=
    (shiftTwoSitePhysicalEquiv d).surjective ij
  simpa only [Equiv.symm_apply_apply] using
    shiftExampleU₂_sourceU_fourSpin_apply d a b c e i j k l

/-- The supplied $U_2$ source-$v$ gate in the paper's four-spin coordinates.

Source: CPSV17 equation `eq:uv2_U2`, lines 2018--2026. -/
private theorem shiftExampleU₂_sourceV_eq_inv_scaled_gate_apply
    (d : ℕ) [NeZero d]
    (ij : Fin (d * d) × Fin (d * d))
    (rl : Fin r[shiftExampleU₂ d] × Fin ℓ[shiftExampleU₂ d]) :
    SourceFactors.sourceV (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        ij rl =
      (d : ℂ)⁻¹ *
        (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
          ((shiftTwoSitePhysicalEquiv d).symm ij)
          ((shiftExampleU₂SourceVColumnEquiv d).symm rl) := by
  obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ :=
    (shiftTwoSitePhysicalEquiv d).surjective ij
  obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ :=
    (shiftExampleU₂SourceVColumnEquiv d).surjective rl
  let z := SourceFactors.sourceV (shiftExampleU₂ d)
    (shiftExampleU₂SourceFactors d)
    (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
    (shiftExampleU₂SourceVColumnEquiv d ((a, b), (c, e)))
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hgate := shiftExampleU₂_sourceV_fourSpin_apply d i j k l a b c e
  change z = _
  calc
    z = (d : ℂ)⁻¹ * ((d : ℂ) * z) :=
      (inv_mul_cancel_left₀ hd z).symm
    _ = _ := by
      simpa only [Equiv.symm_apply_apply] using
        congrArg (fun w ↦ (d : ℂ)⁻¹ * w) hgate

/-- The $U_2$ block factors through
$u_2^{(2)}=\Id\otimes\mathbb S\otimes\Id$ and the open $X_2,X_1$
boundaries. The factor $d$ records the identity-weight normalization of the
supplied factors.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₂ d) I J α γ =
      ∑ l : Fin ℓ[shiftExampleU₂ d], ∑ r : Fin r[shiftExampleU₂ d],
        (shiftExampleU₂SourceFactors d).X₂
            (α, (finProdFinEquiv.symm I).1) l *
          ((d : ℂ) • identitySwapIdentityMatrix d
            ((shiftExampleU₂SourceURowEquiv d).symm (l, r))
            ((shiftTwoSitePhysicalEquiv d).symm
              (finProdFinEquiv.symm J))) *
            (shiftExampleU₂SourceFactors d).X₁
              ((finProdFinEquiv.symm I).2, γ) r := by
  simpa only [shiftExampleU₂_sourceU_eq_scaled_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁
      (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d) I J α γ

/-- The reflected $U_2$ block factors through the balanced gate
$(\mathbb S\otimes\mathbb S)(\Id\otimes\mathbb S\otimes\Id)$ and the open
$Y_1,Y_2$ boundaries.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₂ d) I J α γ =
      ∑ r : Fin r[shiftExampleU₂ d], ∑ l : Fin ℓ[shiftExampleU₂ d],
        ((d : ℂ)⁻¹ *
          (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
            ((shiftTwoSitePhysicalEquiv d).symm
              (finProdFinEquiv.symm I))
            ((shiftExampleU₂SourceVColumnEquiv d).symm (r, l))) *
          (shiftExampleU₂SourceFactors d).Y₁ r
            (α, (finProdFinEquiv.symm J).1) *
            (shiftExampleU₂SourceFactors d).Y₂ l
              ((finProdFinEquiv.symm J).2, γ) := by
  simpa only [shiftExampleU₂_sourceV_eq_inv_scaled_gate_apply] using
    SourceFactors.blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂
      (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d) I J α γ

/-- The supplied $U_3$ source-$u$ gate in the paper's four-spin coordinates.

Source: CPSV17 equation `eq:uv2_U3`, lines 2028--2034. -/
private theorem shiftExampleU₃_sourceU_eq_scaled_gate_apply
    (d : ℕ) [NeZero d]
    (lr : Fin ℓ[shiftExampleU₃ d] × Fin r[shiftExampleU₃ d])
    (ij : Fin (d * d) × Fin (d * d)) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        lr ij =
      (d : ℂ) • (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((shiftExampleU₃SourceURowEquiv d).symm lr)
        ((shiftTwoSitePhysicalEquiv d).symm ij) := by
  obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ :=
    (shiftExampleU₃SourceURowEquiv d).surjective lr
  obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ :=
    (shiftTwoSitePhysicalEquiv d).surjective ij
  simpa only [Equiv.symm_apply_apply] using
    shiftExampleU₃_sourceU_fourSpin_apply d a b c e i j k l

/-- The supplied $U_3$ source-$v$ gate in the paper's four-spin coordinates.

Source: CPSV17 equation `eq:uv2_U3`, lines 2028--2034. -/
private theorem shiftExampleU₃_sourceV_eq_inv_scaled_identitySwapIdentity_apply
    (d : ℕ) [NeZero d]
    (ij : Fin (d * d) × Fin (d * d))
    (rl : Fin r[shiftExampleU₃ d] × Fin ℓ[shiftExampleU₃ d]) :
    SourceFactors.sourceV (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        ij rl =
      (d : ℂ)⁻¹ * identitySwapIdentityMatrix d
        ((shiftTwoSitePhysicalEquiv d).symm ij)
        ((shiftExampleU₃SourceVColumnEquiv d).symm rl) := by
  obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ :=
    (shiftTwoSitePhysicalEquiv d).surjective ij
  obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ :=
    (shiftExampleU₃SourceVColumnEquiv d).surjective rl
  let z := SourceFactors.sourceV (shiftExampleU₃ d)
    (shiftExampleU₃SourceFactors d)
    (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
    (shiftExampleU₃SourceVColumnEquiv d ((a, b), (c, e)))
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hgate := shiftExampleU₃_sourceV_fourSpin_apply d i j k l a b c e
  change z = _
  calc
    z = (d : ℂ)⁻¹ * ((d : ℂ) * z) :=
      (inv_mul_cancel_left₀ hd z).symm
    _ = _ := by
      simpa only [Equiv.symm_apply_apply] using
        congrArg (fun w ↦ (d : ℂ)⁻¹ * w) hgate

/-- The $U_3$ block factors through
$(\Id\otimes\mathbb S\otimes\Id)(\mathbb S\otimes\mathbb S)$ and the open
$X_2,X_1$ boundaries. The factor $d$ records the identity-weight normalization
of the supplied factors.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₃ d) I J α γ =
      ∑ l : Fin ℓ[shiftExampleU₃ d], ∑ r : Fin r[shiftExampleU₃ d],
        (shiftExampleU₃SourceFactors d).X₂
            (α, (finProdFinEquiv.symm I).1) l *
          ((d : ℂ) •
            (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
              ((shiftExampleU₃SourceURowEquiv d).symm (l, r))
              ((shiftTwoSitePhysicalEquiv d).symm
                (finProdFinEquiv.symm J))) *
            (shiftExampleU₃SourceFactors d).X₁
              ((finProdFinEquiv.symm I).2, γ) r := by
  simpa only [shiftExampleU₃_sourceU_eq_scaled_gate_apply] using
    SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁
      (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d) I J α γ

/-- The reflected $U_3$ block factors through the balanced gate
$\Id\otimes\mathbb S\otimes\Id$ and the open $Y_1,Y_2$ boundaries.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂
    (d : ℕ) [NeZero d] (I J : Fin ((d * d) * (d * d)))
    (α γ : Fin (d * d)) :
    blockTwo (shiftExampleU₃ d) I J α γ =
      ∑ r : Fin r[shiftExampleU₃ d], ∑ l : Fin ℓ[shiftExampleU₃ d],
        ((d : ℂ)⁻¹ * identitySwapIdentityMatrix d
          ((shiftTwoSitePhysicalEquiv d).symm
            (finProdFinEquiv.symm I))
          ((shiftExampleU₃SourceVColumnEquiv d).symm (r, l))) *
          (shiftExampleU₃SourceFactors d).Y₁ r
            (α, (finProdFinEquiv.symm J).1) *
            (shiftExampleU₃SourceFactors d).Y₂ l
              ((finProdFinEquiv.symm J).2, γ) := by
  simpa only [shiftExampleU₃_sourceV_eq_inv_scaled_identitySwapIdentity_apply] using
    SourceFactors.blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂
      (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d) I J α γ

end MPOTensor
