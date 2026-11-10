/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum

/-!
# Restriction of compressed observables to the actual ground eigenspace

These are the restriction identities in Hastings, arXiv:cond-mat/0508554v3,
lines 1562–1601 and 1678–1708. No basis or conditioning hypothesis is needed.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

local instance (H : Matrix ν ν ℂ) (E₀ : ℝ) : CompleteSpace (groundEigenspace H E₀) :=
  FiniteDimensional.complete ℂ (groundEigenspace H E₀)

/-- The compression `P W P`, acting on the ground eigenspace itself. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708. -/
noncomputable def groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀ :=
  ((groundCompression H E₀ W).codRestrict (groundEigenspace H E₀)
    (fun _ => (groundEigenspace H E₀).starProjection_apply_mem _)).comp
      (groundEigenspace H E₀).subtypeL

@[simp]
theorem coe_groundSpaceCompression_apply (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ)
    (x : groundEigenspace H E₀) :
    (groundSpaceCompression H E₀ W x : EuclideanSpace ℂ ν) = groundCompression H E₀ W x := rfl

theorem isSelfAdjoint_groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ)
    {W : Matrix ν ν ℂ} (hW : W.IsHermitian) : IsSelfAdjoint (groundSpaceCompression H E₀ W) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact (isSelfAdjoint_groundCompression H E₀ hW).isSymmetric x.val y.val

/-- The norm of a ground-space compression does not exceed the original term norm.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708. -/
theorem norm_groundSpaceCompression_le (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W‖ ≤ ‖W‖ := by
  refine (show ‖groundSpaceCompression H E₀ W‖ ≤ ‖groundCompression H E₀ W‖ from ?_).trans
    (norm_groundCompression_le H E₀ W)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    (groundCompression H E₀ W).le_opNorm x.val

/-- Restriction to the ground space does not increase the norm of the commutator.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1683–1708. -/
theorem norm_groundSpaceCompression_commutator_le (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W‖ ≤
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  exact (groundCompression H E₀ W * groundCompression H E₀ B -
    groundCompression H E₀ B * groundCompression H E₀ W).le_opNorm x.val

/-- The ambient compression has exactly the operator norm of its restriction to the
actual ground eigenspace. Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601. -/
theorem norm_groundSpaceCompression_eq (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W‖ = ‖groundCompression H E₀ W‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦
      (groundCompression H E₀ W).le_opNorm x.val
  · refine ContinuousLinearMap.opNorm_le_bound (groundCompression H E₀ W)
      (norm_nonneg (groundSpaceCompression H E₀ W)) ?_
    intro x
    let y : groundEigenspace H E₀ :=
      ⟨(groundEigenspace H E₀).starProjection x,
        (groundEigenspace H E₀).starProjection_apply_mem x⟩
    have hCx : groundCompression H E₀ W x =
        (groundSpaceCompression H E₀ W y : EuclideanSpace ℂ ν) := by
      have hp : (groundEigenspace H E₀).starProjection
          ((groundEigenspace H E₀).starProjection x) =
          (groundEigenspace H E₀).starProjection x :=
        (groundEigenspace H E₀).starProjection_eq_self_iff.mpr
          ((groundEigenspace H E₀).starProjection_apply_mem x)
      simp only [y, coe_groundSpaceCompression_apply, groundCompression,
        mul_apply_eq_comp, hp]
    rw [hCx]
    exact ((groundSpaceCompression H E₀ W).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left
        ((groundEigenspace H E₀).norm_starProjection_apply_le x)
        (norm_nonneg (groundSpaceCompression H E₀ W)))

/-- Restricting a compressed commutator to the ground eigenspace preserves its norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601 and 1644–1654. -/
theorem norm_groundSpaceCompression_commutator_eq (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W‖ =
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ := by
  apply le_antisymm (norm_groundSpaceCompression_commutator_le H E₀ W B)
  refine ContinuousLinearMap.opNorm_le_bound
    (groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W)
    (norm_nonneg (groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
      groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W)) ?_
  intro x
  let y : groundEigenspace H E₀ :=
    ⟨(groundEigenspace H E₀).starProjection x,
      (groundEigenspace H E₀).starProjection_apply_mem x⟩
  have hp : (groundEigenspace H E₀).starProjection
      ((groundEigenspace H E₀).starProjection x) =
      (groundEigenspace H E₀).starProjection x :=
    (groundEigenspace H E₀).starProjection_eq_self_iff.mpr
      ((groundEigenspace H E₀).starProjection_apply_mem x)
  have hCx : (groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W) x =
      ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W) y :
          EuclideanSpace ℂ ν) := by
    simp only [_root_.sub_apply, mul_apply_eq_comp, Submodule.coe_sub,
      coe_groundSpaceCompression_apply, y, groundCompression, hp]
  rw [hCx]
  exact ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
    groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left ((groundEigenspace H E₀).norm_starProjection_apply_le x)
        (norm_nonneg (groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
          groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W)))

end TNLean.Lattice
