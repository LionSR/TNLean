/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.DiagonalDressing
import TNLean.MPS.Symmetry.MPOSymmetry.AnomalyObstruction

/-!
# Diagonal on-site twists of group matrix product operators

A group family can be multiplied by a diagonal on-site representation commuting with its
periodic operators. The resulting family is again an exact normal representation. Its bond
dimensions are unchanged: diagonal dressing rescales the doubled-index letters by nonzero
scalars. A state fixed by both representations is fixed by the combined family.

This construction applies to the combined controlled-Z and on-site Z symmetry of
arXiv:2502.20257, line 3970. It does not identify projective bond classes with physical phases.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPOTensor.GroupFamily

variable {G : Type*} [Group G] {d D : ℕ}

/-- The periodic diagonal operator associated with a diagonal on-site representation. -/
def onsiteDiagonal (χ : G →* (Fin d → ℂˣ)) (g : G) (N : ℕ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  Matrix.diagonal fun t ↦ ∏ k, (χ g (t k) : ℂ)

/-- The diagonal operators obey the group multiplication law at every length. -/
theorem onsiteDiagonal_mul (χ : G →* (Fin d → ℂˣ)) (g h : G) (N : ℕ) :
    onsiteDiagonal χ g N * onsiteDiagonal χ h N = onsiteDiagonal χ (g * h) N := by
  rw [onsiteDiagonal, onsiteDiagonal, Matrix.diagonal_mul_diagonal, onsiteDiagonal]
  congr 1
  funext t
  simp only [map_mul, Pi.mul_apply, Units.val_mul, Finset.prod_mul_distrib]

/-- Multiplication by a diagonal on-site representation, on the input leg of each tensor.
Source: arXiv:2502.20257, line 3970, for the combined controlled-Z symmetry. -/
def diagonalTwist (F : GroupFamily G d) (χ : G →* (Fin d → ℂˣ)) : GroupFamily G d where
  bondDim := F.bondDim
  bondDim_pos := F.bondDim_pos
  tensor g := (F.tensor g).mulDiagonal fun j ↦ (χ g j : ℂ)

/-- The twisted periodic operator is the product of the original and on-site operators. -/
theorem mpo_diagonalTwist (F : GroupFamily G d) (χ : G →* (Fin d → ℂˣ)) (g : G) (N : ℕ) :
    mpo ((F.diagonalTwist χ).tensor g) N = mpo (F.tensor g) N * onsiteDiagonal χ g N :=
  mpo_mulDiagonal _ _ _

/-- A commuting diagonal on-site twist preserves exact normal representations. -/
theorem IsNormalRepresentation.diagonalTwist {F : GroupFamily G d}
    (hF : F.IsNormalRepresentation) (χ : G →* (Fin d → ℂˣ))
    (hcomm : ∀ g h N, 0 < N → Commute (onsiteDiagonal χ g N) (mpo (F.tensor h) N)) :
    (F.diagonalTwist χ).IsNormalRepresentation where
  isNormal g := (isNormal_toMPSTensor_mulDiagonal_iff _ fun j ↦ (χ g j).ne_zero).2
    (hF.isNormal g)
  operator_mul g h N hN := by
    rw [mpo_diagonalTwist, mpo_diagonalTwist, mpo_diagonalTwist,
      (hcomm g h N hN).mul_mul_mul_comm, hF.operator_mul g h N hN,
      onsiteDiagonal_mul]

/-- A state fixed by the original family and its diagonal on-site twist is fixed by their
combined operators. The on-site condition is the amplitude identity for every configuration. -/
theorem fixesMPV_diagonalTwist {F : GroupFamily G d} (χ : G →* (Fin d → ℂˣ))
    {A : MPSTensor d D} (hF : ∀ g, FixesMPV (F.tensor g) A)
    (hχ : ∀ g N, 0 < N → ∀ t : Fin N → Fin d,
      (∏ k, (χ g (t k) : ℂ)) * MPSTensor.mpv A t = MPSTensor.mpv A t) :
    ∀ g, FixesMPV ((F.diagonalTwist χ).tensor g) A := by
  intro g N hN
  rw [mpo_diagonalTwist, ← Matrix.mulVec_mulVec]
  have hdiag : onsiteDiagonal χ g N *ᵥ (fun t ↦ MPSTensor.mpv A t) =
      fun t ↦ MPSTensor.mpv A t := by
    funext t
    exact (Matrix.mulVec_diagonal _ _ t).trans (hχ g N hN t)
  rw [hdiag, hF g N hN]

end MPOTensor.GroupFamily
