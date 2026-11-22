/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardForm.StandardFormInterpolation
import TNLean.MPS.Operator.Periodic.BondSimilarity
import TNLean.MPS.MPU.Symmetry.Phases.StandardFormPathContinuity

/-!
# Discarding the off-diagonal blocks of a block-triangular tensor

Grade the bond directions of an MPO tensor by levels `w : Fin D → ℕ`. The tensor is
*level-triangular* when every letter vanishes on the entries from a higher level to a lower one:
`W^{ij}_{βα} = 0` whenever `w β < w α`. Conjugating the bond by `diag(s^{w})` multiplies the entry
`(β, α)` by `s^{w β - w α}`. For `s ≠ 0` this is a bond gauge, so it leaves every periodic
operator unchanged. As `s → 0` it removes every entry between different levels and keeps the
level-diagonal blocks, so the limit has the same periodic operators by continuity.

This is the bond gauge behind the statement that only the diagonal blocks of a block-triangular
transfer structure contribute to traces of words, here realized as a path. It joins a
level-triangular tensor to its level-diagonal part through tensors with the same periodic
operators at every positive length. Combined with bond relabellings
(`joinedIn_sameMPOSet_bondReindex`), it is used to join an explicitly constructed tensor to the
padding of a smaller tensor with the same operators. Strict equivalence
(arXiv:1703.09188, Definition `def:strictly-equivalent-tensors`, lines 708--714) needs exactly
such a path at the endpoints.

## Main results

* `MPOTensor.levelScale`, `MPOTensor.levelDiag`, `MPOTensor.IsLevelTriangular`.
* `MPOTensor.mpo_levelScale`: the scaled tensor has the periodic operators of the tensor, for
  every `s`, including `s = 0`.
* `MPOTensor.joinedIn_sameMPOSet_levelDiag`: a level-triangular tensor is joined to its
  level-diagonal part through tensors with the same periodic operators.
* `MPOTensor.joinedIn_sameMPOSet_padBond_of_levelDiag_eq`: the same, when the level-diagonal part
  is the padding of a smaller tensor.
-/

open scoped Matrix
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- The tensor whose letters have the entry `(β, α)` multiplied by `s ^ (w β - w α)`. For a
level-triangular tensor and `s ≠ 0`, this is the conjugation of the bond by `diag(s^{w})`. -/
def levelScale (w : Fin D → ℕ) (s : ℂ) (W : MPOTensor d D) : MPOTensor d D :=
  fun i j β α => W i j β α * s ^ (w β - w α)

/-- The level-diagonal part of a tensor: the entries between bond directions of the same level. -/
def levelDiag (w : Fin D → ℕ) (W : MPOTensor d D) : MPOTensor d D :=
  fun i j β α => if w β = w α then W i j β α else 0

/-- A tensor is level-triangular when no letter has an entry from a higher level of the bond to a
lower one. -/
def IsLevelTriangular (w : Fin D → ℕ) (W : MPOTensor d D) : Prop :=
  ∀ i j β α, w β < w α → W i j β α = 0

theorem levelScale_one (w : Fin D → ℕ) (W : MPOTensor d D) : levelScale w 1 W = W := by
  funext i j
  ext β α
  simp [levelScale]

theorem levelScale_zero {w : Fin D → ℕ} {W : MPOTensor d D} (hW : IsLevelTriangular w W) :
    levelScale w 0 W = levelDiag w W := by
  funext i j
  ext β α
  simp only [levelScale, levelDiag]
  rcases lt_trichotomy (w β) (w α) with h | h | h
  · simp [hW i j β α h, h.ne]
  · simp [h]
  · simp [h.ne', Nat.sub_ne_zero_of_lt h]

theorem continuous_levelScale (w : Fin D → ℕ) (W : MPOTensor d D) :
    Continuous fun s : ℂ => levelScale w s W := by
  unfold levelScale
  fun_prop

/-- For `s ≠ 0` the scaled tensor is the conjugation of the bond by `diag(s^{w})`. -/
private theorem levelScale_eq_conj {w : Fin D → ℕ} {W : MPOTensor d D}
    (hW : IsLevelTriangular w W) {s : ℂ} (hs : s ≠ 0) (i j : Fin d) :
    Matrix.diagonal (fun β => s ^ w β) * W i j * Matrix.diagonal (fun β => s ^ w β)⁻¹ =
      levelScale w s W i j := by
  ext β α
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Pi.inv_apply, levelScale, Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rcases lt_or_ge (w β) (w α) with h | h
  · simp [hW i j β α h]
  · rw [pow_sub₀ _ hs h]
    ring

/-- **The scaled tensor has the same periodic operators.** For a level-triangular tensor this holds
for every scale `s`: for `s ≠ 0` by the bond gauge `diag(s^{w})`, and at `s = 0` by continuity. -/
theorem mpo_levelScale {w : Fin D → ℕ} {W : MPOTensor d D} (hW : IsLevelTriangular w W)
    (s : ℂ) (N : ℕ) : mpo (levelScale w s W) N = mpo W N := by
  have hne : ∀ s : ℂ, s ≠ 0 → mpo (levelScale w s W) N = mpo W N := fun s hs ↦
    (mpo_eq_of_diagonal_conj (fun β => s ^ w β) (fun β => pow_ne_zero _ hs)
      (levelScale_eq_conj hW hs) N).symm
  have hcont : Continuous fun s : ℂ => mpo (levelScale w s W) N :=
    (continuous_mpo N).comp (continuous_levelScale w W)
  have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont continuous_const
    (fun s hs ↦ hne s hs)
  exact congrFun this s

/-- **A level-triangular tensor is joined to its level-diagonal part** through tensors with the
same periodic operators at every positive length, along `t ↦` the tensor scaled by `1 - t`. -/
theorem joinedIn_sameMPOSet_levelDiag {w : Fin D → ℕ} {W : MPOTensor d D}
    (hW : IsLevelTriangular w W) :
    JoinedIn (SameMPOSet W) W (levelDiag w W) := by
  refine JoinedIn.ofLine (f := fun t : ℝ => levelScale w ((1 - t : ℝ) : ℂ) W)
    ((continuous_levelScale w W).comp
      (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id))).continuousOn
    ?_ ?_ ?_
  · simp [levelScale_one]
  · simp [levelScale_zero hW]
  · rintro _ ⟨t, -, rfl⟩ N -
    exact mpo_levelScale hW _ N

/-- A level-triangular tensor whose level-diagonal part is the padding of a smaller tensor `A` is
joined to that padding through tensors with the same periodic operators. -/
theorem joinedIn_sameMPOSet_padBond_of_levelDiag_eq {w : Fin D → ℕ} {W : MPOTensor d D}
    (hW : IsLevelTriangular w W) {E : ℕ} {A : MPOTensor d E} (hE : E ≤ D)
    (hA : levelDiag w W = padBond A D hE) :
    JoinedIn (SameMPOSet W) W (padBond A D hE) :=
  hA ▸ joinedIn_sameMPOSet_levelDiag hW

end MPOTensor
