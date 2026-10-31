/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Matrices in the cyclic quantum Wielandt example

The two letters are the cyclic shift `S` and `R = |1⟩⟨D-1|`, as in
arXiv:0909.5347, source `main.tex`, lines 691–700. The shift has period `D`,
and a sandwich `R S^k R` survives precisely for `k ≡ D-2 (mod D)`.
The letters define a completely positive map; they are not asserted to be
trace preserving.
-/

noncomputable section

open scoped Matrix BigOperators Fin.NatCast

namespace MPSTensor.CyclicWielandt

variable {D : ℕ} [NeZero D]

/-- The cyclic shift in arXiv:0909.5347, example at source lines 691–700. -/
def shift (D : ℕ) [NeZero D] : Matrix (Fin D) (Fin D) ℂ :=
  fun i j ↦ if i = j + 1 then 1 else 0

/-- The extra matrix unit in arXiv:0909.5347, source lines 691–700. -/
def jump (D : ℕ) [NeZero D] : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.single 1 ((D - 1 : ℕ) : Fin D) 1

/-- The binary Kraus family in arXiv:0909.5347, source lines 691–700. -/
def tensor (D : ℕ) [NeZero D] : MPSTensor 2 D := ![shift D, jump D]

@[simp] theorem tensor_zero : tensor D 0 = shift D := by simp [tensor]

@[simp] theorem tensor_one : tensor D 1 = jump D := by simp [tensor]

/-- Left multiplication by the cyclic shift translates the row coordinate.
Source: arXiv:0909.5347, source lines 691–700. -/
theorem shift_mul_apply (X : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (shift D * X) i j = X (i - 1) j := by
  have hoff (k : Fin D) : i = k + 1 ↔ i - 1 = k := (sub_eq_iff_eq_add).symm
  simp [shift, Matrix.mul_apply, ite_mul, hoff]

/-- The entries of every shift power. Source: arXiv:0909.5347, lines 691–700. -/
theorem shift_pow_apply (n : ℕ) (i j : Fin D) :
    (shift D ^ n) i j = if i = j + (n : Fin D) then 1 else 0 := by
  induction n generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
      rw [pow_succ', shift_mul_apply, ih]
      simp [Nat.cast_add, sub_eq_iff_eq_add, add_assoc]

/-- The cyclic shift has period `D`. Source: arXiv:0909.5347, lines 697–700. -/
@[simp] theorem shift_pow_dim : shift D ^ D = 1 := by
  ext i j
  simp [shift_pow_apply, Matrix.one_apply]

/-- Full turns give identity words. Source: arXiv:0909.5347, lines 697–700. -/
theorem shift_pow_mul_dim (m : ℕ) : shift D ^ (m * D) = 1 := by
  rw [Nat.mul_comm m D, pow_mul, shift_pow_dim, one_pow]

/-- Reduce a shift exponent modulo the dimension.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem shift_pow_mod (n : ℕ) : shift D ^ n = shift D ^ (n % D) := by
  calc
    shift D ^ n = shift D ^ (n % D + D * (n / D)) :=
      congrArg (fun t ↦ shift D ^ t) (Nat.mod_add_div n D).symm
    _ = shift D ^ (n % D) := by
      rw [pow_add, pow_mul, shift_pow_dim, one_pow, mul_one]

/-- The shift is invertible, with its `(D-1)`st power as inverse.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem shift_isUnit : IsUnit (shift D) := by
  refine ⟨⟨shift D, shift D ^ (D - 1), ?_, ?_⟩, rfl⟩
  · rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos D), shift_pow_dim]
  · rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos D), shift_pow_dim]

/-- Shift powers translate the row of a matrix unit.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem shift_pow_mul_single (n : ℕ) (i j : Fin D) (c : ℂ) :
    shift D ^ n * Matrix.single i j c = Matrix.single (i + (n : Fin D)) j c := by
  ext a b
  by_cases hjb : j = b <;>
    simp [Matrix.mul_apply, Matrix.single_apply, shift_pow_apply,
      mul_ite, ite_mul, eq_comm, hjb]

/-- Shift powers translate the column of a matrix unit in the opposite direction.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem single_mul_shift_pow (n : ℕ) (i j : Fin D) (c : ℂ) :
    Matrix.single i j c * shift D ^ n = Matrix.single i (j - (n : Fin D)) c := by
  ext a b
  have hcol : j = b + (n : Fin D) ↔ j - (n : Fin D) = b := (sub_eq_iff_eq_add).symm
  by_cases hia : i = a <;>
    simp [Matrix.mul_apply, Matrix.single_apply, shift_pow_apply,
      mul_ite, hcol, eq_comm, hia]

/-- The shift-jump-shift words are concrete matrix units.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem sandwich_eq_single (k l : ℕ) :
    shift D ^ k * jump D * shift D ^ l =
      Matrix.single (1 + (k : Fin D)) (((D - 1 : ℕ) : Fin D) - (l : Fin D)) 1 := by
  rw [jump, shift_pow_mul_single, single_mul_shift_pow]

/-- The last coordinate is one step after `D-2`.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem return_coordinate_iff (hD : 2 ≤ D) (k : ℕ) (hk : k < D) :
    (1 : Fin D) + (k : Fin D) = ((D - 1 : ℕ) : Fin D) ↔ k = D - 2 := by
  have h1 : (1 : Fin D).val = 1 := by
    change 1 % D = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.ext_iff, Fin.val_add_eq_ite]
  simp only [h1, Fin.val_natCast, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (show D - 1 < D by omega)]
  split_ifs <;> omega

/-- The cyclic successor of the last coordinate is zero.
Source: arXiv:0909.5347, source lines 691–700. -/
theorem one_add_last (hD : 2 ≤ D) :
    (1 : Fin D) + ((D - 1 : ℕ) : Fin D) = 0 := by
  calc
    (1 : Fin D) + ((D - 1 : ℕ) : Fin D) = ((1 + (D - 1) : ℕ) : Fin D) :=
      (Nat.cast_add 1 (D - 1)).symm
    _ = 0 := by rw [show 1 + (D - 1) = D by omega, Fin.natCast_self]

/-- The return relation, valid also in dimension two.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem jump_shift_pow_jump (hD : 2 ≤ D) (k : ℕ) (hk : k < D) :
    jump D * shift D ^ k * jump D = if k = D - 2 then jump D else 0 := by
  simp only [jump]
  rw [single_mul_shift_pow]
  by_cases h : k = D - 2
  · rw [ite_eq_left h]
    have hcoord : ((D - 1 : ℕ) : Fin D) - (k : Fin D) = 1 := by
      apply (sub_eq_iff_eq_add).2
      exact ((return_coordinate_iff hD k hk).2 h).symm
    rw [hcoord, Matrix.single_mul_single_same, one_mul]
  · rw [ite_eq_right h]
    apply Matrix.single_mul_single_of_ne
    intro hcoord
    apply h
    apply (return_coordinate_iff hD k hk).1
    exact ((sub_eq_iff_eq_add).1 hcoord).symm

/-- A return block may be inserted without changing the jump matrix.
Source: arXiv:0909.5347, source lines 697–700. -/
theorem jump_return (hD : 2 ≤ D) :
    jump D * shift D ^ (D - 2) * jump D = jump D := by
  simpa using jump_shift_pow_jump hD (D - 2) (by omega)

end MPSTensor.CyclicWielandt
