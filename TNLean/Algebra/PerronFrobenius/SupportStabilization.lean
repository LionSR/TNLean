/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Stabilization of the positive support of matrix powers

This file records an elementary aperiodicity criterion for finite
nonnegative matrices. If an irreducible matrix has the same positive support
at powers two and three, then its square is strictly positive.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem pow_add_apply_pos_of_pos {T : Matrix n n ℝ}
    (hT : ∀ i j, 0 ≤ T i j) {a b : ℕ} {i j k : n}
    (ha : 0 < (T ^ a) i k) (hb : 0 < (T ^ b) k j) :
    0 < (T ^ (a + b)) i j := by
  rw [pow_add, Matrix.mul_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun l _ ↦
    mul_nonneg (Matrix.pow_apply_nonneg hT a i l)
      (Matrix.pow_apply_nonneg hT b l j))).2
    ⟨k, Finset.mem_univ k, mul_pos ha hb⟩

private theorem pow_support_succ
    {T : Matrix n n ℝ} (hT : ∀ i j, 0 ≤ T i j) {m : ℕ}
    (hm : ∀ i j, 0 < (T ^ m) i j ↔ 0 < (T ^ (m + 1)) i j) :
    ∀ i j, 0 < (T ^ (m + 1)) i j ↔ 0 < (T ^ (m + 2)) i j := by
  intro i j
  rw [show T ^ (m + 1) = T ^ m * T by rw [pow_succ],
    show T ^ (m + 2) = T ^ (m + 1) * T by rw [show m + 2 = (m + 1) + 1 by omega,
      pow_succ], Matrix.mul_apply, Matrix.mul_apply]
  constructor
  · intro h
    obtain ⟨k, hk, hik⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg hT m i k) (hT k j))).1 h
    have hkj : 0 < T k j := pos_of_mul_pos_right hik
      (Matrix.pow_apply_nonneg hT m i k)
    exact (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
      mul_nonneg (Matrix.pow_apply_nonneg hT (m + 1) i k) (hT k j))).2
      ⟨k, hk, mul_pos ((hm i k).1 (pos_of_mul_pos_left hik (hT k j))) hkj⟩
  · intro h
    obtain ⟨k, hk, hik⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg hT (m + 1) i k) (hT k j))).1 h
    have hkj : 0 < T k j := pos_of_mul_pos_right hik
      (Matrix.pow_apply_nonneg hT (m + 1) i k)
    exact (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
      mul_nonneg (Matrix.pow_apply_nonneg hT m i k) (hT k j))).2
      ⟨k, hk, mul_pos ((hm i k).2 (pos_of_mul_pos_left hik (hT k j))) hkj⟩

/-- Let \(T\) be a finite irreducible nonnegative matrix. If \(T^2\) and
\(T^3\) have the same positive support, then every entry of \(T^2\) is
strictly positive.

Indeed, right multiplication by \(T\) propagates equality of consecutive
supports to all powers from the second onward. Irreducibility supplies a
positive path between each ordered pair; if this path has length one, append
a nonempty return path at its endpoint. The resulting path has length at
least two and may therefore be shortened, at the level of support, to length
two. -/
theorem IsIrreducible.pow_two_pos_of_pow_two_support_eq_pow_three_support
    {T : Matrix n n ℝ} (hT : IsIrreducible T)
    (hsupport : ∀ i j, 0 < (T ^ 2) i j ↔ 0 < (T ^ 3) i j) :
    ∀ i j, 0 < (T ^ 2) i j := by
  have hstep : ∀ m : ℕ, 2 ≤ m →
      ∀ i j, 0 < (T ^ m) i j ↔ 0 < (T ^ (m + 1)) i j := by
    intro m hm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction r with
    | zero =>
        simpa using hsupport
    | succ r ih =>
        simpa [Nat.add_assoc] using pow_support_succ hT.nonneg (ih (by omega))
  have hcollapse : ∀ m : ℕ, 2 ≤ m →
      ∀ i j, 0 < (T ^ m) i j → 0 < (T ^ 2) i j := by
    intro m hm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    intro i j hij
    induction r with
    | zero =>
        simpa using hij
    | succ r ih =>
        apply ih (by omega)
        exact (hstep (2 + r) (by omega) i j).2 (by simpa [Nat.add_assoc] using hij)
  have hexists : ∀ i j : n, ∃ m > 0, 0 < (T ^ m) i j :=
    (isIrreducible_iff_exists_pow_pos hT.nonneg).1 hT
  intro i j
  obtain ⟨m, hm, hij⟩ := hexists i j
  by_cases hmone : m = 1
  · obtain ⟨r, hr, hjj⟩ := hexists j j
    have hpath : 0 < (T ^ (m + r)) i j :=
      pow_add_apply_pos_of_pos hT.nonneg hij hjj
    exact hcollapse (m + r) (by omega) i j hpath
  · exact hcollapse m (by omega) i j hij

end Matrix
