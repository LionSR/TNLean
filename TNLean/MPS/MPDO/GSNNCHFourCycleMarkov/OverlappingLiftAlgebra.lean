/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.GSNNCHFourCycleMarkov.PositiveOverlappingProduct

/-!
# Algebra of overlapping matrix lifts

This file records the additive, support-annihilation, and
positivity properties of the natural lifts from two adjacent tensor factors to
three tensor factors. These lemmas isolate the matrix algebra used in the
four-cycle quantum Markov argument.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

variable {a b c : Type*}
variable [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

omit [DecidableEq b] in
/-- Orthogonal middle supports force the product of two overlapping operators
to vanish. -/
theorem overlappingLifts_mul_eq_zero_of_middle_mul_eq_zero
    (X : Matrix (a × b) (a × b) ℂ)
    (Y : Matrix (b × c) (b × c) ℂ)
    (P Q : Matrix b b ℂ)
    (hXP : X * ((1 : Matrix a a ℂ) ⊗ₖ P) = X)
    (hQY : (Q ⊗ₖ (1 : Matrix c c ℂ)) * Y = Y)
    (hPQ : P * Q = 0) :
    leftOverlappingLift X * rightOverlappingLift Y = 0 := by
  classical
  have hMiddle :
      leftOverlappingLift (c := c) ((1 : Matrix a a ℂ) ⊗ₖ P) *
          rightOverlappingLift (a := a)
            (Q ⊗ₖ (1 : Matrix c c ℂ)) = 0 := by
    rw [rightOverlappingLift_kronecker_one]
    change (((1 : Matrix a a ℂ) ⊗ₖ P) ⊗ₖ
        (1 : Matrix c c ℂ)) *
      (((1 : Matrix a a ℂ) ⊗ₖ Q) ⊗ₖ
        (1 : Matrix c c ℂ)) = 0
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPQ]
    simp
  calc
    leftOverlappingLift X * rightOverlappingLift Y =
        leftOverlappingLift (X * ((1 : Matrix a a ℂ) ⊗ₖ P)) *
          rightOverlappingLift
            ((Q ⊗ₖ (1 : Matrix c c ℂ)) * Y) := by rw [hXP, hQY]
    _ = (leftOverlappingLift X *
          leftOverlappingLift ((1 : Matrix a a ℂ) ⊗ₖ P)) *
        (rightOverlappingLift (Q ⊗ₖ (1 : Matrix c c ℂ)) *
          rightOverlappingLift Y) := by
      rw [← leftOverlappingLift_mul, ← rightOverlappingLift_mul]
    _ = leftOverlappingLift X *
        (leftOverlappingLift ((1 : Matrix a a ℂ) ⊗ₖ P) *
          rightOverlappingLift (Q ⊗ₖ (1 : Matrix c c ℂ))) *
        rightOverlappingLift Y := by simp only [mul_assoc]
    _ = 0 := by rw [hMiddle]; simp

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- The left overlapping lift preserves finite sums. -/
theorem leftOverlappingLift_sum {I : Type*} [Fintype I]
    (X : I → Matrix (a × b) (a × b) ℂ) :
    leftOverlappingLift (c := c) (∑ i, X i) =
      ∑ i, leftOverlappingLift (c := c) (X i) := by
  ext p q
  simp only [leftOverlappingLift, Matrix.sum_apply]
  rw [Finset.sum_mul]

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- The left overlapping lift preserves scalar multiplication. -/
theorem leftOverlappingLift_smul (z : ℂ)
    (X : Matrix (a × b) (a × b) ℂ) :
    leftOverlappingLift (c := c) (z • X) =
      z • leftOverlappingLift (c := c) X := by
  ext p q
  simp [leftOverlappingLift]
  ring

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] in
/-- The right overlapping lift preserves finite sums. -/
theorem rightOverlappingLift_sum {I : Type*} [Fintype I]
    (X : I → Matrix (b × c) (b × c) ℂ) :
    rightOverlappingLift (a := a) (∑ i, X i) =
      ∑ i, rightOverlappingLift (a := a) (X i) := by
  ext p q
  simp only [rightOverlappingLift, Matrix.sum_apply]
  rw [Finset.mul_sum]

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] in
/-- Positivity of a left overlapping lift implies positivity of the local
operator whenever the complementary factor has a basis element. -/
theorem posSemidef_of_leftOverlappingLift_posSemidef
    (X : Matrix (a × b) (a × b) ℂ) (k : c)
    (hX : (leftOverlappingLift (c := c) X).PosSemidef) : X.PosSemidef := by
  have hPrincipal := hX.submatrix (fun x : a × b ↦ (x, k))
  have hPrincipalEq :
      (leftOverlappingLift (c := c) X).submatrix
          (fun x : a × b ↦ (x, k)) (fun x : a × b ↦ (x, k)) = X := by
    ext p q
    change X p q * (1 : Matrix c c ℂ) k k = X p q
    simp
  rw [hPrincipalEq] at hPrincipal
  exact hPrincipal

omit [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] in
/-- Positivity of a right overlapping lift implies positivity of the local
operator whenever the complementary factor has a basis element. -/
theorem posSemidef_of_rightOverlappingLift_posSemidef
    (Y : Matrix (b × c) (b × c) ℂ) (i : a)
    (hY : (rightOverlappingLift (a := a) Y).PosSemidef) : Y.PosSemidef := by
  have hPrincipal := hY.submatrix (fun x : b × c ↦ ((i, x.1), x.2))
  have hPrincipalEq :
      (rightOverlappingLift (a := a) Y).submatrix
          (fun x : b × c ↦ ((i, x.1), x.2))
          (fun x : b × c ↦ ((i, x.1), x.2)) = Y := by
    ext p q
    change (1 : Matrix a a ℂ) i i * Y p q = Y p q
    simp
  rw [hPrincipalEq] at hPrincipal
  exact hPrincipal
end Matrix
