/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Complex.Basic

/-!
# Conjugation and reflection parities

The two sign morphisms in the SPT classification are different: time reversal
conjugates scalar phases, while time reversal **or** reflection conjugates the
virtual projective action. This file supplies their elementary matrix actions.

Source: arXiv:2011.12127, Section III.A, `Papers/2011.12127/TN-Review-main.tex`
lines 1120–1130. Parities are the existing group `Multiplicative (ZMod 2)`;
its identity means no conjugation or reflection.
-/

open scoped Matrix

namespace TNLean.Algebra

/-- The order-two group recording the presence of time reversal or reflection.
Parity notation for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1114. -/
abbrev SymmetryParity := Multiplicative (ZMod 2)

/-- The nontrivial symmetry parity.
Parity notation for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1114. -/
def oddParity : SymmetryParity := Multiplicative.ofAdd 1

/-- A parity is either trivial or nontrivial.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1114. -/
theorem symmetryParity_cases (p : SymmetryParity) : p = 1 ∨ p = oddParity := by
  revert p
  decide

/-- The nontrivial parity squares to the identity.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1114. -/
@[simp] theorem oddParity_mul_self : oddParity * oddParity = 1 := by decide

/-- The nontrivial parity is distinct from the identity.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, line 1114. -/
@[simp] theorem oddParity_ne_one : oddParity ≠ 1 := by decide

/-- The identity or complex conjugation, according to the supplied parity.
Scalar and matrix form of the conjugation in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
noncomputable def parityConj (p : SymmetryParity) : ℂ ≃+* ℂ :=
  if p = 1 then RingEquiv.refl ℂ else starRingAut

/-- Trivial parity fixes complex scalars.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConj_one (z : ℂ) : parityConj 1 z = z := by
  simp [parityConj]

/-- Odd parity conjugates complex scalars.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConj_odd (z : ℂ) : parityConj oddParity z = star z := by
  simp [parityConj]

/-- Composing conjugations multiplies their parities.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem parityConj_mul (p q : SymmetryParity) (z : ℂ) :
    parityConj (p * q) z = parityConj p (parityConj q z) := by
  rcases symmetryParity_cases p with rfl | rfl <;>
    rcases symmetryParity_cases q with rfl | rfl <;> simp

/-- Applying the same scalar conjugation twice is the identity.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConj_self (p : SymmetryParity) (z : ℂ) :
    parityConj p (parityConj p z) = z := by
  rcases symmetryParity_cases p with rfl | rfl <;> simp

/-- Entrywise complex conjugation with the supplied parity.
Scalar and matrix form of the conjugation in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
noncomputable def parityConjMatrix {m n : Type*} (p : SymmetryParity)
    (M : Matrix m n ℂ) : Matrix m n ℂ := M.map (parityConj p)

/-- The parity conjugation acts entrywise on a matrix.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConjMatrix_apply {m n : Type*} (p : SymmetryParity)
    (M : Matrix m n ℂ) (i j) : parityConjMatrix p M i j = parityConj p (M i j) := rfl

/-- Trivial parity fixes a matrix.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConjMatrix_one {m n : Type*} (M : Matrix m n ℂ) :
    parityConjMatrix 1 M = M := by ext; simp

/-- Applying the same matrix conjugation twice is the identity.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConjMatrix_self {m n : Type*} (p : SymmetryParity)
    (M : Matrix m n ℂ) : parityConjMatrix p (parityConjMatrix p M) = M := by
  ext; simp

/-- Odd parity conjugates every matrix entry.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConjMatrix_odd {m n : Type*} (M : Matrix m n ℂ) :
    parityConjMatrix oddParity M = M.map star := by ext; simp

/-- Matrix conjugation respects matrix multiplication.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem parityConjMatrix_mul {m n k : Type*} [Fintype n] (p : SymmetryParity)
    (M : Matrix m n ℂ) (N : Matrix n k ℂ) :
    parityConjMatrix p (M * N) = parityConjMatrix p M * parityConjMatrix p N := by
  ext i j
  simp [parityConjMatrix_apply, Matrix.mul_apply, map_sum, map_mul]

/-- Scalar multiplication is conjugate-linear precisely at odd parity.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem parityConjMatrix_smul {m n : Type*} (p : SymmetryParity)
    (z : ℂ) (M : Matrix m n ℂ) :
    parityConjMatrix p (z • M) = parityConj p z • parityConjMatrix p M := by
  ext; simp [Matrix.smul_apply, map_mul]

/-- Entrywise conjugation commutes with finite sums.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem parityConjMatrix_sum {m n ι : Type*} (p : SymmetryParity)
    (s : Finset ι) (M : ι → Matrix m n ℂ) :
    parityConjMatrix p (∑ i ∈ s, M i) = ∑ i ∈ s, parityConjMatrix p (M i) := by
  ext; simp [Matrix.sum_apply, map_sum]

/-- Entrywise conjugations compose according to the parity group.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem parityConjMatrix_comp {m n : Type*} (p q : SymmetryParity)
    (M : Matrix m n ℂ) :
    parityConjMatrix p (parityConjMatrix q M) = parityConjMatrix (p * q) M := by
  ext; simp [parityConj_mul]

/-- Entrywise parity conjugation commutes with transpose.
Supporting algebra for arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem parityConjMatrix_transpose {m n : Type*} (p : SymmetryParity)
    (M : Matrix m n ℂ) : parityConjMatrix p Mᵀ = (parityConjMatrix p M)ᵀ := rfl

/-- Time reversal conjugates letters; reflection also transposes them.
Algebraic form of the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
noncomputable def symmetryLetter {n : Type*} (t r : SymmetryParity)
    (M : Matrix n n ℂ) : Matrix n n ℂ :=
  if r = 1 then parityConjMatrix t M else (parityConjMatrix t M)ᵀ

/-- The trivial symmetry fixes each tensor letter.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem symmetryLetter_trivial {n : Type*} (M : Matrix n n ℂ) :
    symmetryLetter 1 1 M = M := by simp [symmetryLetter]

/-- Pure time reversal conjugates each tensor letter.
Algebraic form of the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem symmetryLetter_timeReversal {n : Type*} (M : Matrix n n ℂ) :
    symmetryLetter oddParity 1 M = M.map star := by ext; simp [symmetryLetter]

/-- Pure reflection transposes each tensor letter.
Algebraic form of the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem symmetryLetter_reflection {n : Type*} (M : Matrix n n ℂ) :
    symmetryLetter 1 oddParity M = Mᵀ := by simp [symmetryLetter]

/-- Simultaneous time reversal and reflection take the adjoint.
Algebraic form of the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem symmetryLetter_both {n : Type*} (M : Matrix n n ℂ) :
    symmetryLetter oddParity oddParity M = Mᴴ := by
  ext; simp [symmetryLetter, Matrix.conjTranspose_apply]

/-- The two commuting involutions compose by multiplying their parities.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem symmetryLetter_comp {n : Type*} (t r u s : SymmetryParity)
    (M : Matrix n n ℂ) :
    symmetryLetter t r (symmetryLetter u s M) = symmetryLetter (t * u) (r * s) M := by
  rcases symmetryParity_cases r with rfl | rfl <;>
    rcases symmetryParity_cases s with rfl | rfl <;>
      simp [symmetryLetter, parityConjMatrix_comp]

/-- Applying the same letter action twice is the identity.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem symmetryLetter_self {n : Type*} (t r : SymmetryParity)
    (M : Matrix n n ℂ) : symmetryLetter t r (symmetryLetter t r M) = M := by
  rcases symmetryParity_cases r with rfl | rfl <;>
    simp [symmetryLetter]

/-- Only time reversal conjugates a scalar phase; reflection leaves it unchanged.
Algebraic form of the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem symmetryLetter_smul {n : Type*} (t r : SymmetryParity)
    (z : ℂ) (M : Matrix n n ℂ) :
    symmetryLetter t r (z • M) = parityConj t z • symmetryLetter t r M := by
  simp only [symmetryLetter, parityConjMatrix_smul]
  split <;> simp_all [Matrix.transpose_smul]

/-- The letter action commutes with finite sums.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem symmetryLetter_sum {n ι : Type*} (t r : SymmetryParity)
    (s : Finset ι) (M : ι → Matrix n n ℂ) :
    symmetryLetter t r (∑ i ∈ s, M i) = ∑ i ∈ s, symmetryLetter t r (M i) := by
  simp only [symmetryLetter, parityConjMatrix_sum]
  split <;> simp_all [Matrix.transpose_sum]

/-- Reflection reverses the order of matrix multiplication.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem symmetryLetter_mul {n : Type*} [Fintype n] (t r : SymmetryParity)
    (M N : Matrix n n ℂ) :
    symmetryLetter t r (M * N) =
      if r = 1 then symmetryLetter t r M * symmetryLetter t r N
      else symmetryLetter t r N * symmetryLetter t r M := by
  simp only [symmetryLetter, parityConjMatrix_mul]
  split <;> simp_all [Matrix.transpose_mul]

/-- Every letter action fixes the identity matrix.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
@[simp] theorem symmetryLetter_one {n : Type*} [DecidableEq n]
    (t r : SymmetryParity) : symmetryLetter t r (1 : Matrix n n ℂ) = 1 := by
  have h : parityConjMatrix t (1 : Matrix n n ℂ) = 1 := by
    ext i j
    simp only [parityConjMatrix_apply, Matrix.one_apply]
    split <;> simp_all
  simp [symmetryLetter, h]

/-- On a chain, reflection reverses the order of sites as well as transposing
letters. This identity applies to the actual ordered matrix contraction.
Supporting algebra for the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem symmetryLetter_list_prod {n : Type*} [Fintype n] [DecidableEq n]
    (t r : SymmetryParity) (L : List (Matrix n n ℂ)) :
    symmetryLetter t r L.prod =
      (if r = 1 then L.map (symmetryLetter t r)
        else L.reverse.map (symmetryLetter t r)).prod := by
  induction L with
  | nil => simp
  | cons M L ih =>
    rw [List.prod_cons, symmetryLetter_mul, ih]
    split_ifs <;> simp_all [List.reverse_cons, List.prod_append]

/-- Reflection reverses both virtual factors. Together with time reversal this
conjugates the virtual matrix at parity `t*r`, rather than the phase parity `t`.
Algebraic form of the tensor action in arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex`, lines 1116–1120. -/
theorem symmetryLetter_conjugation {n : Type*} [Fintype n] (t r : SymmetryParity)
    (X M : Matrix n n ℂ) :
    symmetryLetter t r (Xᴴ * M * X) =
      (parityConjMatrix (t * r) X)ᴴ * symmetryLetter t r M *
        parityConjMatrix (t * r) X := by
  rcases symmetryParity_cases t with rfl | rfl <;>
    rcases symmetryParity_cases r with rfl | rfl <;>
      simp [symmetryLetter, parityConjMatrix_mul, Matrix.transpose_mul,
        Matrix.mul_assoc, Matrix.conjTranspose, Matrix.transpose_map, Matrix.map_map,
        Function.comp_def]

end TNLean.Algebra
