/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Entrywise images of matrices over a ring embedded in the complex numbers

Worked examples of compression data are verified by deciding identities between matrices over a
commutative ring with decidable equality, and are transported to the complex matrices by applying
a ring homomorphism to each entry. This file records that transport once, for an arbitrary ring
homomorphism into the complex numbers: the entrywise image preserves matrix arithmetic, finite
sums, matrix units and submatrices, so that each example ring contributes only its own ring
homomorphism.

## Main definitions

* `MPSTensor.complexOfRing`: the entrywise image of a matrix along a ring homomorphism into the
  complex numbers.

## Main results

* `MPSTensor.complexOfRing_mul`, `MPSTensor.complexOfRing_one`: the entrywise image is
  multiplicative and preserves the identity matrix.
* `MPSTensor.complexOfRing_single`: the entrywise image of a matrix unit is the corresponding
  complex matrix unit.
-/

open scoped Matrix

namespace MPSTensor

variable {R : Type*} [CommRing R] (f : R →+* ℂ)

/-- The entrywise image of a matrix over `R` along a ring homomorphism `f : R →+* ℂ`. -/
def complexOfRing {m n : Type*} (X : Matrix m n R) : Matrix m n ℂ :=
  X.map f

@[simp] theorem complexOfRing_apply {m n : Type*} (X : Matrix m n R) (i : m) (j : n) :
    complexOfRing f X i j = f (X i j) := rfl

theorem complexOfRing_mul {m n o : Type*} [Fintype n] (X : Matrix m n R) (Y : Matrix n o R) :
    complexOfRing f (X * Y) = complexOfRing f X * complexOfRing f Y :=
  Matrix.map_mul

theorem complexOfRing_one {n : Type*} [DecidableEq n] :
    complexOfRing f (1 : Matrix n n R) = 1 :=
  Matrix.map_one f (map_zero f) (map_one f)

theorem complexOfRing_zero {m n : Type*} : complexOfRing f (0 : Matrix m n R) = 0 :=
  Matrix.map_zero f (map_zero f)

theorem complexOfRing_add {m n : Type*} (X Y : Matrix m n R) :
    complexOfRing f (X + Y) = complexOfRing f X + complexOfRing f Y :=
  Matrix.map_add f (map_add f) X Y

theorem complexOfRing_neg {m n : Type*} (X : Matrix m n R) :
    complexOfRing f (-X) = -complexOfRing f X :=
  Matrix.map_neg f (map_neg f) X

theorem complexOfRing_smul {m n : Type*} (c : R) (X : Matrix m n R) :
    complexOfRing f (c • X) = f c • complexOfRing f X :=
  Matrix.map_smulₛₗ f f c (fun a => map_mul f c a) X

theorem complexOfRing_sum {m n κ : Type*} (t : Finset κ) (g : κ → Matrix m n R) :
    complexOfRing f (∑ x ∈ t, g x) = ∑ x ∈ t, complexOfRing f (g x) :=
  map_sum (f.toAddMonoidHom.mapMatrix (m := m) (n := n)) g t

theorem complexOfRing_single {m n : Type*} [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    complexOfRing f (Matrix.single i j (1 : R)) = Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [complexOfRing_apply, Matrix.single_apply]
  split <;> simp

theorem complexOfRing_submatrix {m n m' n' : Type*} (X : Matrix m n R) (g : m' → m)
    (h : n' → n) : complexOfRing f (X.submatrix g h) = (complexOfRing f X).submatrix g h := rfl

end MPSTensor
