/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexOfRing

/-!
# Integer matrices over the complex numbers

The entrywise coercion of an integer matrix is the entrywise image along the canonical ring
homomorphism from the integers into the complex numbers. Its compatibilities with matrix
arithmetic are the instances at that homomorphism of the general statements of
`TNLean.Algebra.ComplexOfRing`, recorded here under the names the integer examples rewrite with,
two of them phrased through the integer cast.
-/

open scoped Matrix

namespace MPSTensor

/-! ### Entrywise coercion of integer matrices -/

/-- The entrywise coercion of an integer matrix into the complex matrices. -/
abbrev complexOfInt {m n : Type*} (X : Matrix m n ℤ) : Matrix m n ℂ :=
  complexOfRing (Int.castRingHom ℂ) X

@[simp] theorem complexOfInt_apply {m n : Type*} (X : Matrix m n ℤ) (i : m) (j : n) :
    complexOfInt X i j = (X i j : ℂ) := rfl

theorem complexOfInt_mul {m n o : Type*} [Fintype n] (X : Matrix m n ℤ) (Y : Matrix n o ℤ) :
    complexOfInt (X * Y) = complexOfInt X * complexOfInt Y :=
  complexOfRing_mul (Int.castRingHom ℂ) X Y

theorem complexOfInt_one {n : Type*} [DecidableEq n] :
    complexOfInt (1 : Matrix n n ℤ) = 1 :=
  complexOfRing_one (Int.castRingHom ℂ)

theorem complexOfInt_zero {m n : Type*} : complexOfInt (0 : Matrix m n ℤ) = 0 :=
  complexOfRing_zero (Int.castRingHom ℂ)

theorem complexOfInt_add {m n : Type*} (X Y : Matrix m n ℤ) :
    complexOfInt (X + Y) = complexOfInt X + complexOfInt Y :=
  complexOfRing_add (Int.castRingHom ℂ) X Y

theorem complexOfInt_neg {m n : Type*} (X : Matrix m n ℤ) :
    complexOfInt (-X) = -complexOfInt X :=
  complexOfRing_neg (Int.castRingHom ℂ) X

theorem complexOfInt_zsmul {m n : Type*} (c : ℤ) (X : Matrix m n ℤ) :
    complexOfInt (c • X) = (c : ℂ) • complexOfInt X :=
  complexOfRing_smul (Int.castRingHom ℂ) c X

theorem complexOfInt_sum {m n κ : Type*} (t : Finset κ) (f : κ → Matrix m n ℤ) :
    complexOfInt (∑ x ∈ t, f x) = ∑ x ∈ t, complexOfInt (f x) :=
  complexOfRing_sum (Int.castRingHom ℂ) t f

end MPSTensor
