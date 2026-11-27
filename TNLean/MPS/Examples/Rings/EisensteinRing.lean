/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Real.Sqrt
import TNLean.MPS.FundamentalTheorem.Compression.ExplicitGauge
import TNLean.MPS.Operator.Product.OperatorProduct
import QICLean.Algebra.Matrix.EisensteinInt

/-!
# The ring of Eisenstein integers

**Source.** None: this is infrastructure of this development for exact arithmetic in the
`ℤ/3` worked examples, and no paper states it.

**Formalized here.** The tensors of the `ℤ/3` matrix product operator symmetries have entries in
the cyclotomic field `ℚ(ω)`, where `ω = e^{2πi/3}` is a primitive cube root of unity and
satisfies `ω² + ω + 1 = 0`. The entries are in fact all integral: every one of them is a
`ℤ`-linear combination of `1` and `ω`, and so are the gauges and their inverses, which are
unimodular.

This file builds the exact arithmetic of that ring in two layers, following
`GoldenRing.lean`.

The computational layer is `EisensteinInt`, the ring `ℤ[ω]` presented by the two integer
coordinates of an element in the basis `1, ω`, with the multiplication obtained by reducing
`ω² = -1 - ω`. Equality of Eisenstein integers is decidable, so every matrix identity between
explicit matrices over `ℤ[ω]` is decidable, exactly as an identity between integer matrices is.
Mathlib's `Zsqrtd (-3)` is the ring `ℤ[√-3]`, a subring of index two in `ℤ[ω]` that does not
contain `ω` itself, so a dedicated structure is used.

The algebraic layer identifies those coordinates with the actual complex number
`ω = (-1 + i√3)/2`. The ring homomorphism `eisensteinToComplex` is the embedding along which a
matrix over `ℤ[ω]` becomes a complex matrix, and identities proved by decision over `ℤ[ω]`
transport to the complex matrices. The embedding is injective, so a nonzero Eisenstein integer
stays nonzero in `ℂ`; this is what allows a matrix unit scaled by `ω - 1` to be divided back.

## Main definitions

* `EisensteinInt`: the ring `ℤ[ω]` in coordinates.
* `EisensteinInt.omega`: the generator `ω`.
* `eisensteinOmega`: the complex number `(-1 + i√3)/2`.
* `eisensteinToComplex`: the embedding of `ℤ[ω]` into the complex numbers.
* `MPSTensor.complexOfEisenstein`: the entrywise image of a matrix over `ℤ[ω]` in the complex
  matrices.

## Main results

* `EisensteinInt.omega_quadratic`, `eisensteinOmega_quadratic`: the relation `ω² + ω + 1 = 0`
  in the two models.
* `eisensteinMulRule`: the multiplication rule of `ℤ[ω]` in any commutative ring carrying a root
  of `X² + X + 1`.
* `eisensteinToComplex_injective`, `MPSTensor.complexOfEisenstein_ne_zero`: the embedding is
  injective, on scalars, and nonzero matrices have nonzero images.
* `MPSTensor.complexOfEisenstein_mul`, `MPSTensor.complexOfEisenstein_one`: the embedding of
  matrices is multiplicative and unital.

Word evaluation and bond-space products over `ℤ[ω]` are the general `MPSTensor.evalWordR` and
`MPSTensor.mulTensorR`, transported by `MPSTensor.evalWord_complexOfRing` and
`MPSTensor.mulTensor_complexOfRing`.
-/

open scoped Matrix

namespace MPSTensor

/-- The entrywise image of a matrix over the Eisenstein integers in the complex matrices. -/
noncomputable abbrev complexOfEisenstein {m n : Type*} (X : Matrix m n EisensteinInt) :
    Matrix m n ℂ :=
  Matrix.complexOfRing eisensteinToComplex X

@[simp] theorem complexOfEisenstein_apply {m n : Type*} (X : Matrix m n EisensteinInt) (i : m)
    (j : n) : complexOfEisenstein X i j = eisensteinToComplex (X i j) := rfl

theorem complexOfEisenstein_mul {m n o : Type*} [Fintype n] (X : Matrix m n EisensteinInt)
    (Y : Matrix n o EisensteinInt) :
    complexOfEisenstein (X * Y) = complexOfEisenstein X * complexOfEisenstein Y :=
  Matrix.complexOfRing_mul eisensteinToComplex X Y

theorem complexOfEisenstein_one {n : Type*} [DecidableEq n] :
    complexOfEisenstein (1 : Matrix n n EisensteinInt) = 1 :=
  Matrix.complexOfRing_one eisensteinToComplex

theorem complexOfEisenstein_zero {m n : Type*} :
    complexOfEisenstein (0 : Matrix m n EisensteinInt) = 0 :=
  Matrix.complexOfRing_zero eisensteinToComplex

theorem complexOfEisenstein_sub {m n : Type*} (X Y : Matrix m n EisensteinInt) :
    complexOfEisenstein (X - Y) = complexOfEisenstein X - complexOfEisenstein Y :=
  Matrix.complexOfRing_sub eisensteinToComplex X Y

theorem complexOfEisenstein_smul {m n : Type*} (c : EisensteinInt) (X : Matrix m n EisensteinInt) :
    complexOfEisenstein (c • X) = eisensteinToComplex c • complexOfEisenstein X :=
  Matrix.complexOfRing_smul eisensteinToComplex c X

theorem complexOfEisenstein_transpose {m n : Type*} (X : Matrix m n EisensteinInt) :
    complexOfEisenstein Xᵀ = (complexOfEisenstein X)ᵀ :=
  Matrix.complexOfRing_transpose eisensteinToComplex X

theorem complexOfEisenstein_submatrix {m n m' n' : Type*} (X : Matrix m n EisensteinInt)
    (f : m' → m) (g : n' → n) :
    complexOfEisenstein (X.submatrix f g) = (complexOfEisenstein X).submatrix f g :=
  Matrix.complexOfRing_submatrix eisensteinToComplex X f g

theorem complexOfEisenstein_ne_zero {m n : Type*} {X : Matrix m n EisensteinInt} (hX : X ≠ 0) :
    complexOfEisenstein X ≠ 0 :=
  Matrix.complexOfRing_ne_zero eisensteinToComplex_injective hX

theorem complexOfEisenstein_blockDiagonal' {o : Type*} [DecidableEq o] {m' : o → Type*}
    (M : ∀ k, Matrix (m' k) (m' k) EisensteinInt) :
    complexOfEisenstein (Matrix.blockDiagonal' M) =
      Matrix.blockDiagonal' fun k => complexOfEisenstein (M k) :=
  Matrix.complexOfRing_blockDiagonal' eisensteinToComplex M

end MPSTensor
