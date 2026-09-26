/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Determinants of orthogonal and symplectic Kronecker products

An orthogonal matrix has determinant whose square is one. Consequently its
determinant is a sign over a domain, and every even power of its determinant
is one. The Kronecker determinant formula then gives determinant one for a
product of orthogonal matrices of even dimensions. The same conclusion for
symplectic factors needs no parity hypothesis.

These are the determinant identities used in arXiv:1703.09188, lines
1464--1477. The symplectic assertion here concerns the standard symplectic
form; identifying it with the source's interleaved form is a separate change
of coordinates.
-/

open scoped Kronecker

namespace Matrix

variable {m n R : Type*}
variable [Fintype m] [DecidableEq m] [CommRing R]

/-- The determinant of an orthogonal matrix has square one. -/
private theorem det_sq_eq_one_of_mem_orthogonalGroup (A : Matrix m m R)
    (hA : A ∈ orthogonalGroup m R) : A.det ^ 2 = 1 := by
  have hA' : A * Aᵀ = 1 := (mem_orthogonalGroup_iff (n := m) (R := R)).mp hA
  have hdet := congrArg det hA'
  simpa only [det_mul, det_transpose, det_one, pow_two] using hdet

/-- An orthogonal matrix over a domain has determinant (1) or (-1).

This is the determinant assertion used in arXiv:1703.09188, lines
1469--1477. -/
theorem det_eq_one_or_neg_one_of_mem_orthogonalGroup [NoZeroDivisors R]
    (A : Matrix m m R) (hA : A ∈ orthogonalGroup m R) :
    A.det = 1 ∨ A.det = -1 := by
  exact sq_eq_one_iff.mp (det_sq_eq_one_of_mem_orthogonalGroup A hA)

/-- Every even power of the determinant of an orthogonal matrix is one.
No assumption on the coefficient ring being a domain is needed. -/
theorem det_pow_eq_one_of_mem_orthogonalGroup_of_even (A : Matrix m m R)
    (hA : A ∈ orthogonalGroup m R) {k : ℕ} (hk : Even k) :
    A.det ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  simp only [← two_mul, pow_mul, det_sq_eq_one_of_mem_orthogonalGroup A hA,
    one_pow]

/-- The Kronecker product of orthogonal matrices of even dimensions has
determinant one, including when either index type is empty.

Source: arXiv:1703.09188, lines 1473--1477. -/
theorem det_kronecker_eq_one_of_mem_orthogonalGroup
    [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R)
    (hA : A ∈ orthogonalGroup m R) (hB : B ∈ orthogonalGroup n R)
    (hm : Even (Fintype.card m)) (hn : Even (Fintype.card n)) :
    (A ⊗ₖ B).det = 1 := by
  rw [det_kronecker,
    det_pow_eq_one_of_mem_orthogonalGroup_of_even A hA hn,
    det_pow_eq_one_of_mem_orthogonalGroup_of_even B hB hm,
    one_mul]

/-- A Kronecker product of symplectic matrices has determinant one, with no
parity or nonemptiness hypothesis beyond their symplectic index types.

Source: arXiv:1703.09188, lines 1473--1477. -/
theorem det_kronecker_eq_one_of_mem_symplecticGroup
    {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix (p ⊕ p) (p ⊕ p) R)
    (B : Matrix (q ⊕ q) (q ⊕ q) R)
    (hA : A ∈ symplecticGroup p R) (hB : B ∈ symplecticGroup q R) :
    (A ⊗ₖ B).det = 1 := by
  rw [det_kronecker, SymplecticGroup.det_eq_one hA,
    SymplecticGroup.det_eq_one hB]
  simp

end Matrix
