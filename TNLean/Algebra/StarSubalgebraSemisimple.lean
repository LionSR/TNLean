/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Semisimplicity of a finite-dimensional ⋆-subalgebra of complex matrices

A ⋆-subalgebra of the complex matrix algebra is semisimple, and over the complex
numbers it therefore decomposes as a finite product of matrix algebras
(its Wedderburn–Artin form).

This is the algebraic core of Wolf Ch. 6, towards Thm 6.14 (the structure of the
fixed-point set of a Schwarz map), and resolves the missing decomposition step
recorded in issue #27.

## Main results

* `Matrix.eq_zero_of_isNilpotent_conjTranspose_mul_self` — if the positive
  semidefinite matrix `Aᴴ * A` is nilpotent, then `A = 0`.
* `StarSubalgebra.isSemisimpleRing` — a ⋆-subalgebra of `Matrix n n ℂ` is a
  semisimple ring.
* `StarSubalgebra.exists_algEquiv_pi_matrix` — such a ⋆-subalgebra is isomorphic,
  as a `ℂ`-algebra, to a finite product of complex matrix algebras.

## Proof outline

A finite-dimensional algebra over a field is Artinian, so its Jacobson radical is
nilpotent. If `x` lies in the radical, then `x⋆ * x` lies there too (the radical
is a two-sided ideal), hence is nilpotent. In `Matrix n n ℂ` the element
`x⋆ * x = (↑x)ᴴ * ↑x` is positive semidefinite, and a nilpotent positive
semidefinite matrix vanishes (its trace is a nilpotent complex number, hence
zero, and `(Aᴴ * A).trace = 0 ↔ A = 0`). Therefore `↑x = 0`, so the radical is
trivial and the subalgebra is semisimple. Wedderburn–Artin over an algebraically
closed field then gives the product-of-matrix-algebras decomposition.

## Remaining gap towards Wolf Thm 6.14

The full theorem also asserts that the decomposition is implemented by a single
*unitary* conjugation bringing the subalgebra to block-diagonal form (each block a
full matrix algebra times the identity on a multiplicity space). That ⋆- and
unitary-upgrade of the abstract algebra isomorphism is not formalized here; it is
the remaining step for issue #27.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nilpotent positive semidefinite complex matrix is zero: if `Aᴴ * A` is
nilpotent then `A = 0`. The trace of a nilpotent matrix is a nilpotent complex
number, hence zero, and `(Aᴴ * A).trace = 0 ↔ A = 0`. -/
theorem eq_zero_of_isNilpotent_conjTranspose_mul_self {A : Matrix n n ℂ}
    (h : IsNilpotent (Aᴴ * A)) : A = 0 := by
  have htr : IsNilpotent (Aᴴ * A).trace := Matrix.isNilpotent_trace_of_isNilpotent h
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr.eq_zero

end Matrix

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- A ⋆-subalgebra of `Matrix n n ℂ` is module-finite over `ℂ`, being a `ℂ`-submodule
of the finite-dimensional algebra `Matrix n n ℂ`. -/
instance instModuleFinite : Module.Finite ℂ S :=
  (inferInstance : Module.Finite ℂ S.toSubalgebra)

instance instIsArtinianRing : IsArtinianRing S :=
  IsArtinianRing.of_finite ℂ S

/-- A finite-dimensional ⋆-subalgebra of the complex matrix algebra is a semisimple
ring. Wolf Ch. 6, towards Thm 6.14; see issue #27. -/
instance isSemisimpleRing : IsSemisimpleRing S := by
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  -- The Jacobson radical is nilpotent because the ring is Artinian.
  obtain ⟨k, hk⟩ := (IsSemiprimaryRing.isNilpotent (R := S))
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Submodule.mem_bot]
  -- `x⋆ * x` lies in the (two-sided) radical, hence is nilpotent.
  have hmem : star x * x ∈ Ring.jacobson S := Ideal.mul_mem_left _ _ hx
  have hnil : IsNilpotent (star x * x) := by
    refine ⟨k, ?_⟩
    have hpow : (star x * x) ^ k ∈ Ring.jacobson S ^ k := Ideal.pow_mem_pow hmem k
    rw [hk] at hpow
    exact (Submodule.mem_bot _).mp hpow
  -- Transfer the nilpotency to the matrix `Aᴴ * A` and apply the matrix lemma.
  set A : Matrix n n ℂ := (x : Matrix n n ℂ) with hA
  have hcoe : ((star x * x : S) : Matrix n n ℂ) = Aᴴ * A := by
    push_cast
    rw [StarMemClass.coe_star, Matrix.star_eq_conjTranspose, hA]
  have hnilM : IsNilpotent (Aᴴ * A) := by
    rw [← hcoe]
    exact hnil.map S.subtype.toRingHom
  have hx0 : A = 0 := Matrix.eq_zero_of_isNilpotent_conjTranspose_mul_self hnilM
  exact Subtype.ext (hx0.trans (ZeroMemClass.coe_zero S).symm)

/-- The Wedderburn–Artin decomposition of a finite-dimensional ⋆-subalgebra of
the complex matrix algebra: it is isomorphic, as a `ℂ`-algebra, to a finite
product of complex matrix algebras. Wolf Ch. 6, towards Thm 6.14; see issue #27. -/
theorem exists_algEquiv_pi_matrix :
    ∃ (k : ℕ) (d : Fin k → ℕ),
      Nonempty (S ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  obtain ⟨k, d, _, he⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S
  exact ⟨k, d, he⟩

end StarSubalgebra
