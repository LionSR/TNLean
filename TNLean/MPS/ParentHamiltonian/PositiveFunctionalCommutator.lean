/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Matrix.Order
/-!
# Positive functionals and commutator energies

A positive functional vanishing on a positive finite-dimensional Hamiltonian
also vanishes on its left multiples. Consequently
\(f(X^*[H,X])=f(X^*HX)\). If \(C,H\geq0\), \(C\leq cH\), and \(f(H)=0\), then
\(f(X^*[C,X])\leq c f(X^*[H,X])\). Normalization and translation invariance
are unnecessary.

The first lemma is the algebraic Cauchy--Schwarz implication for a vanishing
square in a star-ordered complex algebra. The remaining lemmas use the positive
square factorization of finite matrices. They are intermediate consequences
of the zero-energy argument in Nachtergaele, arXiv:cond-mat/9410110,
Section 6, lines 2649--2675; they do not assert an infinite-volume gap.
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace PositiveLinearMap
variable {E : Type*} [Ring E] [PartialOrder E] [Module ℂ E] [StarRing E]
  [StarOrderedRing E] [SelfAdjointDecompose E] [StarModule ℂ E] [IsScalarTower ℂ E E]
/-- Vanishing expectation of a square annihilates every left multiple of
that square. This is the Cauchy--Schwarz step in the finite zero-energy
argument of Nachtergaele, arXiv:cond-mat/9410110, Section 6. -/
theorem apply_mul_star_mul_self_eq_zero
    (f : E →ₚ[ℂ] ℂ) (Y C : E) (hzero : f (star C * C) = 0) :
    f (Y * (star C * C)) = 0 := by
  exact norm_eq_zero.mp (le_antisymm
    (by simpa only [star_star, mul_assoc, hzero, norm_zero, Real.sqrt_zero, mul_zero] using
      PositiveLinearMap.norm_map_star_mul_le f (star (Y * star C)) C) (norm_nonneg _))
variable {n : Type*} [Fintype n]
open scoped Classical in
/-- A positive matrix of zero expectation has every left multiple of zero
expectation. Source: the finite zero-energy argument in Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem apply_mul_eq_zero_of_posSemidef
    (f : Matrix n n ℂ →ₚ[ℂ] ℂ) (Y H : Matrix n n ℂ)
    (hH : H.PosSemidef) (hzero : f H = 0) : f (Y * H) = 0 := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  exact apply_mul_star_mul_self_eq_zero f Y C hzero
/-- The commutator energy of a positive matrix of zero expectation is its
quadratic-form energy. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 6, lines 2649--2675. -/
theorem apply_conjTranspose_commutator_eq
    (f : Matrix n n ℂ →ₚ[ℂ] ℂ) (H X : Matrix n n ℂ)
    (hH : H.PosSemidef) (hzero : f H = 0) :
    f (Xᴴ * (H * X - X * H)) = f (Xᴴ * H * X) := by
  have hz := apply_mul_eq_zero_of_posSemidef f (Xᴴ * X) H hH hzero
  simp only [Matrix.mul_sub, ← Matrix.mul_assoc, map_sub, hz, sub_zero]
/-- Positive comparison of finite Hamiltonians compares their commutator
energies under the hypothesis \(f(H)=0\). The comparison
itself forces zero expectation for the smaller Hamiltonian.
Source: the finite positive-comparison argument used in Nachtergaele,
arXiv:cond-mat/9410110, Section 6. -/
theorem apply_conjTranspose_commutator_le
    (f : Matrix n n ℂ →ₚ[ℂ] ℂ) (C H X : Matrix n n ℂ)
    (hC : C.PosSemidef) (hH : H.PosSemidef) (hzero : f H = 0) (c : ℝ)
    (hBound : C ≤ (c : ℂ) • H) :
    f (Xᴴ * (C * X - X * C)) ≤ (c : ℂ) * f (Xᴴ * (H * X - X * H)) := by
  have hzC : f C = 0 := le_antisymm
    (by simpa only [map_smul, hzero, smul_zero] using OrderHomClass.monotone f hBound)
    (f.map_nonneg hC.nonneg)
  rw [apply_conjTranspose_commutator_eq f C X hC hzC,
    apply_conjTranspose_commutator_eq f H X hH hzero]
  simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    map_smul, smul_eq_mul] using
    OrderHomClass.monotone f (star_left_conjugate_le_conjugate hBound X)
end PositiveLinearMap
