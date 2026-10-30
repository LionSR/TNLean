/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive quadratic lifting of a one-particle coefficient matrix

The map `A ↦ ∑ᵤᵥ Aᵤᵥ sᵤ* sᵥ` preserves positive semidefiniteness for every finite
family of operators. In particular it applies to hard-core qubit lowering operators;
no canonical bosonic commutation relations are used. A positive one-particle gap therefore
gives the many-body occupation-minus-mode inequality used in the tree example.

These are algebraic ingredients of the counterexample to the unrestricted metric-lattice
summability assertion in Hastings, arXiv:cond-mat/0508554v3, equation `oibu`, lines 1690–1694.
The complete physical tree family is described in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex`; this module proves the lifting
step and does not assert that the full physical counterexample has been formalized.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace TNLean.Lattice.TreeBasisCounterexample

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- The quadratic lifting of a coefficient matrix through a family of lowering operators. -/
noncomputable def quadraticLift (s : ι → Matrix n n ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun A := ∑ u, ∑ v, A u v • ((s u)ᴴ * s v)
  map_add' A B := by simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- The lowering operator of a collective mode. -/
noncomputable def modeOperator (s : ι → Matrix n n ℂ) (w : ι → ℂ) : Matrix n n ℂ :=
  ∑ v, w v • s v

/-- The lift of a rank-one coefficient matrix is a positive operator of the form `B* B`. -/
theorem quadraticLift_outer (s : ι → Matrix n n ℂ) (w : ι → ℂ) :
    quadraticLift s (vecMulVec (star w) w) = (modeOperator s w)ᴴ * modeOperator s w := by
  simp only [quadraticLift, LinearMap.coe_mk, AddHom.coe_mk, vecMulVec_apply, Pi.star_apply,
    modeOperator, conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- A rectangular coefficient matrix gives precisely the sum of squares of its row modes. -/
theorem quadraticLift_gram {κ : Type*} [Fintype κ] (s : ι → Matrix n n ℂ)
    (D : Matrix κ ι ℂ) :
    quadraticLift s (Dᴴ * D) = ∑ k, (modeOperator s (D k))ᴴ * modeOperator s (D k) := by
  have hgram : Dᴴ * D = ∑ k, vecMulVec (star (D k)) (D k) := by
    ext u v
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.sum_apply,
      vecMulVec_apply, Pi.star_apply]
  rw [hgram, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ quadraticLift_outer s (D k)

/-- Quadratic lifting preserves positive semidefiniteness, including for hard-core spins. -/
theorem posSemidef_quadraticLift (s : ι → Matrix n n ℂ) {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) : (quadraticLift s A).PosSemidef := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB, star_eq_conjTranspose, quadraticLift_gram]
  apply Matrix.posSemidef_sum
  intro k _
  exact posSemidef_conjTranspose_mul_self _

variable [DecidableEq ι]

/-- The identity lifts to the total occupation operator. -/
theorem quadraticLift_one (s : ι → Matrix n n ℂ) :
    quadraticLift s 1 = ∑ v, (s v)ᴴ * s v := by
  simp [quadraticLift, Matrix.one_apply]

/-- A one-particle gap transfers to a many-body occupation-minus-mode inequality.
The input is an inequality only for the finite coefficient matrix. -/
theorem quadraticLift_gap (s : ι → Matrix n n ℂ) {A : Matrix ι ι ℂ}
    (w : ι → ℂ) (δ : ℝ)
    (hA : (A - (δ : ℂ) • (1 - vecMulVec (star w) w)).PosSemidef) :
    (quadraticLift s A - (δ : ℂ) •
      ((∑ v, (s v)ᴴ * s v) - (modeOperator s w)ᴴ * modeOperator s w)).PosSemidef := by
  have h := posSemidef_quadraticLift s hA
  simpa only [map_sub, map_smul, quadraticLift_one, quadraticLift_outer] using h

end TNLean.Lattice.TreeBasisCounterexample
