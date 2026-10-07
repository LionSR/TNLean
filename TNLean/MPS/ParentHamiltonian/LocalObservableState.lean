/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import TNLean.MPS.ParentHamiltonian.LocalObservableExpectation

/-!
# Bounded local MPS states

A positive invariant virtual matrix of nonzero trace determines a positive
normalized functional on each finite local observable algebra. Its operator
norm is one. Thus the local expectations satisfy the bound needed to extend
a consistent family to the quasi-local algebra. Neither primitivity nor
faithfulness of the invariant matrix is required for this bound.

These are consequences of the local GVBS expectation in Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b). The construction in this file
is finite dimensional; it does not assert purity of an infinite-volume state.
-/

open scoped ComplexOrder Matrix MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The local observable insertion expectation as a complex-linear functional.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
noncomputable def observableInsertionExpectationₗ (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (k : ℕ) :
    Matrix (Cfg d k) (Cfg d k) ℂ →ₗ[ℂ] ℂ where
  toFun := observableInsertionExpectation A ρ
  map_add' := observableInsertionExpectation_add A ρ
  map_smul' := by
    intro c X
    exact observableInsertionExpectation_smul A ρ c X

/-- The positive local functional at a positive virtual matrix, with the matrix
operator norm on its domain. Normalization is established separately at an
invariant matrix of nonzero trace. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
noncomputable def observableInsertionExpectationPositive (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (k : ℕ) :
    CStarMatrix (Cfg d k) (Cfg d k) ℂ →P[ℂ] ℂ := by
  let f : CStarMatrix (Cfg d k) (Cfg d k) ℂ →ₚ[ℂ] ℂ :=
    { toLinearMap := (observableInsertionExpectationₗ A ρ k).comp
        CStarMatrix.ofMatrixₗ.symm.toLinearMap
      monotone' := by
        apply (monotone_iff_map_nonneg _).mpr
        intro X hX
        exact observableInsertionExpectation_nonneg A hρ
          (Matrix.nonneg_iff_posSemidef.mp
            (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hX)) }
  exact PositiveContinuousLinearMap.ofClass f

/-- The positive functional agrees with the trace insertion formula.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
@[simp] theorem observableInsertionExpectationPositive_apply (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectationPositive A hρ k (CStarMatrix.ofMatrix X) =
      observableInsertionExpectation A ρ X := rfl

/-- The local positive functional at an invariant matrix of nonzero trace
has norm one. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), normalized local GVBS expectations. -/
theorem norm_observableInsertionExpectationPositive (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0) (k : ℕ) :
    ‖(observableInsertionExpectationPositive A hρ k :
      CStarMatrix (Cfg d k) (Cfg d k) ℂ →L[ℂ] ℂ)‖ = 1 := by
  apply Complex.ofReal_injective
  rw [PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one, Complex.ofReal_one]
  exact observableInsertionExpectation_one A ρ hfix htr k

/-- The absolute value of a normalized local expectation is bounded by the
observable operator norm. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), local state property. -/
theorem norm_observableInsertionExpectation_le (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    ‖observableInsertionExpectation A ρ X‖ ≤ ‖CStarMatrix.ofMatrix X‖ := by
  change ‖(observableInsertionExpectationPositive A hρ k).toContinuousLinearMap
    (CStarMatrix.ofMatrix X)‖ ≤ _
  simpa only [norm_observableInsertionExpectationPositive A hρ hfix htr k, one_mul]
    using (observableInsertionExpectationPositive A hρ k).toContinuousLinearMap.le_opNorm
      (CStarMatrix.ofMatrix X)

/-- Taking the adjoint of a local observable conjugates its expectation.
Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), positivity of the local GVBS expectations. -/
theorem observableInsertionExpectation_conjTranspose (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ Xᴴ = star (observableInsertionExpectation A ρ X) := by
  let f : Matrix (Cfg d k) (Cfg d k) ℂ →ₚ[ℂ] ℂ :=
    { toLinearMap := observableInsertionExpectationₗ A ρ k
      monotone' := by
        apply (monotone_iff_map_nonneg (observableInsertionExpectationₗ A ρ k)).mpr
        exact fun Y hY => observableInsertionExpectation_nonneg A hρ
          (Matrix.nonneg_iff_posSemidef.mp hY) }
  exact map_star f X

end MPSTensor
