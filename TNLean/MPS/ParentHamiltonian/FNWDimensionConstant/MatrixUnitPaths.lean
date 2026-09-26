/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryCoordinates
import Mathlib.Data.Matrix.Basis
import TNLean.Algebra.FinSumPermutation

/-!
# Physical path vectors for weighted matrix-unit tensors

The physical letters are directed edges between virtual indices. A product
of matrix-unit letters vanishes unless the edges form a path. The resulting
path coordinates permit finite physical projector computations without
expanding the entire physical configuration space.
-/

open scoped BigOperators Matrix InnerProductSpace

namespace MPSTensor.FNWDimensionConstant

variable {k : ℕ}

/-- A weighted matrix-unit tensor, with a directed edge encoded by the standard
bijection from pairs of virtual indices to physical letters. -/
noncomputable def matrixUnitTensor (t : Matrix (Fin k) (Fin k) ℝ) :
    MPSTensor (k * k) k := fun p ↦
  Matrix.single (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
    (t (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)

@[simp] theorem matrixUnitTensor_apply (t : Matrix (Fin k) (Fin k) ℝ)
    (a b : Fin k) :
    matrixUnitTensor t (finProdFinEquiv (a, b)) = Matrix.single a b (t a b : ℂ) := by
  simp [matrixUnitTensor]

/-- The physical configuration of a path with four directed edges. -/
def pathConfig (a b c e f : Fin k) : Cfg (k * k) 4 :=
  ![finProdFinEquiv (a, b), finProdFinEquiv (b, c),
    finProdFinEquiv (c, e), finProdFinEquiv (e, f)]

/-- Two four-edge path configurations coincide exactly when their five vertices
agree. -/
@[simp] theorem pathConfig_eq_iff (a b c e f a' b' c' e' f' : Fin k) :
    pathConfig a b c e f = pathConfig a' b' c' e' f' ↔
      a = a' ∧ b = b' ∧ c = c' ∧ e = e' ∧ f = f' := by
  constructor
  · intro h
    have h0 := finProdFinEquiv.injective (congrFun h 0)
    have h1 := finProdFinEquiv.injective (congrFun h 1)
    have h2 := finProdFinEquiv.injective (congrFun h 2)
    have h3 := finProdFinEquiv.injective (congrFun h 3)
    exact ⟨(Prod.mk.inj h0).1, (Prod.mk.inj h0).2, (Prod.mk.inj h1).2,
      (Prod.mk.inj h2).2, (Prod.mk.inj h3).2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-- A marked path vector with fixed external indices. The mark depends on the
first and last internal vertices. -/
noncomputable def pathVector (t z : Matrix (Fin k) (Fin k) ℝ) (a f : Fin k) :
    EuclideanSpace ℂ (Cfg (k * k) 4) :=
  ∑ b, ∑ c, ∑ e, EuclideanSpace.single (pathConfig a b c e f)
    ((z b e * (t a b * t b c * t c e * t e f) : ℝ) : ℂ)

/-- Inner products of marked path vectors reduce to a sum over the three
internal vertices. -/
theorem inner_pathVector (t z z' : Matrix (Fin k) (Fin k) ℝ) (a f : Fin k) :
    ⟪pathVector t z a f, pathVector t z' a f⟫_ℂ =
      ((∑ b, ∑ c, ∑ e, z b e * z' b e *
        (t a b * t b c * t c e * t e f) ^ 2 : ℝ) : ℂ) := by
  simp [pathVector, sum_inner, inner_sum, EuclideanSpace.inner_single_left,
    pathConfig_eq_iff, ite_and, pow_two, mul_left_comm, mul_comm]

/-- Evaluation of an open-boundary vector on a consistent physical path. -/
theorem groundSpaceMap_pathConfig (t : Matrix (Fin k) (Fin k) ℝ)
    (X : Matrix (Fin k) (Fin k) ℂ) (a b c e f : Fin k) :
    groundSpaceMap (matrixUnitTensor t) 4 X (pathConfig a b c e f) =
      ((t a b * t b c * t c e * t e f : ℝ) : ℂ) * X f a := by
  simp [groundSpaceMap_apply, pathConfig, List.ofFn_succ, Kraus.evalWord,
    mul_assoc, Matrix.trace_single_mul]

/-- Pairing a marked path with any full-interval boundary vector involves only
the fixed external matrix entry and a scalar path sum. -/
theorem inner_pathVector_groundSpaceMap (t z : Matrix (Fin k) (Fin k) ℝ)
    (X : Matrix (Fin k) (Fin k) ℂ) (a f : Fin k) :
    ⟪pathVector t z a f,
      WithLp.toLp 2 (groundSpaceMap (matrixUnitTensor t) 4 X)⟫_ℂ =
      ((∑ b, ∑ c, ∑ e, z b e *
        (t a b * t b c * t c e * t e f) ^ 2 : ℝ) : ℂ) * X f a := by
  simp only [pathVector, sum_inner, EuclideanSpace.inner_single_left,
    groundSpaceMap_pathConfig]
  simp [pow_two, Finset.sum_mul, mul_assoc]

/-- A mark at the first internal vertex is a physical-coordinate multiplier
on the first edge. -/
theorem pathVector_first_mark_apply (t : Matrix (Fin k) (Fin k) ℝ)
    (u : Fin k → ℝ) (a f : Fin k) (σ : Cfg (k * k) 4) :
    pathVector t (fun b _ ↦ u b) a f σ =
      (u (finProdFinEquiv.symm (σ 0)).2 : ℂ) *
        pathVector t (fun _ _ ↦ 1) a f σ := by
  simp only [pathVector, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr₂ fun b _ c _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases h : pathConfig a b c e f = σ
  · subst σ
    simp [pathConfig]
  · simp [Ne.symm h]

/-- A mark at the last internal vertex is a physical-coordinate multiplier
on the last edge. -/
theorem pathVector_last_mark_apply (t : Matrix (Fin k) (Fin k) ℝ)
    (w : Fin k → ℝ) (a f : Fin k) (σ : Cfg (k * k) 4) :
    pathVector t (fun _ e ↦ w e) a f σ =
      (w (finProdFinEquiv.symm (σ 3)).1 : ℂ) *
        pathVector t (fun _ _ ↦ 1) a f σ := by
  simp only [pathVector, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr₂ fun b _ c _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases h : pathConfig a b c e f = σ
  · subst σ
    simp [pathConfig]
  · simp [Ne.symm h]

end MPSTensor.FNWDimensionConstant
