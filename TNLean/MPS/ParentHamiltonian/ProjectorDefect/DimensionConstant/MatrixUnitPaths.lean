/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.SpectatorBoundaryGram
import Mathlib.Data.Matrix.Basis
import QICLean.Algebra.Combinatorics.FinSumPermutation
import QICLean.Algebra.Matrix.MatrixSingleSpan
import QICLean.Channel.KrausMap.KrausMap

/-!
# Physical path vectors for weighted matrix-unit tensors

The physical letters are directed edges between virtual indices. A product
of matrix-unit letters vanishes unless the edges form a path. The resulting
path coordinates permit finite physical projector computations without
expanding the entire physical configuration space.

## Normalization and injectivity of weighted matrix-unit tensors

Nonzero weights give one-site injectivity. Unit column sums of their squares
give the trace-preserving Kraus normalization.

## Unmarked path vectors as open-boundary matrix-product vectors

For weighted matrix-unit tensors, fixing the external vertices of a path
is equivalent to inserting the corresponding matrix-unit boundary.

## Normalization and orthogonality from scalar path sums

The inner-product formulas for marked paths turn scalar contractions into
unit-vector and ground-space orthogonality certificates.
-/

section

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

end

section

open scoped BigOperators Matrix

namespace MPSTensor.FNWDimensionConstant

/-- Nonzero weights retain every matrix unit in the span of the letters. -/
theorem matrixUnitTensor_isInjective {k : ℕ} (t : Matrix (Fin k) (Fin k) ℝ)
    (ht : ∀ i j, t i j ≠ 0) : Kraus.IsInjective (matrixUnitTensor t) := by
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  simpa [Matrix.smul_single, ht i j] using
    (Submodule.span ℂ (Set.range (matrixUnitTensor t))).smul_mem (t i j : ℂ)⁻¹
      (Submodule.subset_span (Set.mem_range_self (finProdFinEquiv (i, j))))

/-- Unit column sums of the squared weights give trace preservation. -/
theorem matrixUnitTensor_isTP {k : ℕ} (t : Matrix (Fin k) (Fin k) ℝ)
    (hcol : ∀ j, ∑ i, t i j ^ 2 = 1) : Kraus.IsTP (matrixUnitTensor t) := by
  rw [Kraus.IsTP, ← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, matrixUnitTensor_apply, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same]
  ext i j
  simp [Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply, ite_and,
    ← pow_two, ← Complex.ofReal_pow, ← Complex.ofReal_sum, hcol]

end MPSTensor.FNWDimensionConstant

end

section

open scoped BigOperators Matrix InnerProductSpace

namespace MPSTensor.FNWDimensionConstant

variable {k : ℕ}

/-- The unmarked four-edge path vector is the open-boundary vector of the
matrix unit joining its terminal vertex to its initial vertex. -/
theorem pathVector_one_eq_groundSpaceMap (t : Matrix (Fin k) (Fin k) ℝ)
    (a f : Fin k) :
    pathVector t (fun _ _ ↦ 1) a f =
      WithLp.toLp 2 (groundSpaceMap (matrixUnitTensor t) 4 (Matrix.single f a 1)) := by
  ext σ
  simp only [pathVector, WithLp.ofLp_sum, Finset.sum_apply, one_mul,
    groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord]
  simp [pathConfig, funext_iff, Fin.forall_fin_succ,
    matrixUnitTensor, Matrix.mul_apply, Matrix.single_apply]
  simp only [← finProdFinEquiv.symm_apply_eq, Prod.ext_iff]
  simp [Matrix.trace, Matrix.single_apply, ite_and]
  split_ifs <;> simp_all [mul_assoc]

end MPSTensor.FNWDimensionConstant

end

section

open scoped BigOperators InnerProductSpace

namespace MPSTensor.FNWDimensionConstant

variable {k : ℕ}

/-- A unit scalar self-contraction normalizes a marked path vector. -/
theorem norm_pathVector_eq_one (t z : Matrix (Fin k) (Fin k) ℝ) (a f : Fin k)
    (h : (∑ b, ∑ c, ∑ e, z b e * z b e *
      (t a b * t b c * t c e * t e f) ^ 2 : ℝ) = 1) :
    ‖pathVector t z a f‖ = 1 := by
  have hi := inner_pathVector t z z a f
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hi, h, Complex.ofReal_one,
    RCLike.one_re, Real.sqrt_one]

/-- A vanishing scalar contraction makes a marked path perpendicular to the
full-interval ground space. -/
theorem pathVector_mem_map_groundSpace_orthogonal
    (t z : Matrix (Fin k) (Fin k) ℝ) (a f : Fin k)
    (h : (∑ b, ∑ c, ∑ e, z b e *
      (t a b * t b c * t c e * t e f) ^ 2 : ℝ) = 0) :
    pathVector t z a f ∈ ((groundSpace (matrixUnitTensor t) 4).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨X, hX⟩ := (mem_map_groundSpace_iff (matrixUnitTensor t) 4 u).mp hu
  have huX : WithLp.toLp 2 (groundSpaceMap (matrixUnitTensor t) 4 X) = u :=
    congrArg (WithLp.toLp 2) hX
  simpa only [huX, h, Complex.ofReal_zero, zero_mul] using
    inner_pathVector_groundSpaceMap t z X a f

end MPSTensor.FNWDimensionConstant

end
