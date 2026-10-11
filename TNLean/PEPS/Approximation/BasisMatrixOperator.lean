/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Operators in finite orthonormal coordinates

A matrix in a finite orthonormal basis specifies a continuous linear operator.
Its entries are exactly the coordinates of the images of the basis vectors.
The index set may be empty; no positivity or contraction condition is imposed.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the source coordinates at lines 279–355 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {I : Type} [Fintype I]

/-- An operator constructed from its specified matrix in an orthonormal basis.
This definition imposes no contraction or positivity condition.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 565–588. -/
def basisMatrixOperator (b : OrthonormalBasis I ℂ E) (M : Matrix I I ℂ) : E →L[ℂ] E := by
  classical
  letI := Module.Finite.of_basis b.toBasis
  exact LinearMap.toContinuousLinearMap (Matrix.toLin b.toBasis b.toBasis M)

/-- The constructed operator has exactly the specified matrix coefficients.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 565–588. -/
theorem basisMatrixOperator_repr (b : OrthonormalBasis I ℂ E) (M : Matrix I I ℂ)
    (i j : I) : b.repr (basisMatrixOperator b M (b j)) i = M i j := by
  classical
  have h := congrArg (fun N : Matrix I I ℂ => N i j)
    (LinearMap.toMatrix_toLin b.toBasis b.toBasis M)
  simpa [basisMatrixOperator, LinearMap.toMatrix_apply] using h

/-- The coordinate-entry matrix of an actual continuous linear map is its
linear-map matrix in the same orthonormal bases.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
theorem matrix_repr_eval_eq_toMatrix
    {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (b : OrthonormalBasis I ℂ E) (c : OrthonormalBasis J ℂ F) (A : E →L[ℂ] F) :
    Matrix.of (fun i j ↦ c.repr (A (b j)) i) =
      LinearMap.toMatrix b.toBasis c.toBasis A.toLinearMap := by
  classical
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply]


end TNLean.PEPS.PairEffect
