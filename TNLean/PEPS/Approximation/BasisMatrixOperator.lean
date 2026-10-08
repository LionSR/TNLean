/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointOperatorCoordinates

/-! # Actual endpoint coordinates and their sample average

The literal endpoint operator is expressed in the recorded source-slot bases.
The sample assignments are shared between the two endpoints of each slot.
Source: polynomial-PEPS, `04-compression.tex`, lines 279–355 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {I : Type} [Fintype I]

/-- An operator constructed from its specified matrix in an orthonormal basis.
This definition imposes no contraction or positivity condition. -/
def basisMatrixOperator (b : OrthonormalBasis I ℂ E) (M : Matrix I I ℂ) : E →L[ℂ] E := by
  classical
  letI := Module.Finite.of_basis b.toBasis
  exact LinearMap.toContinuousLinearMap (Matrix.toLin b.toBasis b.toBasis M)

/-- The constructed operator has exactly the specified matrix coefficients. -/
theorem basisMatrixOperator_repr (b : OrthonormalBasis I ℂ E) (M : Matrix I I ℂ)
    (i j : I) : b.repr (basisMatrixOperator b M (b j)) i = M i j := by
  classical
  have h := congrArg (fun N : Matrix I I ℂ => N i j)
    (LinearMap.toMatrix_toLin b.toBasis b.toBasis M)
  simpa [basisMatrixOperator, LinearMap.toMatrix_apply] using h

end TNLean.PEPS.PairEffect
