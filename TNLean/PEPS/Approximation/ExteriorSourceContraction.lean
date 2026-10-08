/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PhysicalOutputContraction
import QICLean.Analysis.OrthonormalMatrixNorm
import QICLean.Channel.RectangularTraceNormContraction

/-!
# Trace-norm contraction by the actual exterior words

Fix a common identification of the output memory with physical output and
discarded output, and choose orthonormal coordinates on the input and discarded
memories. Two independently chosen allowed words give rectangular contraction
matrices. Applying these matrices on the ket and bra sides of an arbitrary
rectangular input, then tracing the discarded output, contracts trace norm.
There is no factor depending on any input or discarded-memory dimension.

The manuscript assumes that every Hilbert space is finite dimensional, without
bounds on unspecified private dimensions. Thus finite orthonormal coordinate
bases impose no additional restriction in its setting.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19 and
`eq:compression-exterior-contraction`, lines 454–470.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-exteriorsourcecontraction-01
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalOutputMatrix_le_one

Provenance-ID: 8769-physical-exteriorsourcecontraction-02
Downstream declaration:
TNLean.PEPS.PairEffect.Word.rectangularTraceNorm_partialTrace_physicalOutputMatrix_le

-/


noncomputable section
open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word

/-- Finite coordinates preserve the norm bound of the actual exterior word.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 454–470. -/
theorem norm_physicalOutputMatrix_le_one {P X d n : Type}
    [Fintype X] [Fintype d] [Fintype n] [DecidableEq n]
    {a b : Layout P} {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (v : Word a b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bD : OrthonormalBasis d ℂ D)
    (hv : v.IsAllowed) : ‖physicalOutputMatrix J v bIn bD‖ ≤ 1 := by
  change ‖LinearMap.toMatrix bIn.toBasis
    ((EuclideanSpace.basisFun X ℂ).tensorProduct bD).toBasis
    (((J : Mem b →L[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) ∘L v.eval).toLinearMap)‖ ≤ 1
  rw [ContinuousLinearMap.norm_toMatrix_orthonormal, opNorm_linearIsometryEquiv_comp]
  exact v.norm_eval_le_one hv

/-- In finite discarded-output coordinates, the two actual exterior words contract
trace norm even for an arbitrary rectangular input. The two words need not
coincide, and the input need not be positive or Hermitian.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-exterior-contraction`,
`04-compression.tex`, lines 454–470. -/
theorem rectangularTraceNorm_partialTrace_physicalOutputMatrix_le
    {P X d n n' : Type} [Fintype X] [Fintype d] [Fintype n] [Fintype n']
    [DecidableEq X] [DecidableEq n] [DecidableEq n']
    {a a' b : Layout P} {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D)
    (v : Word a b) (w : Word a' b)
    (bIn : OrthonormalBasis n ℂ (Mem a)) (bIn' : OrthonormalBasis n' ℂ (Mem a'))
    (bD : OrthonormalBasis d ℂ D) (hv : v.IsAllowed) (hw : w.IsAllowed)
    (Z : Matrix n n' ℂ) :
    Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (physicalOutputMatrix J v bIn bD * Z * (physicalOutputMatrix J w bIn' bD)ᴴ)) ≤
      Matrix.rectangularTraceNorm Z :=
  Matrix.rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le Z _ _
    (norm_physicalOutputMatrix_le_one J v bIn bD hv)
    (norm_physicalOutputMatrix_le_one J w bIn' bD hw)

end TNLean.PEPS.PairEffect.Word
