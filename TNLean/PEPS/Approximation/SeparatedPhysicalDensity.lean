/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SeparatedSchmidtOutput
import QICLean.Channel.PartialTraceBlocks

/-!
# Reconstructing the separated physical density

Gather all affected physical components of the two local Schmidt outputs.
Their mixed outer products, traced over both discarded memories, give a
matrix on the affected and exterior physical registers. Each affected block
is exactly the exterior action on the weighted source error.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–549.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.Word

variable {P Q X Y I T d e : Type} [Fintype X] [Fintype Y] [Fintype I] [Fintype T]
    [Fintype d] [Fintype e] {a b : Layout P} {c f : Layout Q}
    {D D' : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [NormedAddCommGroup D'] [InnerProductSpace ℂ D']

/-- Joint coordinates of all actual affected physical components and the exterior
output, with both discarded indices retained independently. -/
def separatedPhysicalCoordinates
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (v : Word a b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a) (tau : T → ℝ)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D') (v' : Word c f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c)
    (bD : OrthonormalBasis d ℂ D) (bD' : OrthonormalBasis e ℂ D') (i : I) :
    ((X × Y) × (d × e)) → ℂ :=
  fun h ↦ (bD.tensorProduct ((EuclideanSpace.basisFun Y ℂ).tensorProduct bD')).repr
    (separatedSchmidtOutput J h.1.1 v F tau J' v' G i) (h.2.1, (h.1.2, h.2.2))

/-- The full physical operator formed from the actual separated ket and bra
coordinates, after tracing both discarded memories. -/
def separatedPhysicalDensity {a' : Layout P} {c' : Layout Q} {L U : Type}
    [Fintype L] [Fintype U]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ (L × U) →ₗᵢ[ℂ] Mem a')
    (tau : T → ℝ) (tau' : U → ℝ)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D')
    (v' : Word c f) (w' : Word c' f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c)
    (G' : EuclideanSpace ℂ U →ₗᵢ[ℂ] Mem c')
    (bD : OrthonormalBasis d ℂ D) (bD' : OrthonormalBasis e ℂ D')
    (z : I × L → ℂ) : Matrix (X × Y) (X × Y) ℂ :=
  Matrix.partialTraceRight (∑ q, z q • Matrix.vecMulVec
    (separatedPhysicalCoordinates J v F tau J' v' G bD bD' q.1)
    (fun h ↦ conj (separatedPhysicalCoordinates J w F' tau' J' w' G' bD bD' q.2 h)))

open Classical in
/-- Fixing the affected physical ket and bra indices recovers exactly the
weighted source error acted on by the exterior words. -/
theorem separatedPhysicalDensity_submatrix {a' : Layout P} {c' : Layout Q} {L U : Type}
    [Fintype L] [Fintype U]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ (L × U) →ₗᵢ[ℂ] Mem a')
    (tau : T → ℝ) (tau' : U → ℝ)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D')
    (v' : Word c f) (w' : Word c' f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c)
    (G' : EuclideanSpace ℂ U →ₗᵢ[ℂ] Mem c')
    (bD : OrthonormalBasis d ℂ D) (bD' : OrthonormalBasis e ℂ D') (z : I × L → ℂ) :
    (separatedPhysicalDensity J v w F F' tau tau' J' v' w' G G' bD bD' z).submatrix
        (fun i ↦ (x, i)) (fun j ↦ (y, j)) =
      Matrix.partialTraceRight
        (physicalOutputFrameMatrix J' v' G bD' *
          ProbabilityTheory.weightedSourceError tau tau'
            (physicalFrameGramMatrix J x y v w F F' bD) z *
          (physicalOutputFrameMatrix J' w' G' bD')ᴴ) := by
  rw [separatedPhysicalDensity, Matrix.submatrix_partialTraceRight]
  rw [← partialTrace_separatedSchmidtOutput_eq_weightedSourceError
    J x y v w F F' tau tau' J' v' w' G G' bD bD' z]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, separatedPhysicalCoordinates]

end TNLean.PEPS.PairEffect.Word
