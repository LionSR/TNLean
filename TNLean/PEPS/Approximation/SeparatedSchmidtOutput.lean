/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WeightedPhysicalSource

/-!
# Tracing the two discarded outputs of the separated calculation

The actual affected and exterior words act on matching Schmidt coordinates.
Tracing their two discarded outputs gives exactly the exterior action on the
weighted source error, with the original complex coefficients unchanged.
The two discarded memories are retained explicitly throughout. No contraction,
positivity, normalization, or covariance premise is needed for this identity.

The input frames remain explicit. Their identification with the original
corrected and crossing source registers is supplied by a separate construction.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–480.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped InnerProductSpace TensorProduct Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect.Word

/-- Applying fixed exterior matrices commutes with tracing the affected discard.
The ket and bra retained-coordinate spaces may have different dimensions. -/
private theorem partialTrace_outer_mulVec
    {I L T U Y d e : Type} [Fintype I] [Fintype L] [Fintype T] [Fintype U]
    [Fintype d] [Fintype e]
    (K : Matrix (Y × e) T ℂ) (K' : Matrix (Y × e) U ℂ)
    (ψ : I → T × d → ℂ) (φ : L → U × d → ℂ) (z : I × L → ℂ) :
    Matrix.partialTraceRight (∑ q, z q • Matrix.vecMulVec
      (fun h : Y × (d × e) ↦ (K *ᵥ fun t ↦ ψ q.1 (t, h.2.1)) (h.1, h.2.2))
      (fun h : Y × (d × e) ↦ conj ((K' *ᵥ fun u ↦ φ q.2 (u, h.2.1)) (h.1, h.2.2)))) =
      Matrix.partialTraceRight (K *
        Matrix.of (fun t u ↦ ∑ h : d, (∑ q, z q • Matrix.vecMulVec
          (ψ q.1) (fun r ↦ conj (φ q.2 r))) (t, h) (u, h)) * K'ᴴ) := by
  classical
  have hZ : Matrix.of (fun t u ↦ ∑ h : d, (∑ q, z q • Matrix.vecMulVec
      (ψ q.1) (fun r ↦ conj (φ q.2 r))) (t, h) (u, h)) =
      ∑ h : d, ∑ q, z q • Matrix.vecMulVec
        (fun t ↦ ψ q.1 (t, h)) (star (fun u ↦ φ q.2 (u, h))) := by
    ext t u
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Pi.star_apply, starRingEnd_apply]
  rw [hZ]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  ext y y'
  simp only [Matrix.partialTraceRight_apply, Fintype.sum_prod_type, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Pi.star_apply, starRingEnd_apply]
  rw [Finset.sum_comm]

variable {P Q X Y I T d e : Type} [Fintype X] [Fintype Y] [Fintype I] [Fintype T]
    [Fintype d] [Fintype e] {a b : Layout P} {c f : Layout Q}
    {D D' : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [NormedAddCommGroup D'] [InnerProductSpace ℂ D']

/-- The actual two local outputs from the matched Schmidt summands, with the
physical affected output projected onto the prescribed basis vector. -/
def separatedSchmidtOutput
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a) (tau : T → ℝ)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D') (v' : Word c f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c) (i : I) :
    D ⊗[ℂ] (EuclideanSpace ℂ Y ⊗[ℂ] D') :=
  ∑ t, (Real.sqrt (tau t) : ℂ) •
    (physicalComponent J x v (F (EuclideanSpace.basisFun (I × T) ℂ (i, t))) ⊗ₜ[ℂ]
      J' (v'.eval (G (EuclideanSpace.basisFun T ℂ t))))

/-- The exterior frame matrix gives the coordinates of the actual exterior output. -/
private theorem physicalOutputFrameMatrix_apply
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D') (v' : Word c f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c) (bD' : OrthonormalBasis e ℂ D')
    (y : Y) (k : e) (t : T) :
    physicalOutputFrameMatrix J' v' G bD' (y, k) t =
      ((EuclideanSpace.basisFun Y ℂ).tensorProduct bD').repr
        (J' (v'.eval (G (EuclideanSpace.basisFun T ℂ t)))) (y, k) := by
  classical
  simp only [physicalOutputFrameMatrix, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply]
  rfl

/-- The exterior word acts on the retained coordinate of the actual affected
Schmidt-output vector; the two discarded factors retain their separate indices. -/
theorem separatedSchmidtOutput_repr
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a) (tau : T → ℝ)
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D') (v' : Word c f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c) (i : I)
    (bD : OrthonormalBasis d ℂ D) (bD' : OrthonormalBasis e ℂ D')
    (h : d) (y : Y) (k : e) :
    (bD.tensorProduct ((EuclideanSpace.basisFun Y ℂ).tensorProduct bD')).repr
      (separatedSchmidtOutput J x v F tau J' v' G i) (h, (y, k)) =
      (physicalOutputFrameMatrix J' v' G bD' *ᵥ fun t ↦
        ((EuclideanSpace.basisFun T ℂ).tensorProduct bD).repr
          (schmidtPhysicalVector J x v F tau i) (t, h)) (y, k) := by
  classical
  simp only [separatedSchmidtOutput, map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, OrthonormalBasis.tensorProduct_repr_tmul_apply,
    Matrix.mulVec, dotProduct, schmidtPhysicalVector_repr, physicalComponentFrameMatrix_apply,
    physicalOutputFrameMatrix_apply]
  apply Finset.sum_congr rfl
  intro t _
  ring

open Classical in
/-- Tracing both actual discarded outputs gives the exterior action on the
weighted source error. This is an exact identity for arbitrary complex
coefficients, with independent ket and bra Schmidt-support spaces.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-exterior-input`,
`04-compression.tex`, lines 454–480. -/
theorem partialTrace_separatedSchmidtOutput_eq_weightedSourceError
    {a' : Layout P} {c' : Layout Q} {L U : Type} [Fintype L] [Fintype U]
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
    let Ψ := fun i ↦ (bD.tensorProduct ((EuclideanSpace.basisFun Y ℂ).tensorProduct bD')).repr
      (separatedSchmidtOutput J x v F tau J' v' G i)
    let Φ := fun l ↦ (bD.tensorProduct ((EuclideanSpace.basisFun Y ℂ).tensorProduct bD')).repr
      (separatedSchmidtOutput J y w F' tau' J' w' G' l)
    Matrix.partialTraceRight (∑ q, z q • Matrix.vecMulVec
      (fun h : Y × (d × e) ↦ Ψ q.1 (h.2.1, (h.1, h.2.2)))
      (fun h : Y × (d × e) ↦ conj (Φ q.2 (h.2.1, (h.1, h.2.2))))) =
      Matrix.partialTraceRight
        (physicalOutputFrameMatrix J' v' G bD' *
          ProbabilityTheory.weightedSourceError tau tau'
            (physicalFrameGramMatrix J x y v w F F' bD) z *
          (physicalOutputFrameMatrix J' w' G' bD')ᴴ) := by
  dsimp only
  simp only [separatedSchmidtOutput_repr]
  rw [partialTrace_outer_mulVec (physicalOutputFrameMatrix J' v' G bD')
    (physicalOutputFrameMatrix J' w' G' bD')
    (fun i ↦ ((EuclideanSpace.basisFun T ℂ).tensorProduct bD).repr
      (schmidtPhysicalVector J x v F tau i))
    (fun l ↦ ((EuclideanSpace.basisFun U ℂ).tensorProduct bD).repr
      (schmidtPhysicalVector J y w F' tau' l)) z]
  congr 3
  ext t u
  exact congrFun (congrFun
    (sum_schmidtPhysicalVector_outer_eq_weightedSourceError J x y v w F F' bD tau tau' z) t) u

end TNLean.PEPS.PairEffect.Word
