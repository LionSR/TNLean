/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExteriorSourceContraction
import QICLean.Probability.WeightedSourceError

/-!
# Weighted source coefficients of actual separated words

Finite Schmidt coordinate spaces may embed as proper subspaces of the actual
input memories. Applying the two local words, projecting the affected physical
outputs, and tracing the common discarded memory gives the square-root weighted
blocks of the actual mixed contraction. Complex correction coefficients retain
their phase; the block operation is ordinary transpose.

The expected-error theorem takes coefficient covariance as an explicit
hypothesis and derives every operator contraction bound from the actual words.
The identification of these input frames with the original corrected and
crossing source registers is a separate construction.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–480.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-weightedphysicalsource-01
Downstream declaration:
TNLean.PEPS.PairEffect.Word.integral_rectangularTraceNorm_weightedPhysicalSource_le

Provenance-ID: 8769-physical-weightedphysicalsource-02
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalComponentFrameMatrix_le_one

Provenance-ID: 8769-physical-weightedphysicalsource-03
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalFrameGramMatrix_le_one

Provenance-ID: 8769-physical-weightedphysicalsource-04
Downstream declaration:
TNLean.PEPS.PairEffect.Word.norm_physicalOutputFrameMatrix_le_one

Provenance-ID: 8769-physical-weightedphysicalsource-05
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalComponentFrameMatrix

Provenance-ID: 8769-physical-weightedphysicalsource-06
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalComponentFrameMatrix_apply

Provenance-ID: 8769-physical-weightedphysicalsource-07
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalFrameGramMatrix

Provenance-ID: 8769-physical-weightedphysicalsource-08
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalFrameGramMatrix_apply

Provenance-ID: 8769-physical-weightedphysicalsource-09
Downstream declaration:
TNLean.PEPS.PairEffect.Word.physicalOutputFrameMatrix

Provenance-ID: 8769-physical-weightedphysicalsource-10
Downstream declaration:
TNLean.PEPS.PairEffect.Word.rectangularTraceNorm_partialTrace_physicalOutputFrameMatrix_le

Provenance-ID: 8769-physical-weightedphysicalsource-11
Downstream declaration:
TNLean.PEPS.PairEffect.Word.schmidtPhysicalVector

Provenance-ID: 8769-physical-weightedphysicalsource-12
Downstream declaration:
TNLean.PEPS.PairEffect.Word.schmidtPhysicalVector_repr

Provenance-ID: 8769-physical-weightedphysicalsource-13
Downstream declaration:
TNLean.PEPS.PairEffect.Word.sum_schmidtPhysicalVector_outer_eq_weightedSourceError

-/


noncomputable section
open scoped InnerProductSpace TensorProduct Matrix ComplexConjugate Matrix.Norms.L2Operator
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word

variable {P X d n : Type} [Fintype X] [Fintype d] [Fintype n]
    {a b : Layout P} {D : Type} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

/-- The projected actual word in an isometric input frame and discarded-output basis.
The frame is not required to span the input memory. -/
def physicalComponentFrameMatrix
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a) (bD : OrthonormalBasis d ℂ D) :
    Matrix d n ℂ := by
  classical
  exact LinearMap.toMatrix (EuclideanSpace.basisFun n ℂ).toBasis bD.toBasis
    ((physicalComponent J x v) ∘L F.toContinuousLinearMap).toLinearMap

/-- Coordinate frames and physical projection preserve the actual word's norm bound. -/
theorem norm_physicalComponentFrameMatrix_le_one [DecidableEq n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a) (bD : OrthonormalBasis d ℂ D)
    (hv : v.IsAllowed) : ‖physicalComponentFrameMatrix J x v F bD‖ ≤ 1 := by
  classical
  let : DecidableEq n := Classical.decEq n
  exact (ContinuousLinearMap.norm_toMatrix_orthonormal
    (physicalComponent J x v ∘L F.toContinuousLinearMap)
    (EuclideanSpace.basisFun n ℂ) bD).le.trans
      (norm_comp_le_one (norm_physicalComponent_le_one J x v hv)
        (LinearIsometry.norm_toContinuousLinearMap_le F))

/-- The entry of the projected frame matrix is the actual discarded-vector coordinate. -/
theorem physicalComponentFrameMatrix_apply
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a) (bD : OrthonormalBasis d ℂ D)
    (k : d) (i : n) :
    physicalComponentFrameMatrix J x v F bD k i =
      bD.repr (physicalComponent J x v (F (EuclideanSpace.basisFun n ℂ i))) k := by
  classical
  simp only [physicalComponentFrameMatrix, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply]
  rfl

/-- The mixed affected contraction in two independent isometric input frames. -/
def physicalFrameGramMatrix {a' : Layout P} {n' : Type} [Fintype n']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ n' →ₗᵢ[ℂ] Mem a') (bD : OrthonormalBasis d ℂ D) :
    Matrix n' n ℂ :=
  (physicalComponentFrameMatrix J y w F' bD)ᴴ * physicalComponentFrameMatrix J x v F bD

/-- Isometric Schmidt coordinates preserve the full affected contraction bound. -/
theorem norm_physicalFrameGramMatrix_le_one {a' : Layout P} {n' : Type}
    [Fintype n'] [DecidableEq n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ n' →ₗᵢ[ℂ] Mem a') (bD : OrthonormalBasis d ℂ D)
    (hv : v.IsAllowed) (hw : w.IsAllowed) :
    ‖physicalFrameGramMatrix J x y v w F F' bD‖ ≤ 1 := by
  classical
  calc
    _ ≤ ‖(physicalComponentFrameMatrix J y w F' bD)ᴴ‖ *
        ‖physicalComponentFrameMatrix J x v F bD‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul (norm_physicalComponentFrameMatrix_le_one J y w F' bD hw)
        (norm_physicalComponentFrameMatrix_le_one J x v F bD hv) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

/-- The Gram entry retains the actual bra–ket order of the discarded vectors. -/
theorem physicalFrameGramMatrix_apply {a' : Layout P} {n' : Type} [Fintype n']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ n' →ₗᵢ[ℂ] Mem a') (bD : OrthonormalBasis d ℂ D)
    (j : n') (i : n) :
    physicalFrameGramMatrix J x y v w F F' bD j i =
      ⟪physicalComponent J y w (F' (EuclideanSpace.basisFun n' ℂ j)),
        physicalComponent J x v (F (EuclideanSpace.basisFun n ℂ i))⟫_ℂ := by
  simp only [physicalFrameGramMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    physicalComponentFrameMatrix_apply, OrthonormalBasis.repr_apply_apply,
    RCLike.star_def, inner_conj_symm]
  exact bD.sum_inner_mul_inner _ _

/-- The actual affected output from a Schmidt vector, after physical projection.
The untouched Schmidt half is retained as a coordinate register. -/
def schmidtPhysicalVector {I T : Type} [Fintype I] [Fintype T]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a) (tau : T → ℝ) (i : I) :
    EuclideanSpace ℂ T ⊗[ℂ] D :=
  ∑ t, (Real.sqrt (tau t) : ℂ) •
    (EuclideanSpace.basisFun T ℂ t ⊗ₜ[ℂ]
      physicalComponent J x v (F (EuclideanSpace.basisFun (I × T) ℂ (i, t))))

/-- The untouched Schmidt coordinate selects its original summand, without a phase change. -/
theorem schmidtPhysicalVector_repr {I T : Type} [Fintype I] [Fintype T]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x : X) (v : Word a b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a) (tau : T → ℝ) (i : I)
    (bD : OrthonormalBasis d ℂ D) (t : T) (k : d) :
    ((EuclideanSpace.basisFun T ℂ).tensorProduct bD).repr
      (schmidtPhysicalVector J x v F tau i) (t, k) =
      (Real.sqrt (tau t) : ℂ) * physicalComponentFrameMatrix J x v F bD k (i, t) := by
  classical
  simp only [schmidtPhysicalVector, map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, OrthonormalBasis.tensorProduct_repr_tmul_apply]
  simp [physicalComponentFrameMatrix_apply]

open Classical in
/-- Tracing the actual affected discard vectors gives precisely the weighted
source error. The ket and bra Schmidt spaces may have different dimensions;
no correction coefficient is conjugated in this identity. -/
theorem sum_schmidtPhysicalVector_outer_eq_weightedSourceError
    {a' : Layout P} {I L T U : Type}
    [Fintype I] [Fintype L] [Fintype T] [Fintype U]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ (L × U) →ₗᵢ[ℂ] Mem a') (bD : OrthonormalBasis d ℂ D)
    (tau : T → ℝ) (tau' : U → ℝ) (z : I × L → ℂ) :
    let ψ := fun i ↦ ((EuclideanSpace.basisFun T ℂ).tensorProduct bD).repr
      (schmidtPhysicalVector J x v F tau i)
    let φ := fun l ↦ ((EuclideanSpace.basisFun U ℂ).tensorProduct bD).repr
      (schmidtPhysicalVector J y w F' tau' l)
    (fun t u ↦ ∑ k : d, (∑ q : I × L, z q •
      Matrix.vecMulVec (ψ q.1) (fun h ↦ conj (φ q.2 h))) (t, k) (u, k)) =
      ProbabilityTheory.weightedSourceError tau tau'
        (physicalFrameGramMatrix J x y v w F F' bD) z := by
  classical
  dsimp only
  ext t u
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    schmidtPhysicalVector_repr, map_mul, Complex.conj_ofReal,
    ProbabilityTheory.weightedSourceError, Matrix.halfWeighted, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.transpose_apply, ProbabilityTheory.sourceBlock]
  simp only [physicalFrameGramMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [starRingEnd_apply]
  ring

/-- The actual exterior output matrix on a possibly proper Schmidt-support input. -/
def physicalOutputFrameMatrix
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (v : Word a b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a) (bD : OrthonormalBasis d ℂ D) :
    Matrix (X × d) n ℂ := by
  classical
  exact LinearMap.toMatrix (EuclideanSpace.basisFun n ℂ).toBasis
    ((EuclideanSpace.basisFun X ℂ).tensorProduct bD).toBasis
    (((J : Mem b →L[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) ∘L v.eval ∘L
      F.toContinuousLinearMap).toLinearMap)

/-- Restriction to an isometric Schmidt frame keeps the exterior calculation contractive. -/
theorem norm_physicalOutputFrameMatrix_le_one [DecidableEq n]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (v : Word a b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a) (bD : OrthonormalBasis d ℂ D)
    (hv : v.IsAllowed) : ‖physicalOutputFrameMatrix J v F bD‖ ≤ 1 := by
  classical
  let : DecidableEq n := Classical.decEq n
  exact (ContinuousLinearMap.norm_toMatrix_orthonormal
    ((J : Mem b →L[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) ∘L v.eval ∘L
      F.toContinuousLinearMap) (EuclideanSpace.basisFun n ℂ)
    ((EuclideanSpace.basisFun X ℂ).tensorProduct bD)).le.trans
      (norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_comp_le_one (v.norm_eval_le_one hv) (LinearIsometry.norm_toContinuousLinearMap_le F)))

/-- The actual exterior words contract trace norm in independent Schmidt frames,
including when the ket and bra Schmidt-support dimensions differ. -/
theorem rectangularTraceNorm_partialTrace_physicalOutputFrameMatrix_le
    {a' : Layout P} {n' : Type} [Fintype n'] [DecidableEq X] [DecidableEq n']
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ n →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ n' →ₗᵢ[ℂ] Mem a') (bD : OrthonormalBasis d ℂ D)
    (hv : v.IsAllowed) (hw : w.IsAllowed) (Z : Matrix n n' ℂ) :
    Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (physicalOutputFrameMatrix J v F bD * Z * (physicalOutputFrameMatrix J w F' bD)ᴴ)) ≤
      Matrix.rectangularTraceNorm Z := by
  classical
  exact Matrix.rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le Z _ _
    (norm_physicalOutputFrameMatrix_le_one J v F bD hv)
    (norm_physicalOutputFrameMatrix_le_one J w F' bD hw)

/-- Fixed exterior operations act linearly on every source coefficient. -/
private theorem partialTrace_weightedSourceError
    {I L T U Y e : Type} [Fintype I] [Fintype L] [Fintype T] [Fintype U] [Fintype e]
    [DecidableEq T] [DecidableEq U]
    (K : Matrix (Y × e) T ℂ) (K' : Matrix (Y × e) U ℂ)
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ)
    (z : I × L → ℂ) :
    Matrix.partialTraceRight (K * ProbabilityTheory.weightedSourceError tau tau' O z * K'ᴴ) =
      ∑ q, z q • Matrix.partialTraceRight
        (K * Matrix.halfWeighted tau tau' (ProbabilityTheory.sourceBlock O q.2 q.1)ᵀ * K'ᴴ) := by
  simp only [ProbabilityTheory.weightedSourceError, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  change Matrix.partialTraceRightLM (∑ q, z q • _) = _
  simp only [map_sum, map_smul]
  rfl

open MeasureTheory

open Classical in
/-- Diagonal covariance bounds the expected physical exterior error of the actual
separated words. All contraction bounds are derived from their allowedness,
and no input, private-memory, or discarded-output dimension enters the estimate. -/
theorem integral_rectangularTraceNorm_weightedPhysicalSource_le
    {a' : Layout P} {I L T U : Type}
    [Fintype I] [Fintype L] [Fintype T] [Fintype U]
    (J : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ X ⊗[ℂ] D) (x y : X)
    (v : Word a b) (w : Word a' b)
    (F : EuclideanSpace ℂ (I × T) →ₗᵢ[ℂ] Mem a)
    (F' : EuclideanSpace ℂ (L × U) →ₗᵢ[ℂ] Mem a') (bD : OrthonormalBasis d ℂ D)
    (hv : v.IsAllowed) (hw : w.IsAllowed)
    {Q Y e : Type} [Fintype Y] [Fintype e]
    {c c' f : Layout Q} {D' : Type} [NormedAddCommGroup D'] [InnerProductSpace ℂ D']
    (J' : Mem f ≃ₗᵢ[ℂ] EuclideanSpace ℂ Y ⊗[ℂ] D')
    (v' : Word c f) (w' : Word c' f)
    (G : EuclideanSpace ℂ T →ₗᵢ[ℂ] Mem c)
    (G' : EuclideanSpace ℂ U →ₗᵢ[ℂ] Mem c') (bD' : OrthonormalBasis e ℂ D')
    (hv' : v'.IsAllowed) (hw' : w'.IsAllowed)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (z : I × L → Ω → ℂ) (kappa : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (hpsum : ∑ i, p i = 1) (hp'sum : ∑ l, p' l = 1)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1)
    (hkappa : 0 ≤ kappa)
    (hz : ∀ q r, Integrable (fun ω ↦ z q ω * conj (z r ω)) μ)
    (hcov : ∀ q r, (∫ ω, z q ω * conj (z r ω) ∂μ) =
      if q = r then ((kappa * Real.sqrt (p q.1 * p' q.2) : ℝ) : ℂ) else 0) :
    let O := physicalFrameGramMatrix J x y v w F F' bD
    let K := physicalOutputFrameMatrix J' v' G bD'
    let K' := physicalOutputFrameMatrix J' w' G' bD'
    (∫ ω, Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (K * ProbabilityTheory.weightedSourceError tau tau' O (fun q ↦ z q ω) * K'ᴴ)) ∂μ) ≤
      Real.sqrt kappa := by
  intro O K K'
  have hpoint (ω : Ω) : Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (K * ProbabilityTheory.weightedSourceError tau tau' O (fun q ↦ z q ω) * K'ᴴ)) ≤
      Matrix.rectangularTraceNorm (ProbabilityTheory.weightedSourceError tau tau' O
        (fun q ↦ z q ω)) :=
    rectangularTraceNorm_partialTrace_physicalOutputFrameMatrix_le
      J' v' w' G G' bD' hv' hw' _
  have hint := ProbabilityTheory.integrable_rectangularTraceNorm_weightedSourceError
    tau tau' O z hz htau htau' htausum htau'sum
  have hmeas : AEStronglyMeasurable (fun ω ↦ Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight
        (K * ProbabilityTheory.weightedSourceError tau tau' O (fun q ↦ z q ω) * K'ᴴ))) μ := by
    simp_rw [partialTrace_weightedSourceError]
    exact ProbabilityTheory.aestronglyMeasurable_rectangularTraceNorm_sum z hz _
  have hint' := hint.mono' hmeas (Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Matrix.rectangularTraceNorm_nonneg _)]
    exact hpoint ω)
  exact (integral_mono hint' hint hpoint).trans
    (ProbabilityTheory.integral_rectangularTraceNorm_weightedSourceError_le
      p p' tau tau' O z kappa hp hp' htau htau' hpsum hp'sum htausum htau'sum
      (norm_physicalFrameGramMatrix_le_one J x y v w F F' bD hv hw) hkappa hz hcov)

end TNLean.PEPS.PairEffect.Word
