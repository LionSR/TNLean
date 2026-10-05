/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphBondContraction

/-!
# Products of physical maps on graph states with dependent alphabets

Physical maps with arbitrary vertex-dependent input and output spaces commute
with the actual graph contraction. The graph state belongs to the product of
the local tensor-map ranges. Local isometries on those ranges therefore preserve
physical overlaps on that product range, without ambient surjectivity.

Source: SCP10, arXiv:1001.3807, Observation 6.4 and its use in blocking,
`Papers/1001.3807/paper_v3.tex`, lines 1765–1880.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {P Q R I : V → Type*}

/-- The product matrix of physical maps with vertex-dependent alphabets.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
def graphPhysicalProductMatrix (F : (v : V) → Matrix (Q v) (P v) ℂ) :
    Matrix ((v : V) → Q v) ((v : V) → P v) ℂ :=
  fun τ σ => ∏ v, F v (τ v) (σ v)

/-- The actual product physical operation with heterogeneous local spaces.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
def graphPhysicalProductMap [∀ v, Fintype (P v)]
    (F : (v : V) → Matrix (Q v) (P v) ℂ) :
    (((v : V) → P v) → ℂ) →ₗ[ℂ] (((v : V) → Q v) → ℂ) :=
  Matrix.mulVecLin (graphPhysicalProductMatrix F)

/-- Multiplying physical product matrices composes the maps locally.
Source: the independent physical changes of SCP10, lines 1765–1820. -/
theorem graphPhysicalProductMatrix_mul [∀ v, Fintype (Q v)]
    (F : (v : V) → Matrix (R v) (Q v) ℂ)
    (T : (v : V) → Matrix (Q v) (P v) ℂ) :
    graphPhysicalProductMatrix F * graphPhysicalProductMatrix T =
      graphPhysicalProductMatrix (fun v => F v * T v) := by
  classical
  ext τ σ
  simp only [graphPhysicalProductMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : V) (i : Q v) => F v (τ v) i * T v i (σ v))).symm

omit [LinearOrder V] in
/-- Taking adjoints commutes with a product of physical maps.
Source: SCP10, isometric accessibility in lines 1765–1820. -/
theorem graphPhysicalProductMatrix_conjTranspose
    (F : (v : V) → Matrix (Q v) (P v) ℂ) :
    (graphPhysicalProductMatrix F).conjTranspose =
      graphPhysicalProductMatrix (fun v => (F v).conjTranspose) := by
  ext τ σ
  simp only [graphPhysicalProductMatrix, Matrix.conjTranspose_apply, star_prod]

/-- Local Gram equalities preserve every physical overlap on the product
of the original local ranges. No ambient surjectivity is needed.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
theorem graphPhysicalProductMap_dotProduct_on_range
    [∀ v, Fintype (P v)] [∀ v, Fintype (Q v)] [∀ v, Fintype (I v)]
    (F : (v : V) → Matrix (Q v) (P v) ℂ)
    (T : (v : V) → Matrix (P v) (I v) ℂ)
    (h : ∀ v, (F v * T v).conjTranspose * (F v * T v) =
      (T v).conjTranspose * T v)
    (ψ φ : ((v : V) → P v) → ℂ)
    (hψ : ψ ∈ LinearMap.range (graphPhysicalProductMap T))
    (hφ : φ ∈ LinearMap.range (graphPhysicalProductMap T)) :
    star (graphPhysicalProductMap F ψ) ⬝ᵥ graphPhysicalProductMap F φ = star ψ ⬝ᵥ φ := by
  classical
  obtain ⟨x, rfl⟩ := hψ
  obtain ⟨y, rfl⟩ := hφ
  have hGram : (graphPhysicalProductMatrix F * graphPhysicalProductMatrix T).conjTranspose *
        (graphPhysicalProductMatrix F * graphPhysicalProductMatrix T) =
      (graphPhysicalProductMatrix T).conjTranspose * graphPhysicalProductMatrix T := by
    rw [graphPhysicalProductMatrix_mul, graphPhysicalProductMatrix_conjTranspose,
      graphPhysicalProductMatrix_mul, graphPhysicalProductMatrix_conjTranspose,
      graphPhysicalProductMatrix_mul]
    simp only [h]
  simp only [graphPhysicalProductMap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hGram]

variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*} [Fintype X]

/-- Product physical maps commute with the actual sum over graph bond labels.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
theorem graphPhysicalProductMap_graphBondNetwork [∀ v, Fintype (P v)]
    (F : (v : V) → Matrix (Q v) (P v) ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) :
    graphPhysicalProductMap F (graphBondNetwork a) =
      graphBondNetwork (fun v η τ => ∑ s : P v, F v τ s * a v η s) := by
  classical
  ext τ
  simp only [graphPhysicalProductMap, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    graphPhysicalProductMatrix, graphBondNetwork, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : V) (s : P v) =>
    F v (τ v) s * a v (fun f => η f.1) s)).symm

/-- The physical support restriction is derived from the actual graph
contraction, rather than postulated as a state hypothesis.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
theorem graphBondNetwork_mem_range_productSiteMap
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) :
    graphBondNetwork a ∈ LinearMap.range
      (graphPhysicalProductMap (fun v s η => a v η s)) := by
  classical
  refine ⟨∑ η : Edge Γ → X, Pi.single (fun v f => η f.1) 1, ?_⟩
  simp only [map_sum, graphPhysicalProductMap, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one]
  ext σ
  simp only [Finset.sum_apply, Matrix.col_apply, graphPhysicalProductMatrix, graphBondNetwork]

/-- The actual state also belongs to the physical product range in its
Hilbert-space realization. Source: SCP10, Observation 6.4, lines 1765–1820. -/
theorem graphBondNetwork_mem_euclideanRange_productSiteMap [DecidableEq X]
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) :
    WithLp.toLp 2 (graphBondNetwork a) ∈
      (Matrix.toEuclideanLin (LinearMap.toMatrix'
        (graphPhysicalProductMap (fun v s η => a v η s)))).range := by
  obtain ⟨x, hx⟩ := graphBondNetwork_mem_range_productSiteMap a
  refine ⟨WithLp.toLp 2 x, ?_⟩
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    LinearMap.toMatrix'_mulVec] using congrArg (WithLp.toLp 2) hx

end TNLean.PEPS
