/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Multiplicity.GraphInsertedBondState
import TNLean.PEPS.Tensor.GraphState.GraphPhysicalMap
import TNLean.PEPS.Injectivity.Regular.RegularSiteGram
import TNLean.PEPS.Injectivity.GInjective.GIsometricSupportCoordinates

/-!
# One physical support transport for every inserted graph contraction

The same local normalized physical maps carry every choice of bond operators.
Neither their coefficients, their support, nor their positive normalization
factors depend on those operators. Source: SCP10, arXiv:1001.3807,
Observations 6.4–6.6, lines 1765–1915. The arbitrary-matrix formulation is an
auxiliary extension; it does not assert ground-space membership.

It also contains the following results.

* `TNLean.PEPS.IsGIsometric.exists_physicalSupportTransport`,
  `TNLean.PEPS.exists_graphGIsometricPhysicalSupportTransport`: physical support transport between
  G-isometric graph tensors.
-/

section GraphGIsometricSupportTransport

/-!
## Physical support transport between G-isometric graph tensors

Two physical realizations of the same unitary virtual symmetry have isometric
physical supports after retaining their positive normalization factors.
Applying the derived local maps to an actual graph contraction gives the
actual other graph contraction. Source: SCP10, arXiv:1001.3807,
Observations 6.4–6.6, lines 1765–1915.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

section Local
variable {G ι κ ν : Type*} [Group G] [Finite G] [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
attribute [local instance] Representation.invertibleFintypeCardComplex

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] in
/-- The normalized second tensor composed with the normalized adjoint of the
first transports their physical supports isometrically. Both positive factors
remain explicit. Source: SCP10, Observations 6.4 and 6.6. -/
theorem IsGIsometric.exists_physicalSupportTransport
    {ρ : Representation ℂ G (ι → ℂ)}
    {A : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)} {B : (ι → ℂ) →ₗ[ℂ] (ν → ℂ)}
    (hA : IsGIsometric ρ A) (hB : IsGIsometric ρ B)
    (hU : ∀ g x y, star (ρ g x) ⬝ᵥ ρ g y = star x ⬝ᵥ y) :
    ∃ ca cb : ℝ, 0 < ca ∧ 0 < cb ∧
      ∃ F : (κ → ℂ) →ₗ[ℂ] (ν → ℂ),
        F ∘ₗ A = ((Real.sqrt ca : ℂ) / (Real.sqrt cb : ℂ)) • B ∧
        ∀ x ∈ A.range, ∀ y ∈ A.range, star (F x) ⬝ᵥ F y = star x ⬝ᵥ y := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨ca, hca, hJA, hJ⟩ := hA.exists_accessibleCoordinates hU
  obtain ⟨cb, hcb, hBinner⟩ := hB.exists_inner_eq
  let J := (Real.sqrt ca : ℂ)⁻¹ • coordinateAdjoint A
  let F := (Real.sqrt cb : ℂ)⁻¹ • B ∘ₗ J
  have hBP : B ∘ₗ ρ.averageMap = B :=
    LinearMap.ext (apply_averageMap_of_forall_comp_eq hB.invariant)
  change J ∘ₗ A = (Real.sqrt ca : ℂ) • ρ.averageMap at hJA
  have hFA : F ∘ₗ A = ((Real.sqrt ca : ℂ) / (Real.sqrt cb : ℂ)) • B := by
    simp only [F, LinearMap.comp_assoc, hJA, LinearMap.comp_smul, LinearMap.smul_comp,
      hBP, smul_smul, div_eq_mul_inv, mul_comm]
  have hmem (x : κ → ℂ) (hx : x ∈ A.range) : J x ∈ ρ.invariants := by
    obtain ⟨u, rfl⟩ := hx
    have h := LinearMap.congr_fun hJA u
    change J (A u) = _ at h
    rw [h]
    exact ρ.invariants.smul_mem _ (ρ.averageMap_invariant u)
  have hs : (Real.sqrt cb : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hcb)
  refine ⟨ca, cb, hca, hcb, F, hFA, ?_⟩
  intro x hx y hy
  change star ((Real.sqrt cb : ℂ)⁻¹ • B (J x)) ⬝ᵥ
    ((Real.sqrt cb : ℂ)⁻¹ • B (J y)) = _
  rw [star_smul, smul_dotProduct, dotProduct_smul, hBinner _ (hmem x hx) _ (hmem y hy)]
  simp only [smul_eq_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← Complex.ofReal_sqrt_sq cb hcb.le, pow_two]
  have hscalar : (Real.sqrt cb : ℂ)⁻¹ *
      ((Real.sqrt cb : ℂ)⁻¹ * ((Real.sqrt cb : ℂ) * (Real.sqrt cb : ℂ) *
        (star (J x) ⬝ᵥ J y))) = star (J x) ⬝ᵥ J y := by field_simp
  rw [hscalar]
  exact hJ x hx y hy

end Local

section Graph
variable {G X V : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
  [Fintype V] [LinearOrder V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {P Q : V → Type*} [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
  [∀ v, Fintype (Q v)] [∀ v, DecidableEq (Q v)]

omit [∀ v, DecidableEq (P v)] [∀ v, DecidableEq (Q v)] in
/-- Local G-isometry alone supplies a global Hilbert-space isometry on the
actual product physical range, carrying one actual graph state to the other
with all positive site factors retained. Source: SCP10, Observations 6.4–6.6. -/
theorem exists_graphGIsometricPhysicalSupportTransport
    (ρ : (v : V) → Representation ℂ G ((IncidentEdge Γ v → X) → ℂ))
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → X) → Q v → ℂ)
    (ha : ∀ v, IsGIsometric (ρ v) (regularSiteMap (a v)))
    (hb : ∀ v, IsGIsometric (ρ v) (regularSiteMap (b v)))
    (hU : ∀ v g x y, star (ρ v g x) ⬝ᵥ ρ v g y = star x ⬝ᵥ y) :
    ∃ ca cb : V → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
      ∃ F : (v : V) → Matrix (Q v) (P v) ℂ,
        ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix'
            (graphPhysicalProductMap (fun v s η => a v η s)))).range →ₗᵢ[ℂ]
          EuclideanSpace ℂ ((v : V) → Q v),
          (∀ x, (I x).ofLp = graphPhysicalProductMap F x.val.ofLp) ∧
          I ⟨WithLp.toLp 2 (graphBondNetwork a),
              graphBondNetwork_mem_euclideanRange_productSiteMap a⟩ =
            WithLp.toLp 2 ((∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) •
              graphBondNetwork b) := by
  classical
  choose ca cb hca hcb F hFA hF using fun v =>
    (ha v).exists_physicalSupportTransport (hb v) (hU v)
  let M := fun v => LinearMap.toMatrix' (F v)
  have hgram (v : V) :
      (M v * (Matrix.of fun s η => a v η s)).conjTranspose *
          (M v * (Matrix.of fun s η => a v η s)) =
        (Matrix.of fun s η => a v η s).conjTranspose * (Matrix.of fun s η => a v η s) := by
    ext η ξ
    let T := Matrix.of fun s α => a v α s
    have hη : T.col η ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single η 1, Matrix.mulVec_single_one T η⟩
    have hξ : T.col ξ ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single ξ 1, Matrix.mulVec_single_one T ξ⟩
    change star ((M v * T).col η) ⬝ᵥ (M v * T).col ξ = star (T.col η) ⬝ᵥ T.col ξ
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col]
    simpa only [M, LinearMap.toMatrix'_mulVec] using hF v _ hη _ hξ
  have hglobal (ψ) (hψ : ψ ∈ (graphPhysicalProductMap (fun v s η => a v η s)).range)
      (φ) (hφ : φ ∈ (graphPhysicalProductMap (fun v s η => a v η s)).range) :=
    graphPhysicalProductMap_dotProduct_on_range M
      (fun v s η => a v η s) hgram ψ φ hψ hφ
  refine ⟨ca, cb, hca, hcb, M, coordinateSupportIsometry _ _ hglobal,
    coordinateSupportIsometry_apply _ _ hglobal, ?_⟩
  apply WithLp.ofLp_injective 2
  rw [coordinateSupportIsometry_apply, graphPhysicalProductMap_graphBondNetwork]
  have hcoeff (v : V) (η : IncidentEdge Γ v → X) (s : Q v) :
      (∑ t : P v, M v s t * a v η t) =
        ((Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) * b v η s := by
    have h := congrArg (fun T => LinearMap.toMatrix' T s η) (hFA v)
    simp only [LinearMap.toMatrix'_comp, map_smul, toMatrix_regularSiteMap] at h
    exact h
  simp_rw [hcoeff]
  ext σ
  simp only [graphBondNetwork, Finset.prod_mul_distrib, ← Finset.mul_sum,
    Pi.smul_apply, smul_eq_mul]

end Graph
end TNLean.PEPS

end

end GraphGIsometricSupportTransport

section GraphInsertedPhysicalSupport

open ManyBody (Edge)

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {P Q : V → Type*} [∀ v, Fintype (P v)] [∀ v, Fintype (Q v)]

omit [DecidableEq X] [∀ v, Fintype (Q v)] in
/-- Products of physical maps commute with arbitrary inserted bond matrices.
Source: SCP10, physical accessibility, Observation 6.4. -/
theorem graphPhysicalProductMap_graphInsertedBondNetwork
    (F : (v : V) → Matrix (Q v) (P v) ℂ)
    (K : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) :
    graphPhysicalProductMap F (graphInsertedBondNetwork K a) =
      graphInsertedBondNetwork K (fun v η τ => ∑ s : P v, F v τ s * a v η s) := by
  classical
  ext τ
  simp only [graphPhysicalProductMap, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    graphPhysicalProductMatrix, graphInsertedBondNetwork, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ζ _
  simp_rw [← mul_assoc, mul_comm (∏ v, F v (τ v) _), mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : V) (s : P v) =>
    F v (τ v) s * a v (graphSiteBondEndpointEquiv.symm ζ v) s)).symm

omit [DecidableEq X] [∀ v, Fintype (P v)] [∀ v, Fintype (Q v)] in
/-- Every inserted state is in the full product of local tensor-map ranges.
Source: SCP10, physical accessibility, Observation 6.4. -/
theorem graphInsertedBondNetwork_mem_range_productSiteMap
    (K : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) :
    graphInsertedBondNetwork K a ∈ LinearMap.range
      (graphPhysicalProductMap (fun v s η => a v η s)) := by
  classical
  refine ⟨∑ ζ : Edge Γ → X × X,
    (∏ e, K e (ζ e).1 (ζ e).2) • Pi.single (graphSiteBondEndpointEquiv.symm ζ) 1, ?_⟩
  simp only [map_sum, map_smul, graphPhysicalProductMap, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one]
  ext σ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    graphPhysicalProductMatrix, graphInsertedBondNetwork]

omit [∀ v, Fintype (P v)] [∀ v, Fintype (Q v)] in
/-- Hilbert-space version of the inserted-state support membership.
Source: SCP10, physical accessibility, Observation 6.4. -/
theorem graphInsertedBondNetwork_mem_euclideanRange_productSiteMap
    (K : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) :
    WithLp.toLp 2 (graphInsertedBondNetwork K a) ∈
      (Matrix.toEuclideanLin (LinearMap.toMatrix'
        (graphPhysicalProductMap (fun v s η => a v η s)))).range := by
  obtain ⟨x, hx⟩ := graphInsertedBondNetwork_mem_range_productSiteMap K a
  refine ⟨WithLp.toLp 2 x, ?_⟩
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    LinearMap.toMatrix'_mulVec] using congrArg (WithLp.toLp 2) hx

variable {G : Type*} [Group G] [Finite G]

/-- One block-local support isometry transports all inserted contractions at
once. The factors and local matrices are chosen before the bond operators.
Source: SCP10, Observations 6.4–6.6. -/
theorem exists_graphGIsometricInsertedPhysicalSupportTransport
    (ρ : (v : V) → Representation ℂ G ((IncidentEdge Γ v → X) → ℂ))
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → X) → Q v → ℂ)
    (ha : ∀ v, IsGIsometric (ρ v) (regularSiteMap (a v)))
    (hb : ∀ v, IsGIsometric (ρ v) (regularSiteMap (b v)))
    (hU : ∀ v g x y, star (ρ v g x) ⬝ᵥ ρ v g y = star x ⬝ᵥ y) :
    ∃ ca cb : V → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
      ∃ F : (v : V) → Matrix (Q v) (P v) ℂ,
        ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix'
            (graphPhysicalProductMap (fun v s η => a v η s)))).range →ₗᵢ[ℂ]
          EuclideanSpace ℂ ((v : V) → Q v),
          (∀ x, (I x).ofLp = graphPhysicalProductMap F x.val.ofLp) ∧
          ∀ K : Edge Γ → Matrix X X ℂ,
            I ⟨WithLp.toLp 2 (graphInsertedBondNetwork K a),
                graphInsertedBondNetwork_mem_euclideanRange_productSiteMap K a⟩ =
              WithLp.toLp 2 ((∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) •
                graphInsertedBondNetwork K b) := by
  classical
  choose ca cb hca hcb F hFA hF using fun v =>
    (ha v).exists_physicalSupportTransport (hb v) (hU v)
  let M := fun v => LinearMap.toMatrix' (F v)
  have hgram (v : V) :
      (M v * (Matrix.of fun s η => a v η s)).conjTranspose *
          (M v * (Matrix.of fun s η => a v η s)) =
        (Matrix.of fun s η => a v η s).conjTranspose * (Matrix.of fun s η => a v η s) := by
    ext η ξ
    let T := Matrix.of fun s α => a v α s
    have hη : T.col η ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single η 1, Matrix.mulVec_single_one T η⟩
    have hξ : T.col ξ ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single ξ 1, Matrix.mulVec_single_one T ξ⟩
    change star ((M v * T).col η) ⬝ᵥ (M v * T).col ξ = star (T.col η) ⬝ᵥ T.col ξ
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col]
    simpa only [M, LinearMap.toMatrix'_mulVec] using hF v _ hη _ hξ
  have hglobal (ψ) (hψ : ψ ∈ (graphPhysicalProductMap (fun v s η => a v η s)).range)
      (φ) (hφ : φ ∈ (graphPhysicalProductMap (fun v s η => a v η s)).range) :=
    graphPhysicalProductMap_dotProduct_on_range M
      (fun v s η => a v η s) hgram ψ φ hψ hφ
  refine ⟨ca, cb, hca, hcb, M, coordinateSupportIsometry _ _ hglobal,
    coordinateSupportIsometry_apply _ _ hglobal, ?_⟩
  intro K
  apply WithLp.ofLp_injective 2
  rw [coordinateSupportIsometry_apply, graphPhysicalProductMap_graphInsertedBondNetwork]
  have hcoeff (v : V) (η : IncidentEdge Γ v → X) (s : Q v) :
      (∑ t : P v, M v s t * a v η t) =
        ((Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) * b v η s := by
    have h := congrArg (fun T => LinearMap.toMatrix' T s η) (hFA v)
    simp only [LinearMap.toMatrix'_comp, map_smul, toMatrix_regularSiteMap] at h
    exact h
  simp_rw [hcoeff]
  ext σ
  simp only [graphInsertedBondNetwork, Finset.prod_mul_distrib,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm _ (∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)),
    mul_assoc]
  rw [← Finset.mul_sum]

end TNLean.PEPS

end

end GraphInsertedPhysicalSupport
