/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusNativeOrientation
import TNLean.PEPS.GraphOrientedGInjective
import TNLean.PEPS.TorusOperatorString
import TNLean.Algebra.FinTupleEquiv

/-!
# Native four-leg symmetry and oriented graph G-injectivity

The explicit native right/down edge orientation reproduces the source's
incoming top/left and outgoing right/down action for arbitrary matrix
representations, not just regular permutation matrices.
Source: SCP10, Definition 5.1 and Theorem 5.7.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G X : Type*} [Group G] [Fintype X] [DecidableEq X]

/-- The oriented incident matrix is exactly the native four-leg matrix in
actual top/right/down/left coordinates. -/
theorem graphOrientedIncidentMatrix_torus (U : G →* Matrix X X ℂ)
    (v : TorusVertex width height) (g : G)
    (σ η : IncidentEdge (torusGraph width height) v → X) :
    graphOrientedIncidentMatrix U torusNativeEdgeFlip v g σ η =
      torusLegMatrix U g (torusIncidentCoordinates v σ) (torusIncidentCoordinates v η) := by
  unfold graphOrientedIncidentMatrix
  rw [← (torusIncidentLegEquiv v).prod_comp]
  change (∏ i : Fin 4, if graphNativeTail torusNativeEdgeFlip v (torusIncidentLeg v i) then
    U g⁻¹ (η (torusIncidentLeg v i)) (σ (torusIncidentLeg v i)) else
    U g (σ (torusIncidentLeg v i)) (η (torusIncidentLeg v i))) = _
  simp only [graphNativeTail_torus_leg_iff]
  simp [Fin.prod_univ_four, torusIncidentLeg,
    torusLegMatrix, torusLegKernel_apply, torusIncidentCoordinates, mul_assoc]

/-- The native four-leg configuration, in top, right, down, left order.
Source: SCP10, Definition 5.1. -/
def torusNativeIncidentCoordinatesEquiv (v : TorusVertex width height) :
    (IncidentEdge (torusGraph width height) v → X) ≃ X × X × X × X :=
  ((torusIncidentLegEquiv v).symm.arrowCongr (Equiv.refl X)).trans (finFourArrowEquiv X)

omit [Fintype X] [DecidableEq X] in
/-- The configuration equivalence reads the four actual native legs. -/
@[simp]
theorem torusNativeIncidentCoordinatesEquiv_apply (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → X) :
    torusNativeIncidentCoordinatesEquiv v η = torusIncidentCoordinates v η := rfl

/-- A native site expressed on its actual incident graph edges. The virtual
alphabet need not carry a group structure. Source: SCP10, Definition 5.1. -/
def torusNativeIncidentSite {d : ℕ} (a : X → X → X → X → Fin d → ℂ)
    (v : TorusVertex width height) (η : IncidentEdge (torusGraph width height) v → X)
    (s : Fin d) : ℂ :=
  a (η (torusTopLeg v)) (η (torusRightLeg v))
    (η (torusDownLeg v)) (η (torusLeftLeg v)) s

/-- The oriented graph action intertwines the native four-leg action under
actual incident coordinates. Source: SCP10, Definition 5.1(i). -/
theorem graphOrientedIncidentRepresentation_torus (U : G →* Matrix X X ℂ)
    (v : TorusVertex width height) (g : G)
    (x : (IncidentEdge (torusGraph width height) v → X) → ℂ) :
    (graphOrientedIncidentRepresentation U torusNativeEdgeFlip v g x) ∘
        (torusNativeIncidentCoordinatesEquiv v).symm =
      torusLegRep U g (x ∘ (torusNativeIncidentCoordinatesEquiv v).symm) := by
  classical
  let e := torusNativeIncidentCoordinatesEquiv (X := X) v
  funext θ
  simp only [Function.comp_apply, graphOrientedIncidentRepresentation_apply,
    torusLegRep_apply, Matrix.mulVec, dotProduct, graphOrientedIncidentMatrix_torus]
  change (∑ η, torusLegMatrix U g (e (e.symm θ)) (e η) * x η) =
    ∑ ζ, torusLegMatrix U g θ ζ * x (e.symm ζ)
  rw [e.apply_symm_apply]
  simpa only [e.symm_apply_apply] using
    Equiv.sum_comp e (fun ζ => torusLegMatrix U g θ ζ * x (e.symm ζ))

omit [DecidableEq X] in
/-- Native and incident site maps agree by reindexing the virtual sum.
Source: SCP10, Definition 5.1. -/
theorem regularSiteMap_torusNativeIncidentSite_eq_siteMap {d : ℕ}
    (a : X → X → X → X → Fin d → ℂ) (v : TorusVertex width height)
    (x : (IncidentEdge (torusGraph width height) v → X) → ℂ) :
    regularSiteMap (torusNativeIncidentSite a v) x =
      siteMap a (x ∘ (torusNativeIncidentCoordinatesEquiv v).symm) := by
  classical
  ext s
  change (∑ η, torusNativeIncidentSite a v η s * x η) =
    ∑ θ : X × X × X × X, a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s *
      x ((torusNativeIncidentCoordinatesEquiv v).symm θ)
  have h := Equiv.sum_comp (torusNativeIncidentCoordinatesEquiv (X := X) v)
    (fun θ : X × X × X × X => a θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 s *
      x ((torusNativeIncidentCoordinatesEquiv v).symm θ))
  simp only [Equiv.symm_apply_apply] at h
  simpa only [Equiv.symm_apply_apply, torusNativeIncidentCoordinatesEquiv_apply,
    torusIncidentCoordinates, torusNativeIncidentSite] using h

/-- Native four-leg G-injectivity gives G-injectivity on the actual oriented
incident edges, for any finite virtual alphabet. Source: SCP10, Definition 5.1. -/
theorem IsGInjective.isGInjective_torusNativeIncidentSite {d : ℕ}
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (v : TorusVertex width height) :
    IsGInjective (graphOrientedIncidentRepresentation U torusNativeEdgeFlip v)
      (regularSiteMap (torusNativeIncidentSite a v)) := by
  classical
  let e := torusNativeIncidentCoordinatesEquiv (X := X) v
  refine ⟨?_, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, regularSiteMap_torusNativeIncidentSite_eq_siteMap]
    rw [graphOrientedIncidentRepresentation_torus]
    exact LinearMap.congr_fun (ha.invariant g) (x ∘ e.symm)
  · intro x hx hzero
    have hy : x ∘ e.symm ∈ (torusLegRep U).invariants := by
      intro g
      rw [← graphOrientedIncidentRepresentation_torus, hx g]
    have hz := ha.injOn_invariants (x ∘ e.symm) hy
      (by simpa only [regularSiteMap_torusNativeIncidentSite_eq_siteMap] using hzero)
    exact e.symm.surjective.injective_comp_right hz

omit [DecidableEq X] in
/-- The actual numbered graph tensor map is the incident site map after
virtual bond numbering. Source: SCP10, Definition 5.1. -/
theorem localTensorMap_torusNativeIncidentSite {d : ℕ}
    (a : X → X → X → X → Fin d → ℂ) (v : TorusVertex width height) :
    localTensorMap (groupBondTensor (torusNativeIncidentSite a)) v =
      regularSiteMap (torusNativeIncidentSite a v) ∘ₗ
        (graphNumberedVirtualCoeffEquiv X v).toLinearMap := by
  classical
  apply LinearMap.ext
  intro x
  funext s
  simp only [localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change (∑ η : IncidentEdge (torusGraph width height) v → Fin (Fintype.card X),
      x η * torusNativeIncidentSite a v
        (fun f => (Fintype.equivFin X).symm (η f)) s) =
    ∑ ξ : IncidentEdge (torusGraph width height) v → X,
      torusNativeIncidentSite a v ξ s * x (fun f => Fintype.equivFin X (ξ f))
  have h := Equiv.sum_comp
    (graphNumberedVirtualConfigEquiv (Γ := torusGraph width height) X v).symm
    (fun η : IncidentEdge (torusGraph width height) v → Fin (Fintype.card X) =>
      x η * torusNativeIncidentSite a v
        (fun f => (Fintype.equivFin X).symm (η f)) s)
  have hequiv (ξ : IncidentEdge (torusGraph width height) v → X) :
      (graphNumberedVirtualConfigEquiv (Γ := torusGraph width height) X v).symm ξ =
        fun f => Fintype.equivFin X (ξ f) := rfl
  simpa only [hequiv, Equiv.symm_apply_apply, mul_comm] using h.symm

set_option maxHeartbeats 800000 in
-- Reducing the dependent numbered torus virtual spaces requires additional heartbeats.
/-- Native four-leg G-injectivity directly implies G-injectivity of the actual
numbered graph tensor with the native right/down orientation. No range or
kernel equality, isometry, or group structure on the virtual alphabet is assumed.
Source: SCP10, Definition 5.1 and Theorem 5.7. -/
theorem IsGInjective.isGInjective_torusNativeIncidentTensor {d : ℕ}
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (v : TorusVertex width height) :
    IsGInjective (graphOrientedNumberedIncidentRepresentation U torusNativeEdgeFlip v)
      (localTensorMap (groupBondTensor (torusNativeIncidentSite a)) v) := by
  classical
  rw [localTensorMap_torusNativeIncidentSite]
  let E := graphNumberedVirtualCoeffEquiv (Γ := torusGraph width height) X v
  have hT := ha.isGInjective_torusNativeIncidentSite v
  refine ⟨?_, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    change regularSiteMap (torusNativeIncidentSite a v)
        (E (E.symm (graphOrientedIncidentRepresentation U torusNativeEdgeFlip v g (E x)))) =
      regularSiteMap (torusNativeIncidentSite a v) (E x)
    rw [E.apply_symm_apply]
    exact LinearMap.congr_fun (hT.invariant g) (E x)
  · intro x hx hzero
    have hmem : E x ∈ (graphOrientedIncidentRepresentation U torusNativeEdgeFlip v).invariants := by
      intro g
      have heq := congrArg E (hx g)
      change E (E.symm (graphOrientedIncidentRepresentation U torusNativeEdgeFlip v g (E x))) =
        E x at heq
      simpa only [E.apply_symm_apply] using heq
    apply E.injective
    rw [map_zero]
    exact hT.injOn_invariants (E x) hmem hzero

end TNLean.PEPS
