/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NativeTorusClosures
import TNLean.PEPS.ParentHamiltonian.TorusDependentParentSeamCuts

/-!
# Native nonuniform parent vectors are spanned by commuting closures

The existing microscopic plaquette constraints produce a coherent bond
expansion with flat support. Each flat term is reduced by its actual local
averages to a native commuting closure. The genuine physical site maps then
recover the entire parent vector. Every edge representation and every site
tensor may differ; no cut, support, flatness, or spanning premise is supplied.

Source: SCP10, arXiv:1001.3807, Theorems 5.5 and 5.7. Both native simple-graph
torus periods are at least three.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS
open DependentBondNetwork

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Fintype G] {d : ℕ}

/-- The actual canonical projection of each flat dependent-bond term is one
native commuting closure, with the source's vertical and horizontal orientations. -/
theorem averagingProjector_flat_bondProduct_eq_nativeClosure (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (p : Edge Γₜ → G)
    (hp : IsTorusFlat (torusNativeRightTransport p) (torusNativeUpTransport p)) :
    ∃ g h : G, Commute g h ∧
      averagingProjector graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
        (representationBondProduct graphEdgeTail graphEdgeHead (graphBondAlphabet A) U p) =
      NativeTorus.closure (graphBondAlphabet A) U
        (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
        g h := by
  obtain ⟨k, g, h, hgh, hk⟩ := exists_regularVertexGauge_eq_torusClosure p hp
  refine ⟨g, h, hgh, ?_⟩
  change averagingProjector _ _ _ _ (matrixBondProduct _ _ _ _) = _
  rw [averagingProjector_matrixBondProduct]
  funext σ
  change network _ _ _ (DependentBondNetwork.averagingSite _ _ _ U) _ σ =
    network _ _ _ (DependentBondNetwork.averagingSite _ _ _ U) _ σ
  rw [← hk]
  simpa only [regularVertexGaugeOperators, graphEdgeHead, graphEdgeTail, inv_inv] using
    (network_averagingSite_vertexGauge graphEdgeTail graphEdgeHead
      (graphBondAlphabet A) U p (fun v ↦ (k v)⁻¹) σ).symm

omit [Fintype G] in
/-- Every vector in the existing microscopic plaquette parent space is a linear
combination of its actual commuting native closures. Bond dimensions and
semi-regular representations are independent, as are the G-injective tensors.
Source: the spanning assertion of SCP10, Theorem 5.7. -/
theorem torusPlaquetteParentGroundSpace_le_nativeCommutingClosureSpan [Finite G]
    (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v)) :
    regionParentGroundSpace A torusPlaquetteRegion ≤
      NativeTorus.commutingClosureSpan (graphBondAlphabet A) U (graphDependentTensor A) := by
  classical
  let := Fintype.ofFinite G
  intro ψ hψ
  obtain ⟨ξ, hcuts, hrec, hexpand, hsupport⟩ := exists_regionParent_bondCoefficients
    A U hU hA (0 : X) torusPlaquetteRegion
    (fun v ↦ ⟨v, mem_torusPlaquetteRegion_self v⟩)
    exists_torusPlaquetteRegion_contains_edge hψ
  have hfixed : averagingProjector graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U) ξ = ξ := by
    obtain ⟨M, hM⟩ := hcuts 0
    rw [← hM]
    exact averagingProjector_cutMap _ _ _ _ _ M
  have hspan : ξ ∈ NativeTorus.commutingClosureSpan (graphBondAlphabet A) U
      (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U) := by
    rw [← hfixed, hexpand, map_sum]
    apply Submodule.sum_mem
    intro p _
    rw [map_smul]
    by_cases hn : bondCoefficientExtraction graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        U p ξ = 0
    · rw [hn, zero_smul]
      exact Submodule.zero_mem _
    apply Submodule.smul_mem
    have hp : IsTorusFlat (torusNativeRightTransport p) (torusNativeUpTransport p) := by
      intro v
      apply (torusPlaquetteHolonomy_eq_one_iff_squareTransport p v).mp
      obtain ⟨q, hq⟩ := hsupport p hn v
      exact regularWalkHolonomy_eq_one_of_region (torusPlaquetteRegion v) p q hq
        (torusPlaquetteWalk v) (fun x hx ↦ List.mem_toFinset.mpr hx)
    obtain ⟨g, h, hgh, heq⟩ := averagingProjector_flat_bondProduct_eq_nativeClosure A U p hp
    rw [heq]
    exact Submodule.subset_span ⟨⟨(g, h), hgh⟩, rfl⟩
  have hmap : ψ ∈ (NativeTorus.commutingClosureSpan (graphBondAlphabet A) U
      (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)).map
      (dependentPhysicalProductFamilyMap (fun v ↦ LinearMap.toMatrix'
        (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
          (graphDependentTensor A) v))) :=
    ⟨ξ, hspan, hrec⟩
  rwa [NativeTorus.map_commutingClosureSpan_recover (graphBondAlphabet A) U
    (graphDependentTensor A) (fun v ↦ (hA v).invariant)] at hmap

end TNLean.PEPS
