/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentBondCoefficients
import TNLean.PEPS.ParentHamiltonian.TorusRegularParentCoordinates
import TNLean.PEPS.ParentHamiltonian.TorusParentFlatness
import TNLean.PEPS.RegionBondGaugeHolonomy
import TNLean.PEPS.TorusGraphSeamGauge
import TNLean.PEPS.DependentOpenCutIntersection

/-!
# Microscopic plaquette parent membership gives actual native seam cuts

Every vector in the existing positive plaquette-parent kernel belongs to the
actual correlated-boundary range at any chosen pair of native torus seams.
Each original bond has its own dimension and matching semi-regular representation,
and each vertex has its own G-injective tensor. No cut-range, flatness, coefficient
expansion, or closure-spanning hypothesis is supplied.

The proof obtains coherent canonical bond coefficients from actual local parent
constraints. Their nonzero labels are gradients on every plaquette, hence flat.
A group-valued tree gauge removes a flat labeling off either selected seam.
Projecting the coherent expansion gives genuine joint seam boundaries, and the
original tensors recover the physical vector.

Source: SCP10, arXiv:1001.3807, Theorems 5.4 and 5.5. This direct native proof
retains all microscopic sites. The existing simple-graph parent framework has
both periods at least three and one physical alphabet; no identification with
a four-block nonuniform-physical parent is asserted here.
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

/-- A flat coherent bond term, after the actual local averages, has a literal
joint boundary on any selected pair of microscopic seams. -/
theorem averagingProjector_bondProduct_mem_graphSeamCut (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (p : Edge Γₜ → G)
    (hp : IsTorusFlat (torusNativeRightTransport p) (torusNativeUpTransport p))
    (c : ZMod width) (r : ZMod height) :
    averagingProjector graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
      (representationBondProduct graphEdgeTail graphEdgeHead (graphBondAlphabet A) U p) ∈
        cutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
          (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
          (torusGraphSeamCut c r) := by
  change averagingProjector _ _ _ _ (matrixBondProduct _ _ _ _) ∈ _
  rw [averagingProjector_matrixBondProduct]
  change network _ _ _ (DependentBondNetwork.averagingSite _ _ _ U) _ ∈ _
  obtain ⟨q, hq⟩ := exists_vertexGauge_off_torusGraphSeamCut p hp c r
  rw [← funext (network_averagingSite_vertexGauge
    graphEdgeTail graphEdgeHead (graphBondAlphabet A) U p q)]
  apply network_mem_cutSpace_of_eq_one
  intro e he
  change U e (q e.1.2 * p e * (q e.1.1)⁻¹) = 1
  rw [hq e he, map_one]

omit [Fintype G] in
/-- Actual microscopic plaquette constraints force membership in every genuine
native seam-cut range for independently represented bonds and unrelated site tensors. -/
theorem torusPlaquetteParentGroundSpace_le_graphSeamCut [Finite G] (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v))
    (c : ZMod width) (r : ZMod height) :
    regionParentGroundSpace A torusPlaquetteRegion ≤
      cutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (graphDependentTensor A) (torusGraphSeamCut c r) := by
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
  have hseam : ξ ∈ cutSpace graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
      (torusGraphSeamCut c r) := by
    rw [← hfixed, hexpand, map_sum]
    apply Submodule.sum_mem
    intro p _
    rw [map_smul]
    by_cases hn : bondCoefficientExtraction graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        U p ξ = 0
    · rw [hn, zero_smul]
      exact Submodule.zero_mem _
    apply Submodule.smul_mem
    apply averagingProjector_bondProduct_mem_graphSeamCut A U p _ c r
    intro v
    apply (torusPlaquetteHolonomy_eq_one_iff_squareTransport p v).mp
    obtain ⟨q, hq⟩ := hsupport p hn v
    exact regularWalkHolonomy_eq_one_of_region (torusPlaquetteRegion v) p q hq
      (torusPlaquetteWalk v) (fun x hx ↦ List.mem_toFinset.mpr hx)
  obtain ⟨M, hM⟩ := hseam
  change cutMap graphEdgeTail graphEdgeHead (graphBondAlphabet A)
    (representationAveragingSite graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U))
      (torusGraphSeamCut c r) M = ξ at hM
  refine ⟨M, ?_⟩
  rw [← cutMap_recover_representationAveragingSite graphEdgeTail graphEdgeHead
    (graphBondAlphabet A)
    (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U)
    (graphDependentTensor A) (fun v ↦ (hA v).invariant) (torusGraphSeamCut c r) M, hM]
  exact hrec

omit [Fintype G] in
/-- Every vector in the full positive microscopic plaquette-parent kernel has
an actual correlated boundary at each chosen pair of native seams. -/
theorem exists_graphSeamBoundary_of_mem_torusPlaquetteParentKernel [Finite G] (A : Tensor Γₜ d)
    (U : (e : Edge Γₜ) → G →* Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (hA : ∀ v, IsGInjective
      (incidentRepresentation graphEdgeTail graphEdgeHead (graphBondAlphabet A) U v)
      (localSiteMap graphEdgeTail graphEdgeHead (graphBondAlphabet A) (graphDependentTensor A) v))
    (H : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hH : ∀ v, IsRegionParentInteraction A (torusPlaquetteRegion v) (H v))
    {ψ : (X → Fin d) → ℂ}
    (hψ : ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker)
    (c : ZMod width) (r : ZMod height) :
    ∃ M : CutConfig (torusGraphSeamCut c r) (graphBondAlphabet A) → ℂ,
      ∀ σ, cutCoeff graphEdgeTail graphEdgeHead (graphBondAlphabet A)
        (graphDependentTensor A) (torusGraphSeamCut c r) M σ = ψ σ := by
  rw [ker_regionParentHamiltonian A torusPlaquetteRegion H hH] at hψ
  exact (mem_cutSpace_iff _ _ _ _ _ _).mp
    (torusPlaquetteParentGroundSpace_le_graphSeamCut A U hU hA c r hψ)

end TNLean.PEPS
