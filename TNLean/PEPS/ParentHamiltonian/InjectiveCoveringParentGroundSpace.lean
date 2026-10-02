/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionVertexImageSupport
import TNLean.PEPS.ParentHamiltonian.VertexBondRegionConstraint
import TNLean.PEPS.ParentHamiltonian.VertexBondState

/-!
# Uniqueness for covering parent regions of injective PEPS

Let the site tensors be injective. If the parent regions cover every
vertex and contain the two endpoints of every edge, their common
regional space is exactly the span of the actual closed PEPS vector.
The proof reconstructs physical vectors from their genuine local
conditions and then enforces each independent virtual Bell bond.

Source: the virtual-pair uniqueness argument of CPGSV21,
arXiv:2011.12127, Section IV.C.1, lines 2017–2044.
This is its finite-graph covering-region consequence.

**Local fix (physical reconstruction):** The site-image conditions are
derived from vertex coverage, rather than inferred from bare inverse-adjoint
congruence. Isolated vertices must occur in some region. See
`docs/paper-gaps/cpgsv21_injective_parent_reconstruction.tex`.
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The global product site map sends the true virtual Bell product to
the actual closed coefficient vector. Source: CPGSV21,
Section IV.C.1, equation `eq:4:peps-as-peps`, lines 2017–2028. -/
theorem globalVertexTensorMap_virtualBondProduct (A : Tensor Γ d) :
    globalVertexTensorMap A
      ((fullRegionVertexVectorEquivEdgePair A).symm (virtualBondProduct A.bondDim)) =
        stateCoeff A := by
  change (fullRegionPhysicalEquiv d).symm
    (fullRegionVertexTensorMapEdgePairs A (virtualBondProduct A.bondDim)) = _
  rw [fullRegionVertexTensorMapEdgePairs_virtualBondProduct, LinearEquiv.symm_apply_apply]

/-- Injective site tensors and actual regional conditions covering every
vertex and every edge determine exactly the closed PEPS line. Bond
dimensions may vanish; the resulting span may then be zero.
Source: finite-graph covering-region consequence of CPGSV21,
Section IV.C.1, the virtual-pair uniqueness argument, lines 2017–2044. -/
theorem regionParentGroundSpace_eq_span_of_isVertexInjective_of_cover
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ι : Type*} (R : ι → Finset V)
    (hvertices : ∀ v, ∃ i, v ∈ R i)
    (hedges : ∀ e : Edge Γ, ∃ i, e.1.1 ∈ R i ∧ e.1.2 ∈ R i) :
    regionParentGroundSpace A R = Submodule.span ℂ {stateCoeff A} := by
  apply le_antisymm
  · intro ψ hψ
    rw [← vertexVirtualParentGroundSpace_map_globalVertexTensorMap_of_cover
      A hA R hvertices] at hψ
    obtain ⟨x, hx, rfl⟩ := hψ
    have hBell := edgePair_mem_virtualBondGroundSpace_of_vertexVirtualParentGroundSpace
      A R hedges hx
    rw [virtualBondGroundSpace_eq_span] at hBell
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hBell
    have hrec : c • (fullRegionVertexVectorEquivEdgePair A).symm
        (virtualBondProduct A.bondDim) = x := by
      apply (fullRegionVertexVectorEquivEdgePair A).injective
      simpa only [map_smul, LinearEquiv.apply_symm_apply] using hc
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [← hrec, map_smul, globalVertexTensorMap_virtualBondProduct]
  · exact Submodule.span_le.mpr
      (Set.singleton_subset_iff.mpr (stateCoeff_mem_regionParentGroundSpace A R))

/-- Arbitrary positive interactions with the genuine regional kernels
have exactly the closed PEPS span as their common zero-energy space.
Source: covering-region consequence of CPGSV21,
Section IV.C.1, regional parents and the injective uniqueness argument,
lines 2003–2044. -/
theorem ker_regionParentHamiltonian_eq_span_of_isVertexInjective_of_cover
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ι : Type*} [Fintype ι]
    (R : ι → Finset V) (hvertices : ∀ v, ∃ i, v ∈ R i)
    (hedges : ∀ e : Edge Γ, ∃ i, e.1.1 ∈ R i ∧ e.1.2 ∈ R i)
    (H : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (R i) (H i)) :
    (Matrix.mulVecLin (regionParentHamiltonian R H)).ker =
      Submodule.span ℂ {stateCoeff A} := by
  rw [ker_regionParentHamiltonian A R H hH,
    regionParentGroundSpace_eq_span_of_isVertexInjective_of_cover A hA R hvertices hedges]

/-- Positive bond dimensions give a one-dimensional parent ground space
for an injective family on a vertex- and edge-covering collection.
Source: covering-region form of the injective uniqueness argument of
CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem finrank_regionParentGroundSpace_eq_one_of_isVertexInjective_of_cover
    (A : Tensor Γ d) (hA : IsVertexInjective A) {ι : Type*} (R : ι → Finset V)
    (hvertices : ∀ v, ∃ i, v ∈ R i)
    (hedges : ∀ e : Edge Γ, ∃ i, e.1.1 ∈ R i ∧ e.1.2 ∈ R i)
    (hD : ∀ e, 0 < A.bondDim e) : Module.finrank ℂ (regionParentGroundSpace A R) = 1 := by
  rw [regionParentGroundSpace_eq_span_of_isVertexInjective_of_cover A hA R hvertices hedges]
  exact finrank_span_singleton
    ((stateCoeff_ne_zero_iff_bondDim_pos_of_isVertexInjective A hA).mpr hD)

end TNLean.PEPS
