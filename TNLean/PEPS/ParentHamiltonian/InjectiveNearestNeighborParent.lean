/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.InjectiveCoveringParentGroundSpace

/-!
# Nearest-neighbor parents of injective PEPS

Edge-pair regions cover every vertex when the graph has no isolated vertices.
On an arbitrary finite graph, add singleton regions at precisely the isolated
vertices. Both families then give the actual closed PEPS span as their common
regional space, and as the kernel of every positive exact-kernel parent family.

Source: CPGSV21, arXiv:2011.12127, Section IV.C.1, the nearest-neighbor
virtual-pair uniqueness argument, lines 2017–2044.

**Local fix (isolated vertices):** Edge interactions do not constrain an
isolated site's unused physical directions. The edge-only statements assume
that every vertex has a neighbor; the unrestricted graph statements include
isolated-site singleton parents. See
`docs/paper-gaps/cpgsv21_injective_parent_reconstruction.tex`.
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The two endpoints of an actual graph edge. Source: the nearest-neighbor
regions in CPGSV21, Section IV.C.1, lines 2032–2044. -/
def edgePairRegion (e : Edge Γ) : Finset V := {e.1.1, e.1.2}

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Every edge is covered by its own endpoint region. -/
theorem edgePairRegion_covers_edges (e : Edge Γ) :
    ∃ f : Edge Γ, e.1.1 ∈ edgePairRegion f ∧ e.1.2 ∈ edgePairRegion f := by
  exact ⟨e, by simp [edgePairRegion], by simp [edgePairRegion]⟩

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- An adjacent vertex belongs to the corresponding unordered endpoint region. -/
theorem mem_edgePairRegion_of_adj {v w : V} (h : Γ.Adj v w) :
    v ∈ edgePairRegion (Edge.ofAdj h) := by
  rcases Edge.ofAdj_endpoints h with h | h <;> simp [edgePairRegion, h.1, h.2]

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Edge-pair regions cover the vertices if every vertex has a neighbor. -/
theorem edgePairRegion_covers_vertices
    (hneighbors : ∀ v, ∃ w, Γ.Adj v w) : ∀ v, ∃ e : Edge Γ, v ∈ edgePairRegion e := by
  intro v
  obtain ⟨w, h⟩ := hneighbors v
  exact ⟨Edge.ofAdj h, mem_edgePairRegion_of_adj h⟩

/-- Edge-pair regions together with singleton regions at isolated vertices.
Source: the graph parent construction of CPGSV21, Section IV.C.1,
lines 2003–2044, with the isolated-site coverage convention above. -/
def edgeAndIsolatedRegion : Edge Γ ⊕ {v : V // ¬ ∃ w, Γ.Adj v w} → Finset V
  | .inl e => edgePairRegion e
  | .inr v => {v.1}

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Edge-pair and isolated-site regions cover every vertex of an arbitrary graph. -/
theorem edgeAndIsolatedRegion_covers_vertices :
    ∀ v, ∃ i, v ∈ edgeAndIsolatedRegion (Γ := Γ) i := by
  classical
  intro v
  by_cases h : ∃ w, Γ.Adj v w
  · obtain ⟨w, hw⟩ := h
    exact ⟨Sum.inl (Edge.ofAdj hw), mem_edgePairRegion_of_adj hw⟩
  · exact ⟨Sum.inr ⟨v, h⟩, Finset.mem_singleton_self v⟩

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Every edge is covered by the edge-pair part of the augmented family. -/
theorem edgeAndIsolatedRegion_covers_edges (e : Edge Γ) :
    ∃ i, e.1.1 ∈ edgeAndIsolatedRegion (Γ := Γ) i ∧
      e.1.2 ∈ edgeAndIsolatedRegion (Γ := Γ) i := by
  exact ⟨Sum.inl e, by simp [edgeAndIsolatedRegion, edgePairRegion],
    by simp [edgeAndIsolatedRegion, edgePairRegion]⟩

/-- Without isolated vertices, actual nearest-neighbor regional conditions
select exactly the closed injective PEPS span. Source: CPGSV21,
Section IV.C.1, the nearest-neighbor uniqueness argument, lines 2032–2044. -/
theorem regionParentGroundSpace_edgePairs_eq_span
    (A : Tensor Γ d) (hA : IsVertexInjective A)
    (hneighbors : ∀ v, ∃ w, Γ.Adj v w) :
    regionParentGroundSpace A (edgePairRegion (Γ := Γ)) = Submodule.span ℂ {stateCoeff A} :=
  regionParentGroundSpace_eq_span_of_isVertexInjective_of_cover A hA edgePairRegion
    (edgePairRegion_covers_vertices hneighbors) edgePairRegion_covers_edges

/-- Positive bonds give a one-dimensional nearest-neighbor parent space
on a graph without isolated vertices. Source: CPGSV21, Section IV.C.1,
the nearest-neighbor uniqueness argument, lines 2032–2044. -/
theorem finrank_regionParentGroundSpace_edgePairs_eq_one
    (A : Tensor Γ d) (hA : IsVertexInjective A)
    (hneighbors : ∀ v, ∃ w, Γ.Adj v w) (hD : ∀ e, 0 < A.bondDim e) :
    Module.finrank ℂ (regionParentGroundSpace A (edgePairRegion (Γ := Γ))) = 1 :=
  finrank_regionParentGroundSpace_eq_one_of_isVertexInjective_of_cover A hA edgePairRegion
    (edgePairRegion_covers_vertices hneighbors) edgePairRegion_covers_edges hD

/-- Every positive exact-kernel nearest-neighbor parent has the closed
injective PEPS span as its kernel, provided no vertex is isolated.
Source: CPGSV21, Section IV.C.1, lines 2032–2044. -/
theorem ker_regionParentHamiltonian_edgePairs_eq_span
    (A : Tensor Γ d) (hA : IsVertexInjective A)
    (hneighbors : ∀ v, ∃ w, Γ.Adj v w)
    (H : (e : Edge Γ) → Matrix (RegionPhysicalConfig (d := d) (edgePairRegion e))
      (RegionPhysicalConfig (d := d) (edgePairRegion e)) ℂ)
    (hH : ∀ e, IsRegionParentInteraction A (edgePairRegion e) (H e)) :
    (Matrix.mulVecLin (regionParentHamiltonian edgePairRegion H)).ker =
      Submodule.span ℂ {stateCoeff A} :=
  ker_regionParentHamiltonian_eq_span_of_isVertexInjective_of_cover A hA edgePairRegion
    (edgePairRegion_covers_vertices hneighbors) edgePairRegion_covers_edges H hH

/-- On an arbitrary graph, edge-pair conditions and isolated-site conditions
select exactly the closed injective PEPS span. Source: the finite-graph
covering-region consequence of CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem regionParentGroundSpace_edgeAndIsolated_eq_span
    (A : Tensor Γ d) (hA : IsVertexInjective A) :
    regionParentGroundSpace A (edgeAndIsolatedRegion (Γ := Γ)) = Submodule.span ℂ {stateCoeff A} :=
  regionParentGroundSpace_eq_span_of_isVertexInjective_of_cover A hA edgeAndIsolatedRegion
    edgeAndIsolatedRegion_covers_vertices edgeAndIsolatedRegion_covers_edges

/-- Positive bonds give a one-dimensional augmented nearest-neighbor parent
space on every finite graph. Source: the covering-region consequence of
CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem finrank_regionParentGroundSpace_edgeAndIsolated_eq_one
    (A : Tensor Γ d) (hA : IsVertexInjective A) (hD : ∀ e, 0 < A.bondDim e) :
    Module.finrank ℂ (regionParentGroundSpace A (edgeAndIsolatedRegion (Γ := Γ))) = 1 :=
  finrank_regionParentGroundSpace_eq_one_of_isVertexInjective_of_cover A hA
    edgeAndIsolatedRegion edgeAndIsolatedRegion_covers_vertices
    edgeAndIsolatedRegion_covers_edges hD

/-- Arbitrary positive exact-kernel parents on the edge-pair and isolated-site
regions have precisely the closed injective PEPS span as their kernel.
Source: finite-graph covering-region consequence of CPGSV21,
Section IV.C.1, lines 2003–2044. -/
theorem ker_regionParentHamiltonian_edgeAndIsolated_eq_span
    (A : Tensor Γ d) (hA : IsVertexInjective A)
    (H : (i : Edge Γ ⊕ {v : V // ¬ ∃ w, Γ.Adj v w}) →
      Matrix (RegionPhysicalConfig (d := d) (edgeAndIsolatedRegion i))
        (RegionPhysicalConfig (d := d) (edgeAndIsolatedRegion i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (edgeAndIsolatedRegion i) (H i)) :
    (Matrix.mulVecLin (regionParentHamiltonian edgeAndIsolatedRegion H)).ker =
      Submodule.span ℂ {stateCoeff A} := by
  classical
  exact ker_regionParentHamiltonian_eq_span_of_isVertexInjective_of_cover A hA
    edgeAndIsolatedRegion edgeAndIsolatedRegion_covers_vertices
    edgeAndIsolatedRegion_covers_edges H hH

/-- With positive bonds, every exact-kernel nearest-neighbor Hamiltonian
has a one-dimensional kernel on a graph without isolated vertices.
Source: CPGSV21, Section IV.C.1, lines 2032–2044. -/
theorem finrank_ker_regionParentHamiltonian_edgePairs_eq_one
    (A : Tensor Γ d) (hA : IsVertexInjective A)
    (hneighbors : ∀ v, ∃ w, Γ.Adj v w) (hD : ∀ e, 0 < A.bondDim e)
    (H : (e : Edge Γ) → Matrix (RegionPhysicalConfig (d := d) (edgePairRegion e))
      (RegionPhysicalConfig (d := d) (edgePairRegion e)) ℂ)
    (hH : ∀ e, IsRegionParentInteraction A (edgePairRegion e) (H e)) :
    Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian edgePairRegion H)).ker = 1 := by
  rw [ker_regionParentHamiltonian A edgePairRegion H hH]
  exact finrank_regionParentGroundSpace_edgePairs_eq_one A hA hneighbors hD

/-- With positive bonds, every exact-kernel augmented nearest-neighbor
Hamiltonian has a one-dimensional kernel on an arbitrary finite graph.
Source: covering-region consequence of CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem finrank_ker_regionParentHamiltonian_edgeAndIsolated_eq_one
    (A : Tensor Γ d) (hA : IsVertexInjective A) (hD : ∀ e, 0 < A.bondDim e)
    (H : (i : Edge Γ ⊕ {v : V // ¬ ∃ w, Γ.Adj v w}) →
      Matrix (RegionPhysicalConfig (d := d) (edgeAndIsolatedRegion i))
        (RegionPhysicalConfig (d := d) (edgeAndIsolatedRegion i)) ℂ)
    (hH : ∀ i, IsRegionParentInteraction A (edgeAndIsolatedRegion i) (H i)) :
    Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian edgeAndIsolatedRegion H)).ker =
      1 := by
  classical
  rw [ker_regionParentHamiltonian A edgeAndIsolatedRegion H hH]
  exact finrank_regionParentGroundSpace_edgeAndIsolated_eq_one A hA hD

end TNLean.PEPS
