import TNLean.PEPS.VirtualInsertion

import Mathlib.Logic.Equiv.Prod

/-!
# Edge-centered decompositions for PEPS local data

This file records two elementary decompositions that recur in the PEPS
Fundamental-Theorem argument.

First, if one incident edge at a vertex is singled out, then local virtual
configurations split as the product of the bond index on that edge and the
remaining incident-edge indices.

Second, for a fixed graph edge `e = (u, v)`, the vertex set splits into the
left endpoint `{u}`, the complement of the endpoints, and the right endpoint
`{v}`. This is the combinatorial starting point for the edge-centered blocking
of a PEPS to a three-partite chain.

## Main results

- `edgeLeftIncident`, `edgeRightIncident`: the two endpoint incidences of an
  ordered edge.
- `localVirtualConfigSplitAt`: split a local virtual configuration at a chosen
  incident edge.
- `edgeLeftVertices`, `edgeMiddleVertices`, `edgeRightVertices`: the canonical
  three-region partition attached to an edge.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, §3](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The lower-endpoint incidence of an ordered edge. -/
def edgeLeftIncident (e : Edge G) : IncidentEdge G e.1.1 :=
  ⟨e, Or.inl rfl⟩

/-- The upper-endpoint incidence of an ordered edge. -/
def edgeRightIncident (e : Edge G) : IncidentEdge G e.1.2 :=
  ⟨e, Or.inr rfl⟩

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem edgeLeftIncident_edge (e : Edge G) :
    (edgeLeftIncident (G := G) e).1 = e :=
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem edgeRightIncident_edge (e : Edge G) :
    (edgeRightIncident (G := G) e).1 = e :=
  rfl

/-- The incident edges at `v` other than a chosen distinguished edge. -/
abbrev OtherIncidentEdge (v : V) (ie : IncidentEdge G v) : Type _ :=
  { je : IncidentEdge G v // je ≠ ie }

/-- The residual local virtual data after removing one distinguished incident
edge. -/
abbrev ResidualLocalConfig (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) : Type _ :=
  (je : OtherIncidentEdge (G := G) v ie) → Fin (A.bondDim je.1.1)

instance instFintypeOtherIncidentEdge (v : V) (ie : IncidentEdge G v) :
    Fintype (OtherIncidentEdge (G := G) v ie) :=
  inferInstance

instance instFintypeResidualLocalConfig (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) : Fintype (ResidualLocalConfig (G := G) A ie) :=
  inferInstance

/-- Split a local virtual configuration into the coordinate on one distinguished
incident edge and the coordinates on all remaining incident edges. -/
noncomputable def localVirtualConfigSplitAt (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) :
    LocalVirtualConfig A v ≃ Fin (A.bondDim ie.1) × ResidualLocalConfig (G := G) A ie := by
  classical
  simpa [LocalVirtualConfig, ResidualLocalConfig, OtherIncidentEdge] using
    (Equiv.piSplitAt ie fun je : IncidentEdge G v => Fin (A.bondDim je.1))

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_apply_fst (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (η : LocalVirtualConfig A v) :
    (localVirtualConfigSplitAt (G := G) A ie η).1 = η ie := by
  classical
  simp [localVirtualConfigSplitAt]

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_apply_snd (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v) (η : LocalVirtualConfig A v)
    (je : OtherIncidentEdge (G := G) v ie) :
    (localVirtualConfigSplitAt (G := G) A ie η).2 je = η je.1 := by
  classical
  simp [localVirtualConfigSplitAt]

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_symm_apply_fst (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (x : Fin (A.bondDim ie.1) × ResidualLocalConfig (G := G) A ie) :
    (localVirtualConfigSplitAt (G := G) A ie).symm x ie = x.1 := by
  classical
  simp [localVirtualConfigSplitAt]

omit [Fintype V] in
@[simp] theorem localVirtualConfigSplitAt_symm_apply_snd (A : Tensor G d) {v : V}
    (ie : IncidentEdge G v)
    (x : Fin (A.bondDim ie.1) × ResidualLocalConfig (G := G) A ie)
    (je : OtherIncidentEdge (G := G) v ie) :
    (localVirtualConfigSplitAt (G := G) A ie).symm x je.1 = x.2 je := by
  classical
  simp [localVirtualConfigSplitAt, je.2]

/-- The left endpoint of an edge as a singleton vertex region. -/
def edgeLeftVertices (e : Edge G) : Finset V :=
  {e.1.1}

/-- The right endpoint of an edge as a singleton vertex region. -/
def edgeRightVertices (e : Edge G) : Finset V :=
  {e.1.2}

/-- The vertices away from the two endpoints of an edge. -/
def edgeMiddleVertices (e : Edge G) : Finset V :=
  (Finset.univ.erase e.1.1).erase e.1.2

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem mem_edgeLeftVertices (e : Edge G) (v : V) :
    v ∈ edgeLeftVertices e ↔ v = e.1.1 := by
  simp [edgeLeftVertices]

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem mem_edgeRightVertices (e : Edge G) (v : V) :
    v ∈ edgeRightVertices e ↔ v = e.1.2 := by
  simp [edgeRightVertices]

omit [DecidableRel G.Adj] in
@[simp] theorem mem_edgeMiddleVertices_iff (e : Edge G) (v : V) :
    v ∈ edgeMiddleVertices e ↔ v ≠ e.1.1 ∧ v ≠ e.1.2 := by
  simpa [and_comm] using (show v ∈ edgeMiddleVertices e ↔ v ≠ e.1.2 ∧ v ≠ e.1.1 by
    simp [edgeMiddleVertices])

omit [DecidableRel G.Adj] in
theorem edgeLeftVertices_disjoint_edgeMiddleVertices (e : Edge G) :
    Disjoint (edgeLeftVertices e) (edgeMiddleVertices e) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hvLeft hvMiddle
  exact (mem_edgeMiddleVertices_iff e v).mp hvMiddle |>.1 <| (mem_edgeLeftVertices e v).mp hvLeft

omit [DecidableRel G.Adj] in
theorem edgeRightVertices_disjoint_edgeMiddleVertices (e : Edge G) :
    Disjoint (edgeRightVertices e) (edgeMiddleVertices e) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hvRight hvMiddle
  exact (mem_edgeMiddleVertices_iff e v).mp hvMiddle |>.2 <|
    (mem_edgeRightVertices e v).mp hvRight

omit [Fintype V] [DecidableRel G.Adj] in
theorem edgeLeftVertices_disjoint_edgeRightVertices (e : Edge G) :
    Disjoint (edgeLeftVertices e) (edgeRightVertices e) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hvLeft hvRight
  have hv₁ : v = e.1.1 := (mem_edgeLeftVertices e v).mp hvLeft
  have hv₂ : v = e.1.2 := (mem_edgeRightVertices e v).mp hvRight
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2.1
  exact hne <| hv₁.symm.trans hv₂

omit [DecidableRel G.Adj] in
theorem edgeVertices_union (e : Edge G) :
    edgeLeftVertices e ∪ edgeMiddleVertices e ∪ edgeRightVertices e = Finset.univ := by
  ext v
  by_cases hvLeft : v = e.1.1
  · simp [edgeLeftVertices, edgeMiddleVertices, edgeRightVertices, hvLeft]
  · by_cases hvRight : v = e.1.2
    · simp [edgeLeftVertices, edgeMiddleVertices, edgeRightVertices, hvRight]
    · simp [edgeLeftVertices, edgeMiddleVertices, edgeRightVertices, hvLeft, hvRight]

end PEPS
end TNLean
