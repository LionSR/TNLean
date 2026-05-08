import TNLean.PEPS.VirtualInsertion

import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Edge-centered decompositions for PEPS local data

This file provides two elementary decompositions that recur in the PEPS
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
- `prod_univ_splitAtEdge`: products over the vertex set factor through the
  three-region partition.
- `stateCoeff_splitAtEdge`: the PEPS amplitude `stateCoeff` factors the
  per-vertex tensor contributions through the three-region partition.
- `edgeInsertedCoeff`: the edge-centered contraction with an arbitrary matrix
  inserted on the distinguished edge.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3](https://arxiv.org/abs/1804.04964)
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

omit [Fintype V] [DecidableRel G.Adj] in
theorem edgeLeft_ne_edgeRight (e : Edge G) : e.1.1 ≠ e.1.2 :=
  ne_of_lt e.2.1

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
  exact edgeLeft_ne_edgeRight e <| hv₁.symm.trans hv₂

omit [DecidableRel G.Adj] in
theorem edgeVertices_union (e : Edge G) :
    edgeLeftVertices e ∪ edgeMiddleVertices e ∪ edgeRightVertices e = Finset.univ := by
  ext v
  by_cases hvLeft : v = e.1.1
  · simp [edgeLeftVertices, edgeMiddleVertices, edgeRightVertices, hvLeft]
  · by_cases hvRight : v = e.1.2
    · simp [edgeLeftVertices, edgeMiddleVertices, edgeRightVertices, hvRight]
    · simp [edgeLeftVertices, edgeMiddleVertices, edgeRightVertices, hvLeft, hvRight]

omit [DecidableRel G.Adj] in
@[simp] theorem notMem_edgeMiddleVertices_left (e : Edge G) :
    e.1.1 ∉ edgeMiddleVertices e := by
  simp [mem_edgeMiddleVertices_iff]

omit [DecidableRel G.Adj] in
@[simp] theorem notMem_edgeMiddleVertices_right (e : Edge G) :
    e.1.2 ∉ edgeMiddleVertices e := by
  simp [mem_edgeMiddleVertices_iff]

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem edgeLeftVertices_card (e : Edge G) :
    (edgeLeftVertices e).card = 1 :=
  Finset.card_singleton _

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem edgeRightVertices_card (e : Edge G) :
    (edgeRightVertices e).card = 1 :=
  Finset.card_singleton _

omit [DecidableRel G.Adj] in
private theorem card_erase_erase_univ (a b : V) (hab : a ≠ b) :
    (((Finset.univ : Finset V).erase a).erase b).card = Fintype.card V - 2 := by
  have ha : a ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  have hb : b ∈ ((Finset.univ : Finset V).erase a) :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, Finset.card_univ]
  rw [Nat.sub_sub]

omit [DecidableRel G.Adj] in
private theorem prod_univ_erase_erase {M : Type*} [CommMonoid M]
    (a b : V) (hab : a ≠ b) (f : V → M) :
    ∏ v : V, f v = f a * (∏ v ∈ (((Finset.univ : Finset V).erase a).erase b), f v) * f b := by
  have ha : a ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  have hb : b ∈ ((Finset.univ : Finset V).erase a) :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
  rw [(Finset.mul_prod_erase _ f ha).symm, (Finset.mul_prod_erase _ f hb).symm]
  simp [mul_left_comm, mul_comm]

omit [DecidableRel G.Adj] in
theorem edgeMiddleVertices_card (e : Edge G) :
    (edgeMiddleVertices e).card = Fintype.card V - 2 := by
  simpa [edgeMiddleVertices] using
    card_erase_erase_univ (V := V) e.1.1 e.1.2 (edgeLeft_ne_edgeRight e)

omit [DecidableRel G.Adj] in
/-- Products over the vertex set factor through the three-region partition at
any edge: the distinguished endpoints appear separately from the middle-region
product. -/
theorem prod_univ_splitAtEdge {M : Type*} [CommMonoid M] (e : Edge G) (f : V → M) :
    ∏ v : V, f v = f e.1.1 * (∏ v ∈ edgeMiddleVertices e, f v) * f e.1.2 := by
  simpa [edgeMiddleVertices] using
    prod_univ_erase_erase (V := V) e.1.1 e.1.2 (edgeLeft_ne_edgeRight e) f

/-- `stateCoeff` evaluates the two endpoint tensors against an independent
product over the middle region. This isolates the two endpoints of an edge in
the PEPS amplitude, matching the edge-centered blocking of
arXiv:1804.04964 Section 3. -/
theorem stateCoeff_splitAtEdge (A : Tensor G d) (e : Edge G) (σ : V → Fin d) :
    stateCoeff A σ =
      ∑ η : VirtualConfig A,
        A.component e.1.1 (fun ie => η ie.1) (σ e.1.1) *
          (∏ v ∈ edgeMiddleVertices e,
              A.component v (fun ie => η ie.1) (σ v)) *
          A.component e.1.2 (fun ie => η ie.1) (σ e.1.2) := by
  unfold stateCoeff
  refine Finset.sum_congr rfl ?_
  intro η _
  exact prod_univ_splitAtEdge e (fun v : V => A.component v (fun ie => η ie.1) (σ v))

/-- Boundary virtual data for the edge-centered three-block decomposition.

For an edge `e = (u, w)`, this consists of the index on `e`, the residual indices on
edges incident to `u` other than `e`, and the residual indices on edges incident
to `w` other than `e`. The middle-region contraction below is fibred over this
data. -/
structure EdgeBoundaryConfig (A : Tensor G d) (e : Edge G) where
  edgeIndex : Fin (A.bondDim e)
  leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e)
  rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)

/-- Product model for edge-centered boundary configurations. -/
def edgeBoundaryConfigEquivProd (A : Tensor G d) (e : Edge G) :
    EdgeBoundaryConfig (G := G) A e ≃
      Fin (A.bondDim e) ×
        ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
        ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e) where
  toFun β := (β.edgeIndex, β.leftResidual, β.rightResidual)
  invFun x :=
    { edgeIndex := x.1
      leftResidual := x.2.1
      rightResidual := x.2.2 }
  left_inv β := by
    cases β
    rfl
  right_inv x := by
    rcases x with ⟨edgeIndex, leftResidual, rightResidual⟩
    rfl

instance instFintypeEdgeBoundaryConfig (A : Tensor G d) (e : Edge G) :
    Fintype (EdgeBoundaryConfig (G := G) A e) :=
  Fintype.ofEquiv
    (Fin (A.bondDim e) ×
      ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
      ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e))
    (edgeBoundaryConfigEquivProd (G := G) A e).symm

/-- The local virtual configuration at the left endpoint determined by an
edge-centered boundary configuration. -/
noncomputable def edgeLeftLocalConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) : LocalVirtualConfig A e.1.1 :=
  (localVirtualConfigSplitAt (G := G) A (edgeLeftIncident (G := G) e)).symm
    (β.edgeIndex, β.leftResidual)

/-- The local virtual configuration at the right endpoint determined by an
edge-centered boundary configuration. -/
noncomputable def edgeRightLocalConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) : LocalVirtualConfig A e.1.2 :=
  (localVirtualConfigSplitAt (G := G) A (edgeRightIncident (G := G) e)).symm
    (β.edgeIndex, β.rightResidual)

omit [Fintype V] in
@[simp] theorem edgeLeftLocalConfig_edgeIndex (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) :
    edgeLeftLocalConfig (G := G) A e β (edgeLeftIncident (G := G) e) =
      β.edgeIndex := by
  simpa [edgeLeftLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_fst (G := G) A (edgeLeftIncident (G := G) e)
      (β.edgeIndex, β.leftResidual)

omit [Fintype V] in
@[simp] theorem edgeRightLocalConfig_edgeIndex (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) :
    edgeRightLocalConfig (G := G) A e β (edgeRightIncident (G := G) e) =
      β.edgeIndex := by
  simpa [edgeRightLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_fst (G := G) A (edgeRightIncident (G := G) e)
      (β.edgeIndex, β.rightResidual)

omit [Fintype V] in
@[simp] theorem edgeLeftLocalConfig_residual (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e)) :
    edgeLeftLocalConfig (G := G) A e β ie.1 = β.leftResidual ie := by
  simpa [edgeLeftLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_snd (G := G) A (edgeLeftIncident (G := G) e)
      (β.edgeIndex, β.leftResidual) ie

omit [Fintype V] in
@[simp] theorem edgeRightLocalConfig_residual (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e)) :
    edgeRightLocalConfig (G := G) A e β ie.1 = β.rightResidual ie := by
  simpa [edgeRightLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_snd (G := G) A (edgeRightIncident (G := G) e)
      (β.edgeIndex, β.rightResidual) ie

/-- A global virtual configuration has prescribed edge-centered boundary data if
it agrees with the distinguished edge index and both residual endpoint families. -/
def edgeBoundaryMatches (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) (η : VirtualConfig A) : Prop :=
  η e = β.edgeIndex ∧
    (∀ ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e),
      η ie.1.1 = β.leftResidual ie) ∧
    (∀ ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e),
      η ie.1.1 = β.rightResidual ie)

/-- Global virtual configurations whose endpoint boundary data are fixed. These
are the internal summation variables of the blocked middle tensor. -/
abbrev EdgeMiddleConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) : Type _ :=
  {η : VirtualConfig A // edgeBoundaryMatches (G := G) A e β η}

noncomputable instance instFintypeEdgeMiddleConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) : Fintype (EdgeMiddleConfig (G := G) A e β) := by
  classical
  infer_instance

/-- Read the edge-centered boundary data from a global virtual configuration. -/
def edgeBoundaryOfVirtualConfig (A : Tensor G d) (e : Edge G)
    (η : VirtualConfig A) : EdgeBoundaryConfig (G := G) A e where
  edgeIndex := η e
  leftResidual ie := η ie.1.1
  rightResidual ie := η ie.1.1

omit [Fintype V] in
@[simp] theorem edgeBoundaryOfVirtualConfig_matches (A : Tensor G d) (e : Edge G)
    (η : VirtualConfig A) :
    edgeBoundaryMatches (G := G) A e (edgeBoundaryOfVirtualConfig (G := G) A e η) η := by
  simp [edgeBoundaryMatches, edgeBoundaryOfVirtualConfig]

/-- Global virtual configurations are equivalent to choosing their edge-centered
boundary data together with a middle configuration in the corresponding fibre. -/
noncomputable def virtualConfigEquivEdgeBoundary (A : Tensor G d) (e : Edge G) :
    VirtualConfig A ≃
      (Σ β : EdgeBoundaryConfig (G := G) A e, EdgeMiddleConfig (G := G) A e β) where
  toFun η :=
    ⟨edgeBoundaryOfVirtualConfig (G := G) A e η,
      ⟨η, edgeBoundaryOfVirtualConfig_matches (G := G) A e η⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨β, η, hη⟩
    have hβ : edgeBoundaryOfVirtualConfig (G := G) A e η = β := by
      rcases β with ⟨edgeIndex, leftResidual, rightResidual⟩
      have hleft :
          (fun ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e) =>
            η ie.1.1) = leftResidual := funext hη.2.1
      have hright :
          (fun ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e) =>
            η ie.1.1) = rightResidual := funext hη.2.2
      cases hη.1
      cases hleft
      cases hright
      rfl
    subst β
    simp

omit [Fintype V] in
/-- The left endpoint local configuration obtained from a matching global virtual
configuration is the one reconstructed from its boundary data. -/
theorem edgeLeftLocalConfig_eq_of_boundaryMatches (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) (η : VirtualConfig A)
    (hη : edgeBoundaryMatches (G := G) A e β η) :
    (fun ie : IncidentEdge G e.1.1 => η ie.1) = edgeLeftLocalConfig (G := G) A e β := by
  funext ie
  by_cases hie : ie = edgeLeftIncident (G := G) e
  · subst ie
    rw [edgeLeftLocalConfig_edgeIndex]
    exact hη.1
  · calc
      η ie.1 = β.leftResidual ⟨ie, hie⟩ := hη.2.1 ⟨ie, hie⟩
      _ = edgeLeftLocalConfig (G := G) A e β ie := by
        simpa using (edgeLeftLocalConfig_residual (G := G) A e β ⟨ie, hie⟩).symm

omit [Fintype V] in
/-- The right endpoint local configuration obtained from a matching global
virtual configuration is the one reconstructed from its boundary data. -/
theorem edgeRightLocalConfig_eq_of_boundaryMatches (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) (η : VirtualConfig A)
    (hη : edgeBoundaryMatches (G := G) A e β η) :
    (fun ie : IncidentEdge G e.1.2 => η ie.1) = edgeRightLocalConfig (G := G) A e β := by
  funext ie
  by_cases hie : ie = edgeRightIncident (G := G) e
  · subst ie
    rw [edgeRightLocalConfig_edgeIndex]
    exact hη.1
  · calc
      η ie.1 = β.rightResidual ⟨ie, hie⟩ := hη.2.2 ⟨ie, hie⟩
      _ = edgeRightLocalConfig (G := G) A e β ie := by
        simpa using (edgeRightLocalConfig_residual (G := G) A e β ⟨ie, hie⟩).symm

/-! ### Open middle region and edge insertions -/

/-- Boundary data for the edge-centered contraction with an inserted matrix.

The two endpoints of the distinguished edge carry independent edge indices; this
is the finite-graph version of inserting a matrix on that bond in
arXiv:1804.04964, Section 3. -/
structure EdgeInsertedBoundaryConfig (A : Tensor G d) (e : Edge G) where
  leftEdgeIndex : Fin (A.bondDim e)
  rightEdgeIndex : Fin (A.bondDim e)
  leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e)
  rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)

/-- Ordinary edge-boundary data, regarded as inserted-edge boundary data on the
diagonal of the two distinguished bond indices. This is the boundary datum
selected by the identity matrix in an edge insertion. -/
def edgeBoundaryToInsertedBoundaryConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) : EdgeInsertedBoundaryConfig (G := G) A e where
  leftEdgeIndex := β.edgeIndex
  rightEdgeIndex := β.edgeIndex
  leftResidual := β.leftResidual
  rightResidual := β.rightResidual

@[simp] theorem edgeBoundaryToInsertedBoundaryConfig_leftEdgeIndex
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e) :
    (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β).leftEdgeIndex =
      β.edgeIndex :=
  rfl

@[simp] theorem edgeBoundaryToInsertedBoundaryConfig_rightEdgeIndex
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e) :
    (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β).rightEdgeIndex =
      β.edgeIndex :=
  rfl

@[simp] theorem edgeBoundaryToInsertedBoundaryConfig_leftResidual
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e) :
    (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β).leftResidual =
      β.leftResidual :=
  rfl

@[simp] theorem edgeBoundaryToInsertedBoundaryConfig_rightResidual
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e) :
    (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β).rightResidual =
      β.rightResidual :=
  rfl

/-- Product model for inserted-edge boundary configurations. -/
def edgeInsertedBoundaryConfigEquivProd (A : Tensor G d) (e : Edge G) :
    EdgeInsertedBoundaryConfig (G := G) A e ≃
      Fin (A.bondDim e) × Fin (A.bondDim e) ×
        ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
        ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e) where
  toFun β := (β.leftEdgeIndex, β.rightEdgeIndex, β.leftResidual, β.rightResidual)
  invFun x :=
    { leftEdgeIndex := x.1
      rightEdgeIndex := x.2.1
      leftResidual := x.2.2.1
      rightResidual := x.2.2.2 }
  left_inv β := by
    cases β
    rfl
  right_inv x := by
    rcases x with ⟨leftEdgeIndex, rightEdgeIndex, leftResidual, rightResidual⟩
    rfl

instance instFintypeEdgeInsertedBoundaryConfig (A : Tensor G d) (e : Edge G) :
    Fintype (EdgeInsertedBoundaryConfig (G := G) A e) :=
  Fintype.ofEquiv
    (Fin (A.bondDim e) × Fin (A.bondDim e) ×
      ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e) ×
      ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e))
    (edgeInsertedBoundaryConfigEquivProd (G := G) A e).symm

/-- The diagonal part of inserted-edge boundary data, where the two distinguished
bond indices agree. This is the part selected by inserting the identity matrix
on the edge. -/
abbrev EdgeDiagonalInsertedBoundaryConfig (A : Tensor G d) (e : Edge G) : Type _ :=
  {β : EdgeInsertedBoundaryConfig (G := G) A e // β.leftEdgeIndex = β.rightEdgeIndex}

instance instFintypeEdgeDiagonalInsertedBoundaryConfig (A : Tensor G d) (e : Edge G) :
    Fintype (EdgeDiagonalInsertedBoundaryConfig (G := G) A e) :=
  inferInstance

/-- Ordinary edge-boundary data are exactly the diagonal inserted-boundary data.

This is the finite reindexing map used after the identity matrix has killed the
off-diagonal inserted-boundary summands. -/
def edgeBoundaryConfigEquivDiagonalInsertedBoundaryConfig (A : Tensor G d)
    (e : Edge G) :
    EdgeBoundaryConfig (G := G) A e ≃
      EdgeDiagonalInsertedBoundaryConfig (G := G) A e where
  toFun β := ⟨edgeBoundaryToInsertedBoundaryConfig (G := G) A e β, rfl⟩
  invFun β :=
    { edgeIndex := β.1.leftEdgeIndex
      leftResidual := β.1.leftResidual
      rightResidual := β.1.rightResidual }
  left_inv β := by
    cases β
    rfl
  right_inv β := by
    rcases β with ⟨β, hβ⟩
    cases β with
    | mk leftEdgeIndex rightEdgeIndex leftResidual rightResidual =>
      cases hβ
      rfl

/-- The left endpoint local configuration determined by inserted-edge boundary
data. -/
noncomputable def edgeInsertedLeftLocalConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeInsertedBoundaryConfig (G := G) A e) : LocalVirtualConfig A e.1.1 :=
  (localVirtualConfigSplitAt (G := G) A (edgeLeftIncident (G := G) e)).symm
    (β.leftEdgeIndex, β.leftResidual)

/-- The right endpoint local configuration determined by inserted-edge boundary
data. -/
noncomputable def edgeInsertedRightLocalConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeInsertedBoundaryConfig (G := G) A e) : LocalVirtualConfig A e.1.2 :=
  (localVirtualConfigSplitAt (G := G) A (edgeRightIncident (G := G) e)).symm
    (β.rightEdgeIndex, β.rightResidual)

omit [Fintype V] in
@[simp] theorem edgeInsertedLeftLocalConfig_edgeIndex (A : Tensor G d) (e : Edge G)
    (β : EdgeInsertedBoundaryConfig (G := G) A e) :
    edgeInsertedLeftLocalConfig (G := G) A e β (edgeLeftIncident (G := G) e) =
      β.leftEdgeIndex := by
  simpa [edgeInsertedLeftLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_fst (G := G) A (edgeLeftIncident (G := G) e)
      (β.leftEdgeIndex, β.leftResidual)

omit [Fintype V] in
@[simp] theorem edgeInsertedRightLocalConfig_edgeIndex (A : Tensor G d) (e : Edge G)
    (β : EdgeInsertedBoundaryConfig (G := G) A e) :
    edgeInsertedRightLocalConfig (G := G) A e β (edgeRightIncident (G := G) e) =
      β.rightEdgeIndex := by
  simpa [edgeInsertedRightLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_fst (G := G) A (edgeRightIncident (G := G) e)
      (β.rightEdgeIndex, β.rightResidual)

omit [Fintype V] in
@[simp] theorem edgeInsertedLeftLocalConfig_residual (A : Tensor G d) (e : Edge G)
    (β : EdgeInsertedBoundaryConfig (G := G) A e)
    (ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e)) :
    edgeInsertedLeftLocalConfig (G := G) A e β ie.1 = β.leftResidual ie := by
  simpa [edgeInsertedLeftLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_snd (G := G) A (edgeLeftIncident (G := G) e)
      (β.leftEdgeIndex, β.leftResidual) ie

omit [Fintype V] in
@[simp] theorem edgeInsertedRightLocalConfig_residual (A : Tensor G d) (e : Edge G)
    (β : EdgeInsertedBoundaryConfig (G := G) A e)
    (ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e)) :
    edgeInsertedRightLocalConfig (G := G) A e β ie.1 = β.rightResidual ie := by
  simpa [edgeInsertedRightLocalConfig] using
    localVirtualConfigSplitAt_symm_apply_snd (G := G) A (edgeRightIncident (G := G) e)
      (β.rightEdgeIndex, β.rightResidual) ie

@[simp] theorem edgeInsertedLeftLocalConfig_edgeBoundaryToInsertedBoundaryConfig
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e) :
    edgeInsertedLeftLocalConfig (G := G) A e
        (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β) =
      edgeLeftLocalConfig (G := G) A e β :=
  rfl

@[simp] theorem edgeInsertedRightLocalConfig_edgeBoundaryToInsertedBoundaryConfig
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e) :
    edgeInsertedRightLocalConfig (G := G) A e
        (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β) =
      edgeRightLocalConfig (G := G) A e β :=
  rfl

/-- Virtual configurations on all edges except the distinguished one. -/
abbrev EdgeComplementConfig (A : Tensor G d) (e : Edge G) : Type _ :=
  (f : {f : Edge G // f ≠ e}) → Fin (A.bondDim f.1)

instance instFintypeEdgeComplementConfig (A : Tensor G d) (e : Edge G) :
    Fintype (EdgeComplementConfig (G := G) A e) :=
  inferInstance

private theorem edge_ne_of_middle_incident (e : Edge G) {v : V}
    (hv : v ∈ edgeMiddleVertices e) (ie : IncidentEdge G v) : ie.1 ≠ e := by
  intro hie
  have hvne := (mem_edgeMiddleVertices_iff e v).mp hv
  rcases ie.2 with hleft | hright
  · exact hvne.1 (hleft.symm.trans (congrArg (fun f : Edge G => f.1.1) hie))
  · exact hvne.2 (hright.symm.trans (congrArg (fun f : Edge G => f.1.2) hie))

private theorem otherLeft_edge_ne (e : Edge G)
    (ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e)) :
    ie.1.1 ≠ e := by
  intro hie
  exact ie.2 (Subtype.ext hie)

private theorem otherRight_edge_ne (e : Edge G)
    (ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e)) :
    ie.1.1 ≠ e := by
  intro hie
  exact ie.2 (Subtype.ext hie)

/-- A complement configuration agrees with the residual data at the two endpoint
stars. -/
def edgeOpenBoundaryMatches (A : Tensor G d) (e : Edge G)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e))
    (ζ : EdgeComplementConfig (G := G) A e) : Prop :=
  (∀ ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e),
    ζ ⟨ie.1.1, otherLeft_edge_ne (G := G) e ie⟩ = leftResidual ie) ∧
  (∀ ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e),
    ζ ⟨ie.1.1, otherRight_edge_ne (G := G) e ie⟩ = rightResidual ie)

/-- Complement configurations compatible with fixed endpoint residual data. -/
abbrev EdgeOpenMiddleConfig (A : Tensor G d) (e : Edge G)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    Type _ :=
  {ζ : EdgeComplementConfig (G := G) A e //
    edgeOpenBoundaryMatches (G := G) A e leftResidual rightResidual ζ}

noncomputable instance instFintypeEdgeOpenMiddleConfig (A : Tensor G d) (e : Edge G)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    Fintype (EdgeOpenMiddleConfig (G := G) A e leftResidual rightResidual) := by
  classical
  infer_instance

/-- Restrict an ordinary edge-middle configuration to the complement of the
distinguished edge. This is the forward map in the finite reindexing that
compares identity insertion with the ordinary edge-blocked middle tensor. -/
def edgeMiddleConfigToOpenMiddleConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (η : EdgeMiddleConfig (G := G) A e β) :
    EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual :=
  ⟨fun f => η.1 f.1,
    by
      constructor
      · intro ie
        exact η.2.2.1 ie
      · intro ie
        exact η.2.2.2 ie⟩

@[simp] theorem edgeMiddleConfigToOpenMiddleConfig_apply (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (η : EdgeMiddleConfig (G := G) A e β) (f : {f : Edge G // f ≠ e}) :
    (edgeMiddleConfigToOpenMiddleConfig (G := G) A e β η).1 f = η.1 f.1 :=
  rfl

/-- Extend a compatible complement configuration by putting the ordinary
edge-boundary index back on the distinguished edge. This is the inverse map
needed for the identity-insertion reindexing. -/
noncomputable def edgeOpenMiddleConfigToMiddleConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual) :
    EdgeMiddleConfig (G := G) A e β :=
  ⟨fun f =>
      if h : f = e then
        Fin.cast (by rw [h]) β.edgeIndex
      else
        ζ.1 ⟨f, h⟩,
    by
      constructor
      · simp
      · constructor
        · intro ie
          have hne := otherLeft_edge_ne (G := G) e ie
          simpa [hne] using ζ.2.1 ie
        · intro ie
          have hne := otherRight_edge_ne (G := G) e ie
          simpa [hne] using ζ.2.2 ie⟩

@[simp] theorem edgeOpenMiddleConfigToMiddleConfig_edge (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual) :
    (edgeOpenMiddleConfigToMiddleConfig (G := G) A e β ζ).1 e = β.edgeIndex := by
  simp [edgeOpenMiddleConfigToMiddleConfig]

@[simp] theorem edgeOpenMiddleConfigToMiddleConfig_apply_ne (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e)
    (ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual)
    (f : {f : Edge G // f ≠ e}) :
    (edgeOpenMiddleConfigToMiddleConfig (G := G) A e β ζ).1 f.1 = ζ.1 f := by
  simp [edgeOpenMiddleConfigToMiddleConfig, f.2]

/-- Ordinary middle configurations and compatible open-middle configurations are
the same finite data once the distinguished edge index is fixed by the boundary
configuration. This is the reindexing equivalence behind the identity-insertion
specialization. -/
noncomputable def edgeMiddleConfigEquivOpenMiddleConfig (A : Tensor G d) (e : Edge G)
    (β : EdgeBoundaryConfig (G := G) A e) :
    EdgeMiddleConfig (G := G) A e β ≃
      EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual where
  toFun := edgeMiddleConfigToOpenMiddleConfig (G := G) A e β
  invFun := edgeOpenMiddleConfigToMiddleConfig (G := G) A e β
  left_inv η := by
    apply Subtype.ext
    funext f
    by_cases hf : f = e
    · subst f
      simp [edgeOpenMiddleConfigToMiddleConfig, η.2.1]
    · simp [edgeOpenMiddleConfigToMiddleConfig, edgeMiddleConfigToOpenMiddleConfig, hf]
  right_inv ζ := by
    apply Subtype.ext
    funext f
    simp [edgeOpenMiddleConfigToMiddleConfig, edgeMiddleConfigToOpenMiddleConfig, f.2]

/-- The value of a complement configuration on an edge incident to a middle
vertex. -/
def edgeComplementValue (A : Tensor G d) (e : Edge G)
    (ζ : EdgeComplementConfig (G := G) A e) {v : V}
    (hv : v ∈ edgeMiddleVertices e) (ie : IncidentEdge G v) :
    Fin (A.bondDim ie.1) :=
  ζ ⟨ie.1, edge_ne_of_middle_incident (G := G) e hv ie⟩

@[simp] theorem edgeComplementValue_edgeMiddleConfigToOpenMiddleConfig
    (A : Tensor G d) (e : Edge G) (β : EdgeBoundaryConfig (G := G) A e)
    (η : EdgeMiddleConfig (G := G) A e β) {v : V}
    (hv : v ∈ edgeMiddleVertices e) (ie : IncidentEdge G v) :
    edgeComplementValue (G := G) A e
        (edgeMiddleConfigToOpenMiddleConfig (G := G) A e β η).1 hv ie =
      η.1 ie.1 :=
  rfl

/-- The blocked middle tensor with the distinguished edge left open.

The endpoint residual data are fixed, while the matrix index on the distinguished
edge is absent from the middle region. This is the middle block in the
edge-centered reduction to a three-site MPS in arXiv:1804.04964, Section 3. -/
noncomputable def edgeOpenMiddleWeight (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    ℂ :=
  ∑ ζ : EdgeOpenMiddleConfig (G := G) A e leftResidual rightResidual,
    ∏ v : {v : V // v ∈ edgeMiddleVertices e},
      A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ.1 v.2 ie)
        (σ v.1)

/-- The edge-centered PEPS contraction with a matrix inserted on the distinguished
edge.

For the identity matrix this is the three-block contraction without insertion;
for arbitrary matrices it is the family of comparisons used after the
edge-centered reduction to the injective MPS theorem. -/
noncomputable def edgeInsertedCoeff (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) : ℂ :=
  ∑ β : EdgeInsertedBoundaryConfig (G := G) A e,
    A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      M β.leftEdgeIndex β.rightEdgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2)

/-- The blocked middle tensor for an edge-centered decomposition, evaluated on a
physical configuration and fixed endpoint boundary data. -/
noncomputable def edgeMiddleWeight (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (β : EdgeBoundaryConfig (G := G) A e) : ℂ :=
  ∑ η : EdgeMiddleConfig (G := G) A e β,
    ∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => η.1 ie.1) (σ v)

/-- The ordinary blocked middle tensor is the open middle tensor after restoring
the fixed distinguished-edge index and reindexing the finite sum.

This is the coefficient-level reindexing behind the identity specialization of
an edge insertion. -/
theorem edgeMiddleWeight_eq_edgeOpenMiddleWeight (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (β : EdgeBoundaryConfig (G := G) A e) :
    edgeMiddleWeight (G := G) A e σ β =
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual := by
  classical
  rw [edgeMiddleWeight, edgeOpenMiddleWeight]
  let φ := edgeMiddleConfigEquivOpenMiddleConfig (G := G) A e β
  calc
    (∑ η : EdgeMiddleConfig (G := G) A e β,
        ∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => η.1 ie.1) (σ v))
        = ∑ ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual,
            ∏ v ∈ edgeMiddleVertices e,
              A.component v (fun ie => (φ.symm ζ).1 ie.1) (σ v) := by
          refine Fintype.sum_equiv φ
            (fun η : EdgeMiddleConfig (G := G) A e β =>
              ∏ v ∈ edgeMiddleVertices e,
                A.component v (fun ie => η.1 ie.1) (σ v))
            (fun ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual =>
              ∏ v ∈ edgeMiddleVertices e,
                A.component v (fun ie => (φ.symm ζ).1 ie.1) (σ v)) ?_
          intro η
          simp [φ]
    _ = ∑ ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual,
          ∏ v : {v : V // v ∈ edgeMiddleVertices e},
            A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ.1 v.2 ie)
              (σ v.1) := by
        refine Finset.sum_congr rfl ?_
        intro ζ _
        rw [Finset.prod_subtype (s := edgeMiddleVertices e)
          (p := fun v => v ∈ edgeMiddleVertices e) (h := by intro v; rfl)]
        refine Fintype.prod_congr _ _ ?_
        intro v
        apply congrArg (fun cfg => A.component v.1 cfg (σ v.1))
        funext ie
        have hne := edge_ne_of_middle_incident (G := G) e v.2 ie
        simpa [φ, edgeComplementValue, edgeMiddleConfigEquivOpenMiddleConfig] using
          edgeOpenMiddleConfigToMiddleConfig_apply_ne (G := G) A e β ζ ⟨ie.1, hne⟩

/-- On the diagonal boundary datum, the identity insertion has exactly the
ordinary edge-blocked summand.

This is the local diagonal part of the specialization of the virtual insertion
to the identity matrix. The remaining summation step is to show that all
off-diagonal inserted boundary data vanish and that the diagonal data reindex
the ordinary edge-boundary sum. -/
theorem edgeInsertedCoeff_identity_diagonal_summand (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (β : EdgeBoundaryConfig (G := G) A e) :
    A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e
        (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β)) (σ e.1.1) *
      (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) β.edgeIndex β.edgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e
        (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β)) (σ e.1.2) =
    A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      edgeMiddleWeight (G := G) A e σ β *
      A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := by
  rw [edgeMiddleWeight_eq_edgeOpenMiddleWeight]
  simp [mul_assoc]

/-- Off the diagonal, the identity insertion contributes no summand. -/
theorem edgeInsertedCoeff_identity_offDiagonal_summand (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (β : EdgeInsertedBoundaryConfig (G := G) A e)
    (hβ : β.leftEdgeIndex ≠ β.rightEdgeIndex) :
    A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
        β.leftEdgeIndex β.rightEdgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2) =
    0 := by
  simp [hβ]

/-- The PEPS coefficient written as a three-block contraction at the edge `e`: the
left endpoint tensor, the blocked middle tensor, and the right endpoint tensor. -/
noncomputable def edgeBlockedCoeff (A : Tensor G d) (e : Edge G) (σ : V → Fin d) : ℂ :=
  ∑ β : EdgeBoundaryConfig (G := G) A e,
    A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      edgeMiddleWeight (G := G) A e σ β *
      A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)

/-- The edge-blocked coefficient is exactly the original PEPS coefficient. This is
the algebraic form of the edge-centered blocking step before applying the
three-site MPS fundamental theorem. -/
theorem edgeBlockedCoeff_eq_stateCoeff (A : Tensor G d) (e : Edge G) (σ : V → Fin d) :
    edgeBlockedCoeff (G := G) A e σ = stateCoeff A σ := by
  classical
  rw [stateCoeff_splitAtEdge]
  calc
    edgeBlockedCoeff (G := G) A e σ
      = ∑ β : EdgeBoundaryConfig (G := G) A e,
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
            (∑ η : EdgeMiddleConfig (G := G) A e β,
              ∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => η.1 ie.1) (σ v)) *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := by
          rfl
    _ = ∑ β : EdgeBoundaryConfig (G := G) A e,
          ∑ η : EdgeMiddleConfig (G := G) A e β,
            A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
              (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => η.1 ie.1) (σ v)) *
              A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2) := by
        refine Finset.sum_congr rfl ?_
        intro β _
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ x : (Σ β : EdgeBoundaryConfig (G := G) A e, EdgeMiddleConfig (G := G) A e β),
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e x.1) (σ e.1.1) *
            (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => x.2.1 ie.1) (σ v)) *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e x.1) (σ e.1.2) := by
        rw [← Fintype.sum_sigma']
    _ = ∑ η : VirtualConfig A,
          A.component e.1.1 (fun ie => η ie.1) (σ e.1.1) *
            (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => η ie.1) (σ v)) *
            A.component e.1.2 (fun ie => η ie.1) (σ e.1.2) := by
        let φ := virtualConfigEquivEdgeBoundary (G := G) A e
        let F : (Σ β : EdgeBoundaryConfig (G := G) A e,
            EdgeMiddleConfig (G := G) A e β) → ℂ := fun x =>
          A.component e.1.1 (edgeLeftLocalConfig (G := G) A e x.1) (σ e.1.1) *
            (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => x.2.1 ie.1) (σ v)) *
            A.component e.1.2 (edgeRightLocalConfig (G := G) A e x.1) (σ e.1.2)
        calc
          (∑ x : (Σ β : EdgeBoundaryConfig (G := G) A e,
              EdgeMiddleConfig (G := G) A e β), F x)
            = ∑ η : VirtualConfig A, F (φ η) := by
              exact (φ.sum_comp F).symm
          _ = ∑ η : VirtualConfig A,
              A.component e.1.1 (fun ie => η ie.1) (σ e.1.1) *
                (∏ v ∈ edgeMiddleVertices e, A.component v (fun ie => η ie.1) (σ v)) *
                A.component e.1.2 (fun ie => η ie.1) (σ e.1.2) := by
              refine Finset.sum_congr rfl ?_
              intro η _
              have hmatch : edgeBoundaryMatches (G := G) A e
                  (edgeBoundaryOfVirtualConfig (G := G) A e η) η := by
                simp
              have hleft := edgeLeftLocalConfig_eq_of_boundaryMatches
                (G := G) A e (edgeBoundaryOfVirtualConfig (G := G) A e η) η hmatch
              have hright := edgeRightLocalConfig_eq_of_boundaryMatches
                (G := G) A e (edgeBoundaryOfVirtualConfig (G := G) A e η) η hmatch
              simp [F, φ, virtualConfigEquivEdgeBoundary, hleft.symm, hright.symm]

/-- Equality of PEPS states gives equality of the corresponding edge-blocked
three-block coefficients at every edge. -/
theorem SameState.edgeBlockedCoeff_eq {A B : Tensor G d} (hAB : SameState A B)
    (e : Edge G) (σ : V → Fin d) :
    edgeBlockedCoeff (G := G) A e σ = edgeBlockedCoeff (G := G) B e σ := by
  rw [edgeBlockedCoeff_eq_stateCoeff, edgeBlockedCoeff_eq_stateCoeff]
  exact hAB σ

end PEPS
end TNLean
