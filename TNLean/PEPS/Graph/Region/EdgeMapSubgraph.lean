/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import QICLean.ManyBody.Sites.Lattice.Edge
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Incident edges, and edges and subgraphs transported along a graph isomorphism

The edges incident to a vertex (`IncidentEdge`) index the virtual legs of a PEPS
tensor at that vertex. A graph isomorphism `φ : G ≃g G'` transports an ordered edge
by mapping its endpoints and sorting them (`Edge.map`, `Edge.equiv`), and carries
the edges incident to `v` to the edges incident to `φ v` (`IncidentEdge.equiv`).
Pulling any graph back along the inverse isomorphism preserves adjacency of these
endpoints, independently of the sorting. In particular a non-tree bond remains
outside the transported tree.

The edge action is the geometric input to the transport of PEPS tensors along
graph isomorphisms (arXiv:1804.04964, Section 3, proof of Theorem 3, lines
1407--1572 of `Papers/1804.04964/paper_normal.tex`).

Auxiliary to SCP10, arXiv:1001.3807, the finite blocking and adjacent-flux
geometries in lines 1765–1920 and 2380–2415.

## Main definitions

* `TNLean.PEPS.IncidentEdge`: the edges incident to a vertex.
* `ManyBody.Edge.map`, `ManyBody.Edge.equiv`: the edge action of a graph isomorphism.
* `TNLean.PEPS.IncidentEdge.equiv`: the incident edges of `v` and of `φ v`.
* `TNLean.PEPS.edgeLeftIncident`, `TNLean.PEPS.edgeRightIncident`: the two endpoint
  incidences of an ordered edge.
* `TNLean.PEPS.Region.map`: the image of a region under a graph isomorphism.

## Main results

* `TNLean.PEPS.prod_incident_eq_prod_edge`, `TNLean.PEPS.prod_region_incident_eq_prod_edge`:
  products over incident half-edges regrouped edge by edge.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open ManyBody (Edge)

namespace TNLean.PEPS

section IncidentEdges

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Edges incident to a vertex `v`. -/
abbrev IncidentEdge (G : SimpleGraph V) (v : V) : Type _ :=
  { e : Edge G // e.1.1 = v ∨ e.1.2 = v }

instance instFintypeIncidentEdge (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype (IncidentEdge G v) :=
  inferInstance

end IncidentEdges

section EdgeAction

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W}

/-! ### The edge action of a graph isomorphism -/

/-- The edge of `G'` obtained by pushing an edge of `G` through the graph
isomorphism `φ`: apply `φ` to both endpoints and reorder them into the `Edge`
convention with `Edge.ofAdj`.  The isomorphism may swap the order of the two
endpoints, which `Edge.ofAdj` corrects. -/
def _root_.ManyBody.Edge.map (φ : G ≃g G') (e : Edge G) : Edge G' :=
  ManyBody.Edge.ofAdj ((φ.map_rel_iff').mpr e.2.2)

omit [Fintype V] [Fintype W] in
/-- The unordered endpoints of `Edge.map φ e` are the `φ`-images of the endpoints
of `e`. -/
theorem _root_.ManyBody.Edge.map_endpoints (φ : G ≃g G') (e : Edge G) :
    ((ManyBody.Edge.map φ e).1.1 = φ e.1.1 ∧ (ManyBody.Edge.map φ e).1.2 = φ e.1.2) ∨
      ((ManyBody.Edge.map φ e).1.1 = φ e.1.2 ∧ (ManyBody.Edge.map φ e).1.2 = φ e.1.1) :=
  ManyBody.Edge.ofAdj_endpoints ((φ.map_rel_iff').mpr e.2.2)

omit [Fintype V] [Fintype W] in
/-- Successive graph isomorphisms transport an edge by their composition. -/
theorem _root_.ManyBody.Edge.map_trans {Z : Type*} [LinearOrder Z] {G'' : SimpleGraph Z}
    (φ : G ≃g G') (ψ : G' ≃g G'') (e : Edge G) :
    ManyBody.Edge.map ψ (ManyBody.Edge.map φ e) = ManyBody.Edge.map (φ.trans ψ) e := by
  apply ManyBody.Edge.ofAdj_eq_ofAdj
  rcases ManyBody.Edge.map_endpoints φ e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨by rw [h₁]; rfl, by rw [h₂]; rfl⟩
  · exact Or.inr ⟨by rw [h₁]; rfl, by rw [h₂]; rfl⟩

omit [Fintype V] [Fintype W] in
/-- Pushing an edge through `φ` and then through `φ.symm` recovers the original
edge.  The two passes return to the original unordered endpoint pair, and
`Edge.ofAdj` re-imposes the same `<`-order, so the round trip is the identity. -/
@[simp] theorem _root_.ManyBody.Edge.map_symm_map (φ : G ≃g G') (e : Edge G) :
    ManyBody.Edge.map φ.symm (ManyBody.Edge.map φ e) = e := by
  apply ManyBody.Edge.ofAdj_eq_of_endpoints
  rcases ManyBody.Edge.map_endpoints φ e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · exact Or.inr ⟨by rw [h1]; simp, by rw [h2]; simp⟩

omit [Fintype V] [Fintype W] in
/-- Pushing an edge through `φ.symm` and then through `φ` recovers it. -/
@[simp] theorem _root_.ManyBody.Edge.map_map_symm (φ : G ≃g G') (e : Edge G') :
    ManyBody.Edge.map φ (ManyBody.Edge.map φ.symm e) = e :=
  ManyBody.Edge.map_symm_map φ.symm e

/-- The edge action of `φ` as a bijection `Edge G ≃ Edge G'`. -/
def _root_.ManyBody.Edge.equiv (φ : G ≃g G') : Edge G ≃ Edge G' where
  toFun := ManyBody.Edge.map φ
  invFun := ManyBody.Edge.map φ.symm
  left_inv := ManyBody.Edge.map_symm_map φ
  right_inv := ManyBody.Edge.map_map_symm φ

omit [Fintype V] [Fintype W] in
-- restored: fired by the bare `simpa` in `IncidentEdge.equiv` below
@[simp] theorem _root_.ManyBody.Edge.equiv_apply (φ : G ≃g G') (e : Edge G) :
    ManyBody.Edge.equiv φ e = ManyBody.Edge.map φ e :=
  rfl

/-! ### The incident-edge correspondence -/

omit [Fintype V] [Fintype W] in
/-- An edge incident to `v` maps, under `φ`, to an edge incident to `φ v`. -/
theorem _root_.ManyBody.Edge.map_incident (φ : G ≃g G') {v : V} {e : Edge G}
    (h : e.1.1 = v ∨ e.1.2 = v) :
    (ManyBody.Edge.map φ e).1.1 = φ v ∨ (ManyBody.Edge.map φ e).1.2 = φ v := by
  rcases ManyBody.Edge.map_endpoints φ e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h with hv | hv
    · exact Or.inl (by rw [h1, hv])
    · exact Or.inr (by rw [h2, hv])
  · rcases h with hv | hv
    · exact Or.inr (by rw [h2, hv])
    · exact Or.inl (by rw [h1, hv])

/-- The correspondence between edges incident to `v` and edges incident to `φ v`,
as a bijection.  The underlying map is the edge action `Edge.map φ`; the incidence
is preserved because `φ` sends the endpoint equal to `v` to one equal to `φ v`. -/
def IncidentEdge.equiv (φ : G ≃g G') (v : V) :
    IncidentEdge G v ≃ IncidentEdge G' (φ v) :=
  (ManyBody.Edge.equiv φ).subtypeEquiv fun e => by
    constructor
    · intro h
      exact ManyBody.Edge.map_incident φ h
    · intro h
      have h' := ManyBody.Edge.map_incident φ.symm (v := φ v) h
      simpa using h'

/-- The edge incident to `φ.symm w` carried to an edge incident to `w` (not merely
to `φ (φ.symm w)`).  The membership at `w` is recomputed from `Edge.map_incident`
through `φ (φ.symm w) = w`, avoiding a transport across the incidence-vertex index.
This is the form consumed in the transported tensor's component, where the vertex
of `G'` is `w` and its `G`-preimage is `φ.symm w`. -/
def IncidentEdge.toSymm (φ : G ≃g G') (w : W) (ie : IncidentEdge G (φ.symm w)) :
    IncidentEdge G' w :=
  ⟨ManyBody.Edge.map φ ie.1, by
    have h := ManyBody.Edge.map_incident φ ie.2
    rwa [φ.apply_symm_apply] at h⟩

/-- The inverse of `IncidentEdge.toSymm`: carry an edge incident to `w` back
through `φ.symm`, obtaining an edge incident to `φ.symm w`. -/
def IncidentEdge.fromSymm (φ : G ≃g G') (w : W) (ie' : IncidentEdge G' w) :
    IncidentEdge G (φ.symm w) :=
  ⟨ManyBody.Edge.map φ.symm ie'.1, ManyBody.Edge.map_incident φ.symm ie'.2⟩

omit [Fintype V] [Fintype W] in
@[simp] theorem IncidentEdge.toSymm_coe (φ : G ≃g G') (w : W)
    (ie : IncidentEdge G (φ.symm w)) :
    (IncidentEdge.toSymm φ w ie).1 = ManyBody.Edge.map φ ie.1 :=
  rfl

omit [Fintype V] [Fintype W] in
@[simp] theorem IncidentEdge.fromSymm_coe (φ : G ≃g G') (w : W)
    (ie' : IncidentEdge G' w) :
    (IncidentEdge.fromSymm φ w ie').1 = ManyBody.Edge.map φ.symm ie'.1 :=
  rfl

omit [Fintype V] [Fintype W] in
/-- Every edge incident to `w` comes from an edge incident to `φ.symm w`. -/
theorem IncidentEdge.toSymm_surjective (φ : G ≃g G') (w : W) :
    Function.Surjective (IncidentEdge.toSymm φ w) := by
  intro ie'
  refine ⟨IncidentEdge.fromSymm φ w ie', ?_⟩
  apply Subtype.ext
  simp only [IncidentEdge.toSymm_coe, IncidentEdge.fromSymm_coe,
    ManyBody.Edge.map_map_symm]

end EdgeAction

variable {V W : Type*} [LinearOrder V] [LinearOrder W]
variable {Γ : SimpleGraph V} {Γ' : SimpleGraph W}

/-- Equality of native sorted edges is equality of their unordered endpoints.
Auxiliary to SCP10, seam-aware flux movement, lines 2271–2305. -/
theorem _root_.ManyBody.Edge.ofAdj_eq_iff_endpoints {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
    {x y a b : V} (hxy : Γ.Adj x y) (hab : Γ.Adj a b) :
    ManyBody.Edge.ofAdj hxy = ManyBody.Edge.ofAdj hab ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  constructor
  · intro h
    rcases ManyBody.Edge.ofAdj_endpoints hxy with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩ <;>
      rcases ManyBody.Edge.ofAdj_endpoints hab with ⟨h₂,h₃⟩ | ⟨h₂,h₃⟩ <;> grind
  · exact ManyBody.Edge.ofAdj_eq_ofAdj hxy hab

/-- A constant endpoint coordinate distinguishes two native edges whenever one
endpoint of the other edge has a different coordinate. Auxiliary to SCP10,
local flux geometries, lines 2271–2305 and 2380–2415. -/
theorem _root_.ManyBody.Edge.ofAdj_ne_of_endpoint_coordinates {Y : Type*} {x y a b : V}
    (hxy : Γ.Adj x y) (hab : Γ.Adj a b) (f : V → Y)
    (hc : f a = f b) (hne : f x ≠ f a ∨ f y ≠ f a) :
    ManyBody.Edge.ofAdj hxy ≠ ManyBody.Edge.ofAdj hab := by
  intro heq
  rcases (ManyBody.Edge.ofAdj_eq_iff_endpoints hxy hab).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne.elim (fun h => h rfl) (fun h => h hc.symm)
  · exact hne.elim (fun h => h hc.symm) (fun h => h rfl)

/-- Adjacency in a transported graph agrees with adjacency of the original
ordered endpoints, even when their order reverses. Auxiliary to SCP10,
finite local blocking and flux geometries, lines 1765–1920 and 2380–2415. -/
theorem _root_.ManyBody.Edge.comap_adj_map_iff (φ : Γ ≃g Γ') (T : SimpleGraph V) (e : Edge Γ) :
    (T.comap φ.symm).Adj (ManyBody.Edge.map φ e).1.1 (ManyBody.Edge.map φ e).1.2 ↔
        T.Adj e.1.1 e.1.2 := by
  rcases ManyBody.Edge.map_endpoints φ e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [SimpleGraph.comap_adj, h₁, h₂, RelIso.symm_apply_apply]
  · simp only [SimpleGraph.comap_adj, h₁, h₂, RelIso.symm_apply_apply, SimpleGraph.adj_comm]

section EndpointIncidence

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

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

end EndpointIncidence

section RegionMap

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-! ### The image region of a graph isomorphism -/

/-- The image of a finite region `R` of `G` under the vertex bijection of `φ`. -/
def Region.map (φ : G ≃g G') (R : Finset V) : Finset W :=
  R.map φ.toEquiv.toEmbedding

omit [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
@[simp] theorem mem_Region_map (φ : G ≃g G') (R : Finset V) (w : W) :
    w ∈ Region.map φ R ↔ φ.symm w ∈ R := by
  simp only [Region.map, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [show (φ.toEquiv : V → W) v = φ v from rfl,
      show φ.symm (φ v) = v from φ.symm_apply_apply v]; exact hv
  · intro h
    refine ⟨φ.symm w, h, ?_⟩
    rw [show (φ.toEquiv : V → W) (φ.symm w) = φ (φ.symm w) from rfl, φ.apply_symm_apply w]

omit [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- A vertex `v` lies in `R` iff `φ v` lies in the image region. -/
theorem mem_Region_map_apply (φ : G ≃g G') (R : Finset V) (v : V) :
    φ v ∈ Region.map φ R ↔ v ∈ R := by
  rw [mem_Region_map]
  rw [show φ.symm (φ v) = v from φ.symm_apply_apply v]

end RegionMap

section IncidentProducts

open scoped BigOperators

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Incidences of vertices with edges are the same as choosing an edge and one
of its two ordered endpoints. -/
private noncomputable def incidentSigmaEquivEdgeSide :
    (Sigma fun v : V => IncidentEdge G v) ≃ Edge G × Fin 2 where
  toFun x :=
    let e := x.2.1
    ⟨e, if e.1.1 = x.1 then 0 else 1⟩
  invFun y :=
    match y.2 with
    | 0 => ⟨y.1.1.1, edgeLeftIncident (G := G) y.1⟩
    | 1 => ⟨y.1.1.2, edgeRightIncident (G := G) y.1⟩
  left_inv x := by
    rcases x with ⟨v, ie⟩
    rcases ie with ⟨e, hinc⟩
    dsimp
    by_cases hleft : e.1.1 = v
    · subst v
      simp only [↓reduceIte, Fin.isValue, Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext rfl
    · have hright : e.1.2 = v := by
        rcases hinc with h | h
        · exact False.elim (hleft h)
        · exact h
      subst v
      have hne : ¬e.1.1 = e.1.2 := ne_of_lt e.2.1
      simp only [hne, ↓reduceIte, Fin.isValue, Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext rfl
  right_inv y := by
    rcases y with ⟨e, side⟩
    fin_cases side
    · dsimp [edgeLeftIncident]
      simp
    · have hne : ¬e.1.1 = e.1.2 := ne_of_lt e.2.1
      dsimp [edgeRightIncident]
      simp [hne]

/-- A product over all incident half-edges factors as the product, over graph
edges, of the two endpoint contributions. -/
lemma prod_incident_eq_prod_edge (f : (v : V) → IncidentEdge G v → ℂ) :
    (∏ v : V, ∏ ie : IncidentEdge G v, f v ie) =
      ∏ e : Edge G,
        f e.1.1 (edgeLeftIncident (G := G) e) *
          f e.1.2 (edgeRightIncident (G := G) e) := by
  rw [← Fintype.prod_sigma']
  calc
    (∏ x : Sigma fun v : V => IncidentEdge G v, f x.1 x.2)
        = ∏ y : Edge G × Fin 2,
            f ((incidentSigmaEquivEdgeSide (G := G)).symm y).1
              ((incidentSigmaEquivEdgeSide (G := G)).symm y).2 := by
          let e := incidentSigmaEquivEdgeSide (G := G)
          calc
            (∏ x : Sigma fun v : V => IncidentEdge G v, f x.1 x.2)
                = ∏ x : Sigma fun v : V => IncidentEdge G v,
                    f (e.symm (e x)).1 (e.symm (e x)).2 := by
                  refine Finset.prod_congr rfl ?_
                  intro x hx
                  rw [Equiv.symm_apply_apply]
            _ = ∏ y : Edge G × Fin 2, f (e.symm y).1 (e.symm y).2 := by
                  exact e.prod_comp
                    (fun y : Edge G × Fin 2 => f (e.symm y).1 (e.symm y).2)
    _ = ∏ e : Edge G, ∏ side : Fin 2,
            f ((incidentSigmaEquivEdgeSide (G := G)).symm (e, side)).1
              ((incidentSigmaEquivEdgeSide (G := G)).symm (e, side)).2 := by
          rw [Fintype.prod_prod_type]
    _ = ∏ e : Edge G,
        f e.1.1 (edgeLeftIncident (G := G) e) *
          f e.1.2 (edgeRightIncident (G := G) e) := by
          refine Finset.prod_congr rfl ?_
          intro e he
          rw [Fin.prod_univ_two]
          simp [incidentSigmaEquivEdgeSide]

/-- **Region incidence product regrouped by edges.**

The product, over the vertices of a region `R`, of a per-incidence factor `f w ie` over the edges
`ie` incident to `w`, regroups edge by edge: each edge contributes its left-endpoint factor when
that endpoint lies in `R` (and `1` otherwise) times its right-endpoint factor when that endpoint
lies in `R` (and `1` otherwise).

This is the region-restricted analogue of `prod_incident_eq_prod_edge`.  An edge with both
endpoints in `R` contributes both factors; a boundary edge of `R` contributes exactly one; an edge
disjoint from `R` contributes nothing.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem prod_region_incident_eq_prod_edge (R : Finset V) (f : (w : V) → IncidentEdge G w → ℂ) :
    (∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1, f w.1 ie) =
      ∏ e : Edge G,
        (if e.1.1 ∈ R then f e.1.1 (edgeLeftIncident (G := G) e) else 1) *
          (if e.1.2 ∈ R then f e.1.2 (edgeRightIncident (G := G) e) else 1) := by
  classical
  have hLHS : (∏ w : {w : V // w ∈ R}, ∏ ie : IncidentEdge G w.1, f w.1 ie) =
      ∏ w : V, ∏ ie : IncidentEdge G w,
        (if w ∈ R then f w ie else (1 : ℂ)) := by
    rw [Finset.prod_coe_sort R (fun w => ∏ ie : IncidentEdge G w, f w ie)]
    have hsub : (∏ w ∈ R, ∏ ie : IncidentEdge G w, (if w ∈ R then f w ie else (1 : ℂ)))
        = ∏ w ∈ (Finset.univ : Finset V), ∏ ie : IncidentEdge G w,
            (if w ∈ R then f w ie else (1 : ℂ)) :=
      Finset.prod_subset (Finset.subset_univ R) (fun w _ hw =>
        Finset.prod_eq_one (fun ie _ => by rw [ite_eq_right hw]))
    rw [← hsub]
    refine Finset.prod_congr rfl (fun w hw => ?_)
    refine Finset.prod_congr rfl (fun ie _ => ?_)
    rw [ite_eq_left hw]
  rw [hLHS, prod_incident_eq_prod_edge (G := G) (fun w ie => if w ∈ R then f w ie else (1 : ℂ))]

end IncidentProducts

end TNLean.PEPS
