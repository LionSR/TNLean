import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# PEPS definitions on finite simple graphs

This file introduces the finite-graph PEPS tensor objects.
The index types (`Edge`, `IncidentEdge`, `VirtualConfig`) are the combinatorial
index sets for PEPS tensors on a finite simple graph.

## Design note on decidability

We keep `[DecidableRel G.Adj]` explicit (rather than deriving locally) because
edge/incident-edge index types are subtypes over adjacency and are used in
finite sums/products. Keeping adjacency decidable at module scope makes
instance synthesis for `Fintype` predictable.
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Undirected edges of `G`, represented by ordered endpoint pairs `(u, v)` with
`u < v` to avoid double-counting. -/
abbrev Edge (G : SimpleGraph V) : Type _ :=
  { uv : V × V // uv.1 < uv.2 ∧ G.Adj uv.1 uv.2 }

instance instFintypeEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (Edge G) :=
  inferInstance

/-- The edge of `G` on an adjacent pair `(u, v)`, with the endpoints reordered into
the `Edge` convention `·.1 < ·.2`.  Adjacency forbids `u = v`, so exactly one of
`u < v` and `v < u` holds; the smaller endpoint is placed first.  This normalizes an
unordered adjacent pair into the ordered-endpoint `Edge` representation, the operation
needed to push an edge through a vertex bijection (such as a translation), where the
bijection may swap the lexicographic order of the two endpoints. -/
def Edge.ofAdj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : Edge G :=
  if huv : u < v then
    ⟨(u, v), huv, h⟩
  else
    ⟨(v, u), lt_of_le_of_ne (not_lt.mp huv) (G.ne_of_adj h).symm, h.symm⟩

omit [Fintype V] in
/-- On a pair already in order (`u < v`), `Edge.ofAdj` keeps the endpoints as given. -/
theorem Edge.ofAdj_of_lt {G : SimpleGraph V} {u v : V} (h : G.Adj u v) (huv : u < v) :
    Edge.ofAdj h = ⟨(u, v), huv, h⟩ := by
  rw [Edge.ofAdj, dif_pos huv]

omit [Fintype V] in
/-- On a pair in reverse order (`v < u`), `Edge.ofAdj` swaps the endpoints. -/
theorem Edge.ofAdj_of_gt {G : SimpleGraph V} {u v : V} (h : G.Adj u v) (hvu : v < u) :
    Edge.ofAdj h =
      ⟨(v, u), hvu, h.symm⟩ := by
  rw [Edge.ofAdj, dif_neg (not_lt.mpr hvu.le)]

omit [Fintype V] in
/-- The unordered endpoint set of `Edge.ofAdj h` is `{u, v}`: its two endpoints are
`u` and `v` in some order. -/
theorem Edge.ofAdj_endpoints {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    ((Edge.ofAdj h).1.1 = u ∧ (Edge.ofAdj h).1.2 = v) ∨
      ((Edge.ofAdj h).1.1 = v ∧ (Edge.ofAdj h).1.2 = u) := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with huv | hvu
  · exact Or.inl ⟨by rw [Edge.ofAdj_of_lt h huv], by rw [Edge.ofAdj_of_lt h huv]⟩
  · exact Or.inr ⟨by rw [Edge.ofAdj_of_gt h hvu], by rw [Edge.ofAdj_of_gt h hvu]⟩

omit [Fintype V] in
/-- `Edge.ofAdj` recovers an edge from either of its incidence directions. -/
@[simp] theorem Edge.ofAdj_fst_snd {G : SimpleGraph V} (e : Edge G) :
    Edge.ofAdj e.2.2 = e := by
  rw [Edge.ofAdj_of_lt e.2.2 e.2.1]

omit [Fintype V] in
/-- The image edge `Edge.ofAdj h` is independent of the incidence direction of the
adjacency `h`: orienting the pair `(u, v)` and the pair `(v, u)` gives the same
edge, since `Edge.ofAdj` places the smaller endpoint first either way. -/
theorem Edge.ofAdj_symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    Edge.ofAdj h = Edge.ofAdj h.symm := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with huv | hvu
  · rw [Edge.ofAdj_of_lt h huv, Edge.ofAdj_of_gt h.symm huv]
  · rw [Edge.ofAdj_of_gt h hvu, Edge.ofAdj_of_lt h.symm hvu]

omit [Fintype V] in
/-- An edge is determined by its unordered endpoint pair: if `(u, v)` is, in some
order, the ordered endpoint pair of `e`, then orienting `(u, v)` with `Edge.ofAdj`
recovers `e`. This is the bookkeeping that makes edge constructions independent
of the order in which an unordered adjacent pair is presented. -/
theorem Edge.ofAdj_eq_of_endpoints {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
    (e : Edge G)
    (H : (u = e.1.1 ∧ v = e.1.2) ∨ (u = e.1.2 ∧ v = e.1.1)) :
    Edge.ofAdj h = e := by
  apply Subtype.ext
  rcases Edge.ofAdj_endpoints h with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;>
    rcases H with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Prod.ext (o1.trans hu) (o2.trans hv)
  · exfalso
    have hlt : (Edge.ofAdj h).1.1 < (Edge.ofAdj h).1.2 := (Edge.ofAdj h).2.1
    rw [o1, o2, hu, hv] at hlt
    exact absurd hlt (not_lt.mpr e.2.1.le)
  · exfalso
    have hlt : (Edge.ofAdj h).1.1 < (Edge.ofAdj h).1.2 := (Edge.ofAdj h).2.1
    rw [o1, o2, hu, hv] at hlt
    exact absurd hlt (not_lt.mpr e.2.1.le)
  · exact Prod.ext (o1.trans hv) (o2.trans hu)

omit [Fintype V] in
/-- Two `Edge.ofAdj` constructions agree when their adjacent pairs have the same
unordered endpoints: orienting `(u, v)` and `(u', v')` gives the same edge
whenever `{u, v} = {u', v'}`. -/
theorem Edge.ofAdj_eq_ofAdj {G : SimpleGraph V} {u v u' v' : V} (h1 : G.Adj u v)
    (h2 : G.Adj u' v')
    (H : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')) :
    Edge.ofAdj h1 = Edge.ofAdj h2 := by
  rw [Edge.ofAdj_eq_of_endpoints h1 (Edge.ofAdj h2)]
  rcases Edge.ofAdj_endpoints h2 with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;> rw [o1, o2] <;> tauto

/-- Edges incident to a vertex `v`. -/
abbrev IncidentEdge (G : SimpleGraph V) (v : V) : Type _ :=
  { e : Edge G // e.1.1 = v ∨ e.1.2 = v }

instance instFintypeIncidentEdge (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype (IncidentEdge G v) :=
  inferInstance

/-- A PEPS tensor family with one physical index per vertex and edge-dependent
virtual bond dimensions. -/
structure Tensor (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) where
  bondDim : Edge G → ℕ
  component : (v : V) → ((ie : IncidentEdge G v) → Fin (bondDim ie.1)) → Fin d → ℂ

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- A global assignment of virtual indices to all edges. -/
abbrev VirtualConfig (A : Tensor G d) : Type _ :=
  (e : Edge G) → Fin (A.bondDim e)

instance instFintypeVirtualConfig (A : Tensor G d) : Fintype (VirtualConfig A) :=
  inferInstance

/-- PEPS state coefficient for a physical configuration `σ`, obtained by
contracting all virtual indices. -/
noncomputable def stateCoeff (A : Tensor G d) (σ : V → Fin d) : ℂ :=
  ∑ η : VirtualConfig A,
    ∏ v : V, A.component v (fun ie => η ie.1) (σ v)

/-- Two PEPS tensors represent the same state when all coefficients agree. -/
def SameState (A B : Tensor G d) : Prop :=
  ∀ σ : V → Fin d, stateCoeff A σ = stateCoeff B σ

/-- `SameState` is symmetric: it is equality of all state coefficients. -/
theorem SameState.symm {A B : Tensor G d} (hAB : SameState A B) : SameState B A :=
  fun σ => (hAB σ).symm

/-- Vertex-wise injectivity: at each vertex `v`, the family of physical vectors
`η ↦ A.component v η` (indexed by virtual configurations on the incident edges)
is linearly independent in `Fin d → ℂ`.

This matches the paper's definition (arXiv:1804.04964 Section 3, line 979):
> *"all tensors interpreted as maps from the virtual space to the physical one
> are injective"*

interpreted linear-algebraically: extending `A.component v` by linearity to a
map from the free `ℂ`-vector space on virtual configurations into the physical
space `ℂ^d`, that map has trivial kernel iff the family `A.component v` is
linearly independent.

Note: the earlier `Function.Injective (A.component v)` formulation is *strictly
weaker* and admits counterexamples to the former global-scalar uniqueness
claim for PEPS gauges (see issues #594 and #762). Linear independence is the
correct notion here. -/
def IsVertexInjective (A : Tensor G d) : Prop :=
  ∀ v : V, LinearIndependent ℂ (A.component v)

end PEPS
end TNLean
