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

/-- Vertex-wise injectivity: at each vertex `v`, the family of physical vectors
`η ↦ A.component v η` (indexed by virtual configurations on the incident edges)
is linearly independent in `Fin d → ℂ`.

This matches the paper's definition (arXiv:1804.04964 §3, line 979):
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
