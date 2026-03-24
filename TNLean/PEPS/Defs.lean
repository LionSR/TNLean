import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# Exploratory PEPS definitions on finite simple graphs

This file introduces a lightweight PEPS scaffold on a finite graph.

## Design note on decidability

We keep `[DecidableRel G.Adj]` explicit (rather than deriving locally) because
edge/incident-edge index types are subtypes over adjacency and are used in
computable finite sums/products (`stateCoeff`). Keeping adjacency decidable at
module scope makes these constructions and instance synthesis predictable.
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Undirected edges of `G`, represented by ordered endpoint pairs `(u, v)` with
`u < v` to avoid double-counting. -/
def Edge (G : SimpleGraph V) : Type _ :=
  { uv : V × V // uv.1 < uv.2 ∧ G.Adj uv.1 uv.2 }


instance instFintypeEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (Edge G) := by
  classical
  unfold Edge
  infer_instance

/-- Edges incident to a vertex `v`. -/
def IncidentEdge (G : SimpleGraph V) (v : V) : Type _ :=
  { e : Edge G // e.1.1 = v ∨ e.1.2 = v }

/-- A PEPS tensor family with one physical index per vertex and edge-dependent
virtual bond dimensions. -/
structure Tensor (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) where
  bondDim : Edge G → ℕ
  tensor : (v : V) → ((ie : IncidentEdge G v) → Fin (bondDim ie.1)) → Fin d → ℂ

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- A global assignment of virtual indices to all edges. -/
def VirtualConfig (A : Tensor G d) : Type _ :=
  (e : Edge G) → Fin (A.bondDim e)

noncomputable instance instFintypeVirtualConfig (A : Tensor G d) : Fintype (VirtualConfig A) := by
  letI : Fintype (Edge G) := inferInstance
  letI : ∀ e : Edge G, Fintype (Fin (A.bondDim e)) := fun _ => inferInstance
  simpa [VirtualConfig] using
    (show Fintype ((e : Edge G) → Fin (A.bondDim e)) from (open Classical in inferInstance))

/-- PEPS state coefficient for a physical configuration `σ`, obtained by
contracting all virtual indices. -/
noncomputable def stateCoeff (A : Tensor G d) (σ : V → Fin d) : ℂ :=
  ∑ η : VirtualConfig A,
    ∏ v : V, A.tensor v (fun ie => η ie.1) (σ v)

/-- Two PEPS tensors represent the same state when all coefficients agree. -/
def SameState (A B : Tensor G d) : Prop :=
  ∀ σ : V → Fin d, stateCoeff A σ = stateCoeff B σ

/-- Vertex-wise injectivity: each local tensor map (virtual → physical data) is
injective. This is a basic exploratory surrogate for PEPS injectivity. -/
def IsVertexInjective (A : Tensor G d) : Prop :=
  ∀ v : V, Function.Injective (A.tensor v)

end PEPS
end TNLean
