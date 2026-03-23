import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Basic PEPS definitions on finite simple graphs

This file sets up a minimal Lean 4 interface for PEPS on a finite graph:

* a vertex-local tensor with one physical index and one virtual index per incident edge,
* the PEPS state coefficient obtained by contracting all virtual indices,
* vertexwise injectivity as injectivity of the local virtual-to-physical map.
-/

open scoped BigOperators

/-- Undirected edges of a simple graph, as a finite index type. -/
abbrev Edge {n : ℕ} (G : SimpleGraph (Fin n)) : Type :=
  {e : Sym2 (Fin n) // e ∈ G.edgeSet}

/-- Edges incident to a fixed vertex `v`. -/
abbrev IncidentEdge {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Type :=
  {e : Edge G // v ∈ (e.1 : Sym2 (Fin n))}

/-- Minimal PEPS data on `SimpleGraph (Fin n)` with physical dimension `d`.

Bond dimensions are allowed to vary by edge. -/
structure PEPS (n d : ℕ) where
  G : SimpleGraph (Fin n)
  /-- Bond dimension on each undirected edge. -/
  bondDim : Edge G → ℕ
  /-- A local PEPS tensor at vertex `v`: virtual indices on incident edges,
  and one physical index in `Fin d`. -/
  tensor : (v : Fin n) → ((ie : IncidentEdge G v) → Fin (bondDim ie.1)) → Fin d → ℂ

namespace PEPS

variable {n d : ℕ}

noncomputable instance instFintypeEdge (A : PEPS n d) : Fintype (Edge A.G) :=
  Fintype.ofFinite (Edge A.G)

/-- A global assignment of all virtual indices (one per edge). -/
abbrev VirtualConfig (A : PEPS n d) : Type :=
  (e : Edge A.G) → Fin (A.bondDim e)

noncomputable instance instFintypeVirtualConfig (A : PEPS n d) :
    Fintype (VirtualConfig A) := by
  classical
  infer_instance

/-- The local virtual-to-physical map at vertex `v`. -/
def vertexMap (A : PEPS n d) (v : Fin n) :
    ((ie : IncidentEdge A.G v) → Fin (A.bondDim ie.1)) → (Fin d → ℂ) :=
  fun ξ i => A.tensor v ξ i

/-- Coefficient of the PEPS state on a physical basis configuration `σ`.

This is the contraction of all virtual indices along edges: sum over global
virtual assignments, product of local tensor entries. -/
noncomputable def stateCoeff (A : PEPS n d) (σ : Fin n → Fin d) : ℂ :=
  ∑ ξ : VirtualConfig A, ∏ v : Fin n, A.tensor v (fun ie => ξ ie.1) (σ v)

/-- Two PEPS define the same state if all computational-basis coefficients agree. -/
def SameState (A B : PEPS n d) : Prop :=
  ∀ σ : Fin n → Fin d, stateCoeff A σ = stateCoeff B σ

/-- Vertexwise injectivity: each local virtual-to-physical map is injective. -/
def IsInjective (A : PEPS n d) : Prop :=
  ∀ v : Fin n, Function.Injective (vertexMap A v)

end PEPS
