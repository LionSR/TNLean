/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Adapted definitions from openai/math, Apache-2.0, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a:
lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean (Pinned below), and
lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean (Vector below).
Changes: namespaces, shared forward-edge spelling, explicit finite instances,
and imports. The two incidence conventions, tensor argument orders, positivity
requirements and State parameter orders are retained. No upstream proofs copied.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import TNLean.PEPS.SquareLatticeGraph

/-
Provenance ledger: docs/provenance/openai-math.d/8740.json.
Adapted from OpenAI's openai/math repository (Apache-2.0).
Upstream revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Changes: renamed namespaces, shared forward-edge spelling, narrowed imports and explicit finite instances.
Retained both incidence conventions, tensor argument orders, State parameter orders and positivity.
No upstream Lean proofs are copied.
Provenance-ID: 8740-vertex
Downstream: TNLean.PEPS.Approximation.Vertex
Upstream: OAI.PolynomialPEPS.PinnedEntropy.Vertex
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L12-L12
Provenance-ID: 8740-forwardadjacent
Downstream: TNLean.PEPS.Approximation.ForwardAdjacent
Upstream: OAI.PolynomialPEPS.PinnedEntropy.ForwardAdjacent
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L14-L14
Provenance-ID: 8740-forwardedge
Downstream: TNLean.PEPS.Approximation.ForwardEdge
Upstream: OAI.PolynomialPEPS.PinnedEntropy.Edge
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L18-L18
Provenance-ID: 8740-pinned-incidentedge
Downstream: TNLean.PEPS.Approximation.Pinned.IncidentEdge
Upstream: OAI.PolynomialPEPS.PinnedEntropy.IncidentEdge
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L25-L25
Provenance-ID: 8740-pinned-state
Downstream: TNLean.PEPS.Approximation.Pinned.State
Upstream: OAI.PolynomialPEPS.PinnedEntropy.State
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L30-L30
Provenance-ID: 8740-pinned-localtensor
Downstream: TNLean.PEPS.Approximation.Pinned.LocalTensor
Upstream: OAI.PolynomialPEPS.PinnedEntropy.LocalTensor
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L80-L80
Provenance-ID: 8740-pinned-contractpeps
Downstream: TNLean.PEPS.Approximation.Pinned.contractPEPS
Upstream: OAI.PolynomialPEPS.PinnedEntropy.contractPEPS
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean#L83-L83
Provenance-ID: 8740-vector-incidentedge
Downstream: TNLean.PEPS.Approximation.Vector.IncidentEdge
Upstream: OAI.PolynomialPEPS.IncidentEdge
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L22-L22
Provenance-ID: 8740-vector-state
Downstream: TNLean.PEPS.Approximation.Vector.State
Upstream: OAI.PolynomialPEPS.State
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L26-L26
Provenance-ID: 8740-vector-peps
Downstream: TNLean.PEPS.Approximation.Vector.PEPS
Upstream: OAI.PolynomialPEPS.PEPS
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L68-L68
Provenance-ID: 8740-vector-peps-contract
Downstream: TNLean.PEPS.Approximation.Vector.PEPS.contract
Upstream: OAI.PolynomialPEPS.PEPS.contract
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L78-L78
Provenance-ID: 8740-vector-peps-maxbonddim
Downstream: TNLean.PEPS.Approximation.Vector.PEPS.maxBondDim
Upstream: OAI.PolynomialPEPS.PEPS.maxBondDim
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L83-L83
-/

/-!
# The two source square-grid PEPS presentations

These are restricted adaptations of the definitions preceding the approximation
statements, not ports of those statements or their proofs. The mathematical source
is the September 24 polynomial PEPS manuscript, introduction, lines 20–34.
The native public tensor remains `TNLean.PEPS.Tensor`.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- Open square-grid vertices; both upstream presentations use these coordinates. -/
abbrev Vertex (L : ℕ) := Fin L × Fin L

/-- Adapted from `PinnedEntropy.ForwardAdjacent`: only right and up, without wraparound. -/
def ForwardAdjacent {L : ℕ} (v w : Vertex L) : Prop :=
  (v.1.val + 1 = w.1.val ∧ v.2 = w.2) ∨
  (v.1 = w.1 ∧ v.2.val + 1 = w.2.val)

/-- The common forward-edge subtype in the two upstream presentations. -/
abbrev ForwardEdge (L : ℕ) :=
  {e : Vertex L × Vertex L // ForwardAdjacent e.1 e.2}

instance (L : ℕ) : Fintype (ForwardEdge L) := Fintype.ofFinite _

namespace Pinned

/-- Adapted from `PinnedEntropy.IncidentEdge`; the vertex occurs on the left. -/
abbrev IncidentEdge {L : ℕ} (v : Vertex L) :=
  {e : ForwardEdge L // v = e.val.1 ∨ v = e.val.2}

instance {L : ℕ} (v : Vertex L) : Fintype (IncidentEdge v) := Fintype.ofFinite _

/-- Adapted from `PinnedEntropy.State`; lattice size precedes physical dimension. -/
abbrev State (L q : ℕ) := EuclideanSpace ℂ (Vertex L → Fin q)

/-- Adapted from `PinnedEntropy.LocalTensor`, with the physical argument first. -/
abbrev LocalTensor {L : ℕ} (q : ℕ) (D : ForwardEdge L → ℕ) (v : Vertex L) :=
  Fin q → ((e : IncidentEdge v) → Fin (D e.val)) → ℂ

/-- Adapted from `PinnedEntropy.contractPEPS`, Basic.lean lines 80–84. -/
def contractPEPS {L q : ℕ} (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → LocalTensor q D v) : State L q :=
  WithLp.toLp 2 (fun x => ∑ a : (e : ForwardEdge L) → Fin (D e),
    ∏ v : Vertex L, A v (x v) (fun e => a e.val))

end Pinned

namespace Vector

/-- Adapted from `PolynomialPEPS.IncidentEdge`; endpoints occur on the left. -/
abbrev IncidentEdge (L : ℕ) (v : Vertex L) :=
  {e : ForwardEdge L // e.val.1 = v ∨ e.val.2 = v}

instance {L : ℕ} (v : Vertex L) : Fintype (IncidentEdge L v) := Fintype.ofFinite _

/-- Adapted from `PolynomialPEPS.State`; physical dimension precedes lattice size. -/
abbrev State (q L : ℕ) := EuclideanSpace ℂ (Vertex L → Fin q)

/-- Adapted from `PolynomialPEPS.PEPS`, VectorColumn.lean lines 66–71.
Unlike a native graph tensor, this source structure requires positive dimensions. -/
structure PEPS (q L : ℕ) where
  bondDim : ForwardEdge L → ℕ
  bondDim_pos : ∀ e, 0 < bondDim e
  tensor : ∀ v : Vertex L,
    ((e : IncidentEdge L v) → Fin (bondDim e.val)) → Fin q → ℂ

/-- Adapted from `PolynomialPEPS.PEPS.contract`, VectorColumn.lean lines 77–81. -/
def PEPS.contract {q L : ℕ} (P : PEPS q L) : State q L :=
  WithLp.toLp 2 (fun x => ∑ a : (e : ForwardEdge L) → Fin (P.bondDim e),
    ∏ v : Vertex L, P.tensor v (fun e => a e.val) (x v))

/-- Adapted from `PolynomialPEPS.PEPS.maxBondDim`; the empty supremum is zero. -/
def PEPS.maxBondDim {q L : ℕ} (P : PEPS q L) : ℕ := by
  classical
  exact Finset.univ.sup P.bondDim

end Vector
end TNLean.PEPS.Approximation
