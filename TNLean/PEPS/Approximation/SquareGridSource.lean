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
structure Tensor (q L : ℕ) where
  bondDim : ForwardEdge L → ℕ
  bondDim_pos : ∀ e, 0 < bondDim e
  tensor : ∀ v : Vertex L,
    ((e : IncidentEdge L v) → Fin (bondDim e.val)) → Fin q → ℂ

/-- Adapted from `PolynomialPEPS.PEPS.contract`, VectorColumn.lean lines 77–81. -/
def Tensor.contract {q L : ℕ} (P : Tensor q L) : State q L :=
  WithLp.toLp 2 (fun x => ∑ a : (e : ForwardEdge L) → Fin (P.bondDim e),
    ∏ v : Vertex L, P.tensor v (fun e => a e.val) (x v))

/-- Adapted from `PolynomialPEPS.PEPS.maxBondDim`; the empty supremum is zero. -/
def Tensor.maxBondDim {q L : ℕ} (P : Tensor q L) : ℕ := by
  classical
  exact Finset.univ.sup P.bondDim

end Vector
end TNLean.PEPS.Approximation
