/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridBounds
import TNLean.PEPS.Approximation.RegionalStates

/-! # Square-grid representation regressions -/

open scoped BigOperators
open TNLean.PEPS TNLean.PEPS.Approximation

noncomputable section

namespace SquareGridStateTransportTest

example {L q : ℕ} (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor D A)) = Pinned.contractPEPS D A :=
  stateVector_pinnedTensorToGraphTensor D A

example {q : ℕ} (D : ForwardEdge 0 → ℕ)
    (A : (v : Vertex 0) → Pinned.LocalTensor q D v)
    (σ : Vertex 0 → Fin q) :
    stateCoeff (pinnedTensorToGraphTensor D A) σ = 1 := by
  rw [stateCoeff_pinnedTensorToGraphTensor]
  simp [Pinned.contractPEPS]

example (D : ForwardEdge 0 → ℕ)
    (A : (v : Vertex 0) → Pinned.LocalTensor 0 D v)
    (σ : Vertex 0 → Fin 0) :
    stateCoeff (pinnedTensorToGraphTensor D A) σ = 1 := by
  rw [stateCoeff_pinnedTensorToGraphTensor]
  simp [Pinned.contractPEPS]

example (D : ForwardEdge 1 → ℕ)
    (A : (v : Vertex 1) → Pinned.LocalTensor 0 D v) :
    WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor D A)) = 0 := by
  ext σ
  exact Fin.elim0 (σ (0, 0))

example {L q : ℕ} (b : Vertex L → Fin q → ℂ)
    (σ : Vertex L → Fin q) :
    stateCoeff (pinnedTensorToGraphTensor (fun _ => 1) (fun v i _ => b v i)) σ =
      ∏ v, b v (σ v) := by
  rw [stateCoeff_pinnedTensorToGraphTensor]
  simp [Pinned.contractPEPS]

example {L q : ℕ} (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v)
    (e : ForwardEdge L) (he : D e = 0) :
    WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor D A)) = 0 := by
  let : IsEmpty ((f : ForwardEdge L) → Fin (D f)) := ⟨fun η => by
    have h := (η e).isLt
    omega⟩
  rw [stateVector_pinnedTensorToGraphTensor]
  ext σ
  simp [Pinned.contractPEPS]

/-- The two bonds meeting the lower-left corner have different dimensions. -/
def heterogeneousDim (e : ForwardEdge 2) : ℕ :=
  if e.val.1.1 = e.val.2.1 then 3 else 2

/-- The lower horizontal bond. -/
def rightEdge : ForwardEdge 2 := ⟨((0, 0), (1, 0)), Or.inl ⟨rfl, rfl⟩⟩

/-- The left vertical bond. -/
def upEdge : ForwardEdge 2 := ⟨((0, 0), (0, 1)), Or.inr ⟨rfl, rfl⟩⟩

example (A : (v : Vertex 2) → Pinned.LocalTensor 2 heterogeneousDim v) :
    (pinnedTensorToGraphTensor heterogeneousDim A).bondDim
        (forwardSquareEdgeEquiv 2 rightEdge) = 2 ∧
      (pinnedTensorToGraphTensor heterogeneousDim A).bondDim
        (forwardSquareEdgeEquiv 2 upEdge) = 3 := by
  constructor <;> rfl

example (A : (v : Vertex 2) → Pinned.LocalTensor 2 heterogeneousDim v)
    (η : (e : ForwardEdge 2) → Fin (heterogeneousDim e)) (i : Fin 2) :
    (pinnedTensorToGraphTensor heterogeneousDim A).component (0, 0)
        (fun e => forwardSquareVirtualConfigEquiv heterogeneousDim η e.val) i =
      A (0, 0) i (fun e => η e.val) :=
  pinnedTensorToGraphTensor_component heterogeneousDim A η (0, 0) i

example (A : (v : Vertex 2) → Pinned.LocalTensor 2 heterogeneousDim v) :
    WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor heterogeneousDim A)) =
      Pinned.contractPEPS heterogeneousDim A :=
  stateVector_pinnedTensorToGraphTensor heterogeneousDim A

example {q : ℕ} (P : Vector.Tensor q 0) : P.maxBondDim = 0 := by
  simp [Vector.Tensor.maxBondDim]

example {q : ℕ} (P : Vector.Tensor q 1) : P.maxBondDim = 0 := by
  let : IsEmpty (ForwardEdge 1) := ⟨fun e => by
    have h := e.property
    simp [ForwardAdjacent, Fin.fin_one_eq_zero] at h⟩
  simp [Vector.Tensor.maxBondDim]

example {q : ℕ} (P : Vector.Tensor q 1) (Ω : Pinned.State 1 q) (ε : ℝ) :
    Vector.PhaseErrorAtMost (WithLp.toLp 2 (stateCoeff (vectorTensorToGraphTensor P))) Ω ε ↔
      Vector.PhaseErrorAtMost P.contract Ω ε :=
  phaseErrorAtMost_vectorTensorToGraphTensor P Ω ε

example {L : ℕ} : Pinned.boundaryCard (∅ : Finset (Vertex L)) = 0 := by
  simp [Pinned.boundaryCard]

example {L : ℕ} : Pinned.boundaryCard (Finset.univ : Finset (Vertex L)) = 0 := by
  simp [Pinned.boundaryCard]

example {L q : ℕ} (P : Vector.Tensor q L) (R : Finset (Vertex L)) :
    regionReducedDensity (vectorTensorToGraphTensor P) R = Pinned.reducedDensity P.contract R :=
  regionReducedDensity_vectorTensorToGraphTensor P R

example (P : Vector.Tensor 3 2) :
    (vectorTensorToGraphTensor P : Tensor (squareLatticeGraph 2 2) 3).bondDim
      (forwardSquareEdgeEquiv 2 rightEdge) = P.bondDim rightEdge := rfl

end SquareGridStateTransportTest
