/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridSource

/-!
# Exact conversion of open square-grid contractions

Original proofs comparing the two adapted source presentations with native graph
PEPS. Source: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
September 24 polynomial PEPS manuscript, introduction lines 20–34. Neither
injectivity nor uniform or positive dimensions are needed for the physical-first
conversion. The virtual-first adapter retains its source's positivity field.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.Approximation

variable {L q : ℕ}

/-- Forward right/up edges are exactly the lexicographically oriented native edges. -/
def forwardSquareEdgeEquiv (L : ℕ) : ForwardEdge L ≃ Edge (squareLatticeGraph L L) where
  toFun e := ⟨e.val, by
    constructor
    · change toLex e.val.1 < toLex e.val.2
      rw [Prod.Lex.toLex_lt_toLex]
      rcases e.property with ⟨hx, _⟩ | ⟨hx, hy⟩
      · left
        change e.val.1.1.val < e.val.2.1.val
        omega
      · right
        refine ⟨hx, ?_⟩
        change e.val.1.2.val < e.val.2.2.val
        omega
    · rcases e.property with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inl ⟨hy, Or.inl hx⟩
      · exact Or.inr ⟨hx, Or.inl hy⟩⟩
  invFun e := ⟨e.val, by
    rcases squareLatticeEdge_horizontal_or_vertical e with h | h
    · obtain ⟨hy, hx⟩ := horizontalSquareLatticeEdge_coords e h
      exact Or.inl ⟨hx, hy⟩
    · exact Or.inr (verticalSquareLatticeEdge_coords e h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The edge conversion preserves the ordered endpoints, not only their unordered set. -/
@[simp] theorem forwardSquareEdgeEquiv_val (e : ForwardEdge L) :
    (forwardSquareEdgeEquiv L e).val = e.val := rfl

/-- The inverse conversion also preserves endpoints. -/
@[simp] theorem forwardSquareEdgeEquiv_symm_val (e : Edge (squareLatticeGraph L L)) :
    ((forwardSquareEdgeEquiv L).symm e).val = e.val := rfl

/-- Incidence conversion for the virtual-first source presentation. -/
def forwardSquareIncidentEquiv (v : Vertex L) :
    Vector.IncidentEdge L v ≃ IncidentEdge (squareLatticeGraph L L) v where
  toFun e := ⟨forwardSquareEdgeEquiv L e.val, e.property⟩
  invFun e := ⟨(forwardSquareEdgeEquiv L).symm e.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Incidence conversion for the physical-first presentation, reversing equality proofs. -/
def pinnedSquareIncidentEquiv (v : Vertex L) :
    Pinned.IncidentEdge v ≃ IncidentEdge (squareLatticeGraph L L) v where
  toFun e := ⟨forwardSquareEdgeEquiv L e.val,
    e.property.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  invFun e := ⟨(forwardSquareEdgeEquiv L).symm e.val,
    e.property.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Forgetting incidence commutes with the global edge conversion. -/
@[simp] theorem forwardSquareIncidentEquiv_val (v : Vertex L)
    (e : Vector.IncidentEdge L v) :
    (forwardSquareIncidentEquiv v e).val = forwardSquareEdgeEquiv L e.val := rfl

/-- The physical-first incidence conversion has the same underlying edge map. -/
@[simp] theorem pinnedSquareIncidentEquiv_val (v : Vertex L) (e : Pinned.IncidentEdge v) :
    (pinnedSquareIncidentEquiv v e).val = forwardSquareEdgeEquiv L e.val := rfl

/-- Exact edge-dependent dimensions pulled back through the inverse edge equivalence. -/
def graphBondDim (D : ForwardEdge L → ℕ) : Edge (squareLatticeGraph L L) → ℕ :=
  fun e => D ((forwardSquareEdgeEquiv L).symm e)

/-- Every edge keeps its dimension, including zero-dimensional bonds. -/
@[simp] theorem graphBondDim_forward (D : ForwardEdge L → ℕ) (e : ForwardEdge L) :
    graphBondDim D (forwardSquareEdgeEquiv L e) = D e := rfl

/-- Bijection of dependent global assignments; there is no padding. -/
def forwardSquareVirtualConfigEquiv (D : ForwardEdge L → ℕ) :
    ((e : ForwardEdge L) → Fin (D e)) ≃
      ((e : Edge (squareLatticeGraph L L)) → Fin (graphBondDim D e)) where
  toFun a e := a ((forwardSquareEdgeEquiv L).symm e)
  invFun a e := a (forwardSquareEdgeEquiv L e)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting a transported global assignment agrees with incidence transport. -/
@[simp] theorem forwardSquareVirtualConfigEquiv_incident (D : ForwardEdge L → ℕ)
    (a : (e : ForwardEdge L) → Fin (D e)) (v : Vertex L)
    (e : Vector.IncidentEdge L v) :
    forwardSquareVirtualConfigEquiv D a (forwardSquareIncidentEquiv v e).val =
      a e.val := rfl

/-- The physical-first version of the same restriction identity. -/
@[simp] theorem forwardSquareVirtualConfigEquiv_pinnedIncident (D : ForwardEdge L → ℕ)
    (a : (e : ForwardEdge L) → Fin (D e)) (v : Vertex L)
    (e : Pinned.IncidentEdge v) :
    forwardSquareVirtualConfigEquiv D a (pinnedSquareIncidentEquiv v e).val =
      a e.val := rfl

/-- Convert arbitrary physical-first tensors into native virtual-first components. -/
def pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) : Tensor (squareLatticeGraph L L) q where
  bondDim := graphBondDim D
  component v a p := A v p (fun e => a (pinnedSquareIncidentEquiv v e))

/-- Convert the virtual-first source structure, preserving its local tensor coefficients. -/
def vectorTensorToGraphTensor (P : Vector.Tensor q L) : Tensor (squareLatticeGraph L L) q where
  bondDim := graphBondDim P.bondDim
  component v a p := P.tensor v (fun e => a (forwardSquareIncidentEquiv v e)) p

/-- Pointwise physical-first component identity for every global assignment. -/
theorem pinnedTensorToGraphTensor_component (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v)
    (a : (e : ForwardEdge L) → Fin (D e)) (v : Vertex L) (p : Fin q) :
    (pinnedTensorToGraphTensor D A).component v
      (fun e => forwardSquareVirtualConfigEquiv D a e.val) p =
      A v p (fun e => a e.val) := rfl

/-- Pointwise virtual-first component identity for every global assignment. -/
theorem vectorTensorToGraphTensor_component (P : Vector.Tensor q L)
    (a : (e : ForwardEdge L) → Fin (P.bondDim e)) (v : Vertex L) (p : Fin q) :
    (vectorTensorToGraphTensor P).component v
      (fun e => forwardSquareVirtualConfigEquiv P.bondDim a e.val) p =
      P.tensor v (fun e => a e.val) p := rfl

/-- Exact coefficient equality for arbitrary physical-first tensors, without a scalar factor. -/
theorem stateCoeff_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) (x : Vertex L → Fin q) :
    stateCoeff (pinnedTensorToGraphTensor D A) x = Pinned.contractPEPS D A x := by
  classical
  unfold stateCoeff Pinned.contractPEPS
  exact (Fintype.sum_equiv (forwardSquareVirtualConfigEquiv D) _ _ (fun _ => rfl)).symm

/-- Exact coefficient equality for the separate virtual-first presentation. -/
theorem stateCoeff_vectorTensorToGraphTensor (P : Vector.Tensor q L) (x : Vertex L → Fin q) :
    stateCoeff (vectorTensorToGraphTensor P) x = P.contract x := by
  classical
  unfold stateCoeff Vector.Tensor.contract
  exact (Fintype.sum_equiv (forwardSquareVirtualConfigEquiv P.bondDim) _ _
    (fun _ => rfl)).symm

end TNLean.PEPS.Approximation
