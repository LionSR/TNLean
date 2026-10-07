import TNLean.PEPS.Approximation.SquareGridContraction

open TNLean.PEPS TNLean.PEPS.Approximation

-- Empty and singleton squares have no virtual bonds.
example : IsEmpty (ForwardEdge 0) := ⟨fun e => Fin.elim0 e.val.1.1⟩

example : IsEmpty (ForwardEdge 1) := by
  constructor
  intro e
  rcases e.property with ⟨h, _⟩ | ⟨_, h⟩ <;>
    have h₁ := e.val.1.1.isLt <;> have h₂ := e.val.2.1.isLt <;>
    have h₃ := e.val.1.2.isLt <;> have h₄ := e.val.2.2.isLt <;> omega

-- Horizontal and vertical endpoints are preserved literally on the first nontrivial square.
example : (forwardSquareEdgeEquiv 2
    ⟨((0, 0), (1, 0)), Or.inl ⟨rfl, rfl⟩⟩).val = ((0, 0), (1, 0)) := rfl

example : (forwardSquareEdgeEquiv 2
    ⟨((0, 0), (0, 1)), Or.inr ⟨rfl, rfl⟩⟩).val = ((0, 0), (0, 1)) := rfl

-- The two incident legs at the corner may have different dimensions.
private def unequalBonds (e : ForwardEdge 2) : ℕ :=
  if e.val.1.1 = e.val.2.1 then 3 else 2

example : graphBondDim unequalBonds (forwardSquareEdgeEquiv 2
    ⟨((0, 0), (1, 0)), Or.inl ⟨rfl, rfl⟩⟩) = 2 := by decide

example : graphBondDim unequalBonds (forwardSquareEdgeEquiv 2
    ⟨((0, 0), (0, 1)), Or.inr ⟨rfl, rfl⟩⟩) = 3 := by decide

-- Arbitrary coefficients, not a special injective or product tensor.
example (A : (v : Vertex 2) → Pinned.LocalTensor 2 unequalBonds v)
    (x : Vertex 2 → Fin 2) :
    stateCoeff (pinnedTensorToGraphTensor unequalBonds A) x =
      Pinned.contractPEPS unequalBonds A x := stateCoeff_pinnedTensorToGraphTensor _ _ _

-- Zero dimensions and zero physical dimension are accepted by the first presentation.
example (A : (v : Vertex 2) → Pinned.LocalTensor 0 (fun _ => 0) v)
    (x : Vertex 2 → Fin 0) :
    stateCoeff (pinnedTensorToGraphTensor (fun _ => 0) A) x =
      Pinned.contractPEPS (fun _ => 0) A x := stateCoeff_pinnedTensorToGraphTensor _ _ _

-- The separate virtual-first adapter uses the source's positive-dimension structure.
example {q L : ℕ} (P : Vector.Tensor q L) (x : Vertex L → Fin q) :
    stateCoeff (vectorTensorToGraphTensor P) x = P.contract x :=
  stateCoeff_vectorTensorToGraphTensor P x

#print axioms stateCoeff_pinnedTensorToGraphTensor
#print axioms stateCoeff_vectorTensorToGraphTensor

-- Bond-one contraction is the product of the arbitrary local physical coefficients.
example {L q : ℕ} (A : (v : Vertex L) → Pinned.LocalTensor q (fun _ => 1) v)
    (x : Vertex L → Fin q) :
    Pinned.contractPEPS (fun _ => 1) A x = ∏ v, A v (x v) (fun _ => 0) := by
  classical
  simp [Pinned.contractPEPS]

-- The empty lattice contracts to the scalar one even with nominally zero dimensions.
example {q : ℕ} (A : (v : Vertex 0) → Pinned.LocalTensor q (fun _ => 0) v)
    (x : Vertex 0 → Fin q) : Pinned.contractPEPS (fun _ => 0) A x = 1 := by
  classical
  letI : IsEmpty (ForwardEdge 0) := ⟨fun e => Fin.elim0 e.val.1.1⟩
  simp [Pinned.contractPEPS]
