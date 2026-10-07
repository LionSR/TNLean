import TNLean.PEPS.Approximation.SourceApproximation

/-! Regression cases and guarded kernel dependencies for regional square-grid transport. -/

-- Kernel dependency reports are intentional in this regression module.
set_option linter.hashCommand false

open TNLean.PEPS TNLean.PEPS.Approximation

-- Both source conventions have the same exact physical vector and regional density.
example {L q : ℕ} (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    pepsVector (pinnedTensorToGraphTensor D A) = Pinned.contractPEPS D A :=
  vector_pinnedTensorToGraphTensor D A

example {L q : ℕ} (P : Vector.Tensor q L) :
    pepsVector (vectorTensorToGraphTensor P) = P.contract :=
  vector_vectorTensorToGraphTensor P

-- Empty and full cuts are included in the universal boundary theorem.
example {L : ℕ} :
    Fintype.card {e : ForwardEdge L //
      (e.val.1 ∈ (∅ : Finset (Vertex L)) ∧ e.val.2 ∉ (∅ : Finset (Vertex L))) ∨
      (e.val.1 ∉ (∅ : Finset (Vertex L)) ∧ e.val.2 ∈ (∅ : Finset (Vertex L)))} =
      Fintype.card {e : Edge (squareLatticeGraph L L) // IsRegionBoundaryEdge ∅ e} :=
  forwardSquareBoundary_card ∅

-- Maximum bonds use zero on an empty edge set.
example {q : ℕ} (P : Vector.Tensor q 0) : P.maxBondDim = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [maxBondDim_le_iff]
  intro e
  exact Fin.elim0 e.val.1.1

-- The actual owner-defined native approximation proposition is the target.
example {L q : ℕ} {Ω : Pinned.State L q} {C c : ℝ}
    (h : Pinned.HasPEPSApproximation Ω C c) : HasPEPSApproximation C c L q Ω :=
  hasPEPSApproximation_of_pinned h

/-- info: 'TNLean.PEPS.Approximation.vector_pinnedTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vector_pinnedTensorToGraphTensor
/-- info: 'TNLean.PEPS.Approximation.vector_vectorTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vector_vectorTensorToGraphTensor
/-- info: 'TNLean.PEPS.Approximation.regionReducedDensity_eq_piSubtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionReducedDensity_eq_piSubtype
/-- info: 'TNLean.PEPS.Approximation.entropy_pinnedTensorToGraphTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_pinnedTensorToGraphTensor
/-- info: 'TNLean.PEPS.Approximation.hasPEPSApproximation_of_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasPEPSApproximation_of_pinned
/-- info: 'TNLean.PEPS.Approximation.hasPEPSApproximation_of_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasPEPSApproximation_of_vector

/-- info: 'TNLean.PEPS.Approximation.regionReducedDensity_eq_pinnedReducedDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionReducedDensity_eq_pinnedReducedDensity

-- A zero bond on a nonempty square forces zero contraction at every physical configuration.
example (A : (v : Vertex 2) → Pinned.LocalTensor 2 (fun _ => 0) v)
    (x : Vertex 2 → Fin 2) : Pinned.contractPEPS (fun _ => 0) A x = 0 := by
  classical
  let : IsEmpty ((e : ForwardEdge 2) → Fin 0) :=
    ⟨fun a => Fin.elim0 (a ⟨((0, 0), (1, 0)), Or.inl ⟨rfl, rfl⟩⟩)⟩
  simp [Pinned.contractPEPS]

/-- info: 'TNLean.PEPS.Approximation.hasPEPSApproximation_of_vector_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasPEPSApproximation_of_vector_max

-- On a nonempty grid with zero physical dimension, the entire vector is zero.
example (D : ForwardEdge 1 → ℕ)
    (A : (v : Vertex 1) → Pinned.LocalTensor 0 D v) :
    pepsVector (pinnedTensorToGraphTensor D A) = 0 := by
  ext x
  exact Fin.elim0 (x (0, 0))

-- One zero bond suffices, even when all other edge dimensions are independent.
example {L q : ℕ} (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v)
    (e : ForwardEdge L) (he : D e = 0) :
    pepsVector (pinnedTensorToGraphTensor D A) = 0 := by
  let : IsEmpty ((f : ForwardEdge L) → Fin (D f)) := ⟨fun a => by
    have h := (a e).isLt
    omega⟩
  rw [vector_pinnedTensorToGraphTensor]
  ext x
  simp [Pinned.contractPEPS]

-- A full region has zero crossing bonds.
example {L : ℕ} :
    Fintype.card {e : Edge (squareLatticeGraph L L) //
      IsRegionBoundaryEdge Finset.univ e} = 0 := by
  simp [IsRegionBoundaryEdge]
