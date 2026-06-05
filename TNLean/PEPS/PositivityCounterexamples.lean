import TNLean.PEPS.FundamentalTheorem

/-!
# `fundamentalTheorem_PEPS` is false without positive bond dimensions

This file is a checked counterexample. The headline PEPS Fundamental Theorem

  `IsVertexInjective A → IsVertexInjective B → SameState A B → GaugeEquiv A B`

is FALSE once the standing positive-bond assumption is dropped. A zero-dimensional
edge empties the global virtual-configuration type, so `stateCoeff` is identically
zero and `SameState` holds vacuously; the same zero-dimensional edge incident to a
vertex empties that vertex's local configuration type, so `IsVertexInjective` holds
vacuously at every vertex. Yet `GaugeEquiv` carries the genuine constraint
`A.bondDim = B.bondDim`, which fails the moment the two tensors disagree on the
bond dimension of any edge.

The witness is the triangle on three vertices, with two of its three edges of bond
dimension zero, and the remaining edge of bond dimension `1` in `A` and `2` in `B`.
All vertex configuration types and both global virtual-configuration types are
empty, so both PEPS are vacuously vertex-injective and both have the zero state;
but the bond dimensions disagree, so no gauge equivalence exists.

Source: the positive-bond assumption is the standing assumption of arXiv:1804.04964
that injective PEPS have nonzero-dimensional virtual bond spaces. The same defect
was found and corrected for `edgeBlockedThreeSiteInjective` (#1366) and
`physical_to_virtual_insertion` (#1370).
-/

namespace TNLean
namespace PEPS
namespace FundamentalTheoremCounterexample

open scoped BigOperators

abbrev V3 := Fin 3

/-- Triangle adjacency on three vertices. -/
def adj3 (a b : V3) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

instance : DecidableRel adj3 := by unfold adj3; infer_instance

def G3 : SimpleGraph V3 where
  Adj := adj3
  symm := by
    intro a b h
    unfold adj3 at *
    fin_cases a <;> fin_cases b <;> simp_all
  loopless := ⟨by intro a; unfold adj3; fin_cases a <;> simp⟩

instance : DecidableRel G3.Adj := by
  change DecidableRel adj3
  infer_instance

/-- Edge `(0,1)`: zero bond dimension. -/
def e3 : Edge G3 := ⟨(0, 1), by constructor <;> decide⟩
/-- Edge `(0,2)`: the only positive edge; dimension differs between `A` and `B`. -/
def f3 : Edge G3 := ⟨(0, 2), by constructor <;> decide⟩
/-- Edge `(1,2)`: zero bond dimension. -/
def g3 : Edge G3 := ⟨(1, 2), by constructor <;> decide⟩

theorem f3_ne_e3 : f3 ≠ e3 := by decide
theorem f3_ne_g3 : f3 ≠ g3 := by decide

/-- Bond dimension for `A`: `1` on the positive edge `f`, `0` elsewhere. -/
def bdA : Edge G3 → ℕ := fun h => if h = f3 then 1 else 0
/-- Bond dimension for `B`: `2` on the positive edge `f`, `0` elsewhere. -/
def bdB : Edge G3 → ℕ := fun h => if h = f3 then 2 else 0

theorem bdA_e3 : bdA e3 = 0 := by simp [bdA, (f3_ne_e3).symm]
theorem bdA_g3 : bdA g3 = 0 := by simp [bdA, (f3_ne_g3).symm]
theorem bdB_e3 : bdB e3 = 0 := by simp [bdB, (f3_ne_e3).symm]
theorem bdB_g3 : bdB g3 = 0 := by simp [bdB, (f3_ne_g3).symm]
theorem bdA_f3 : bdA f3 = 1 := by simp [bdA]
theorem bdB_f3 : bdB f3 = 2 := by simp [bdB]

/-- `A` (`d = 2`): all local configuration types are empty, so the components are
arbitrary (here constantly zero). -/
def A3 : Tensor G3 2 where
  bondDim := bdA
  component := fun _ _ _ => 0

/-- `B` (`d = 2`): identical shape, with the positive edge of dimension `2`. -/
def B3 : Tensor G3 2 where
  bondDim := bdB
  component := fun _ _ _ => 0

theorem A3_bondDim : A3.bondDim = bdA := rfl
theorem B3_bondDim : B3.bondDim = bdB := rfl

/-! ### Every vertex configuration type is empty (each vertex meets a zero edge). -/

/-- `e3` is incident to vertex `0`. -/
def e3_at0 : IncidentEdge G3 (0 : V3) := ⟨e3, Or.inl rfl⟩
/-- `e3` is incident to vertex `1`. -/
def e3_at1 : IncidentEdge G3 (1 : V3) := ⟨e3, Or.inr rfl⟩
/-- `g3` is incident to vertex `2`. -/
def g3_at2 : IncidentEdge G3 (2 : V3) := ⟨g3, Or.inr rfl⟩

/-- The local configuration type of `A` at every vertex is empty. -/
instance : ∀ v : V3, IsEmpty ((ie : IncidentEdge G3 v) → Fin (A3.bondDim ie.1)) := by
  intro v
  refine ⟨fun c => ?_⟩
  fin_cases v
  · have h := c e3_at0
    rw [show A3.bondDim e3_at0.1 = 0 from bdA_e3] at h
    exact h.elim0
  · have h := c e3_at1
    rw [show A3.bondDim e3_at1.1 = 0 from bdA_e3] at h
    exact h.elim0
  · have h := c g3_at2
    rw [show A3.bondDim g3_at2.1 = 0 from bdA_g3] at h
    exact h.elim0

/-- The local configuration type of `B` at every vertex is empty. -/
instance : ∀ v : V3, IsEmpty ((ie : IncidentEdge G3 v) → Fin (B3.bondDim ie.1)) := by
  intro v
  refine ⟨fun c => ?_⟩
  fin_cases v
  · have h := c e3_at0
    rw [show B3.bondDim e3_at0.1 = 0 from bdB_e3] at h
    exact h.elim0
  · have h := c e3_at1
    rw [show B3.bondDim e3_at1.1 = 0 from bdB_e3] at h
    exact h.elim0
  · have h := c g3_at2
    rw [show B3.bondDim g3_at2.1 = 0 from bdB_g3] at h
    exact h.elim0

/-! ### The two PEPS states are both identically zero. -/

/-- `A`'s global virtual-configuration type is empty (edge `e3` has bond `0`). -/
instance : IsEmpty (VirtualConfig A3) := by
  refine ⟨fun η => ?_⟩
  have h := η e3
  rw [show A3.bondDim e3 = 0 from bdA_e3] at h
  exact h.elim0

/-- `B`'s global virtual-configuration type is empty (edge `e3` has bond `0`). -/
instance : IsEmpty (VirtualConfig B3) := by
  refine ⟨fun η => ?_⟩
  have h := η e3
  rw [show B3.bondDim e3 = 0 from bdB_e3] at h
  exact h.elim0

theorem stateCoeff_A3 (σ : V3 → Fin 2) : stateCoeff A3 σ = 0 := by
  simp only [stateCoeff]
  rw [Finset.univ_eq_empty, Finset.sum_empty]

theorem stateCoeff_B3 (σ : V3 → Fin 2) : stateCoeff B3 σ = 0 := by
  simp only [stateCoeff]
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-! ### The three source hypotheses hold; the conclusion fails. -/

/-- `A` is vacuously vertex-injective: every local family is indexed by an empty type. -/
theorem A3_vertexInjective : IsVertexInjective A3 := by
  intro v
  exact linearIndependent_empty_type

/-- `B` is vacuously vertex-injective: every local family is indexed by an empty type. -/
theorem B3_vertexInjective : IsVertexInjective B3 := by
  intro v
  exact linearIndependent_empty_type

/-- The two PEPS represent the same (zero) state. -/
theorem A3_B3_sameState : SameState A3 B3 := by
  intro σ
  rw [stateCoeff_A3, stateCoeff_B3]

/-- The bond dimensions disagree on the positive edge `f3`, so there is no
bond-dimension identification and hence no gauge equivalence. -/
theorem not_gaugeEquiv : ¬ GaugeEquiv A3 B3 := by
  rintro ⟨hDim, -, -⟩
  have h := congr_fun hDim f3
  rw [A3_bondDim, B3_bondDim, bdA_f3, bdB_f3] at h
  exact absurd h (by decide)

/-! ### Refutation of a verbatim copy of the statement. -/

/-- A verbatim copy of the type of `TNLean.PEPS.fundamentalTheorem_PEPS`, generic
over the vertex set, graph, and physical dimension. -/
def FundamentalTheoremPEPSStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A B : Tensor G d)
    (_ : IsVertexInjective A) (_ : IsVertexInjective B)
    (_ : SameState A B),
    GaugeEquiv A B

/-- `fundamentalTheorem_PEPS` is FALSE as written, i.e. without a positive-bond
hypothesis: the witness `(G3, A3, B3)` satisfies all three hypotheses
(`IsVertexInjective A3`, `IsVertexInjective B3`, `SameState A3 B3`) yet
`GaugeEquiv A3 B3` is false. -/
theorem fundamentalTheoremPEPSStatement_false :
    ¬ FundamentalTheoremPEPSStatement := by
  intro hThm
  exact not_gaugeEquiv
    (hThm A3 B3 A3_vertexInjective B3_vertexInjective A3_B3_sameState)

end FundamentalTheoremCounterexample
end PEPS
end TNLean
