/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NormalBondDimension

/-!
# The PEPS bond-dimension comparisons are false without positive bond dimensions

This file gives a counterexample. Without positive virtual bond dimensions,
vertex-injectivity and equality of all PEPS state coefficients do not imply
gauge equivalence. A zero-dimensional edge gives an empty global
virtual-configuration space, so every state coefficient is zero and the
same-state condition holds vacuously; the same zero-dimensional edge incident to
a vertex gives an empty local configuration space, so vertex-injectivity
holds vacuously at every vertex. Yet gauge equivalence carries the genuine
constraint that the two tensors have the same virtual bond dimensions, which
fails the moment the two tensors disagree on the bond dimension of any edge.

The witness is the triangle on three vertices, with two of its three edges of bond
dimension zero, and the remaining edge of dimension one for the first tensor and
dimension two for the second. All vertex configuration spaces and both global
virtual-configuration spaces are empty, so both PEPS are vacuously
vertex-injective and both have the zero state; but the bond dimensions disagree,
so no gauge equivalence exists.

The same witness meets every hypothesis of the one-edge step
`bondDim_apply_eq_of_blockingData` except positivity. Around the edge `f3`, where
the bond dimensions differ, the three blocks are the singletons `{0}`, `{2}` and
`{1}`. Each singleton has a zero-dimensional boundary edge, so it has no boundary
configurations and its blocked tensor is vacuously injective.
`bondDimOfBlockingDataStatement_false` refutes that step without positivity.

Source: arXiv:1804.04964, Theorem 2, local source `paper_normal.tex`, line
1209. The source treats PEPS as having nonzero-dimensional virtual bond spaces.
The same missing positivity condition was identified for
`edgeBlockedThreeSiteInjective` and `physical_to_virtual_insertion`
(`docs/paper-gaps/peps_injective_ft_section3_route.tex`). The source-facing
theorems carry the convention in their tensor hypotheses: `fundamentalTheorem_PEPS`
takes `Tensor.IsInjective`, and the general normal theorem
`fundamentalTheorem_normalPEPS` takes `NormalPEPSPairHypotheses`. The one-edge
and coherent-frame steps `bondDim_apply_eq_of_blockingData` and
`bondDim_apply_eq_of_coherentFrames` constrain their tensors only through
blocking data, and keep explicit positivity; the second refutation below shows
that this positivity is needed.
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
  symm := ⟨by
    intro a b h
    unfold adj3 at *
    fin_cases a <;> fin_cases b <;> simp_all⟩
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

/-- `A` (`d = 2`): all local configuration spaces are empty, so the components are
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

/-! ### Every vertex configuration space is empty (each vertex meets a zero edge). -/

/-- `e3` is incident to vertex `0`. -/
def e3_at0 : IncidentEdge G3 (0 : V3) := ⟨e3, Or.inl rfl⟩
/-- `e3` is incident to vertex `1`. -/
def e3_at1 : IncidentEdge G3 (1 : V3) := ⟨e3, Or.inr rfl⟩
/-- `g3` is incident to vertex `2`. -/
def g3_at2 : IncidentEdge G3 (2 : V3) := ⟨g3, Or.inr rfl⟩

/-- The local configuration space of `A` at every vertex is empty. -/
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

/-- The local configuration space of `B` at every vertex is empty. -/
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

/-- `A`'s global virtual-configuration space is empty (edge `e3` has bond `0`). -/
instance : IsEmpty (VirtualConfig A3) := by
  refine ⟨fun η => ?_⟩
  have h := η e3
  rw [show A3.bondDim e3 = 0 from bdA_e3] at h
  exact h.elim0

/-- `B`'s global virtual-configuration space is empty (edge `e3` has bond `0`). -/
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

/-! ### Refutation of the hypothesis-free statement. -/

/-- The hypothesis-free version of the PEPS Fundamental Theorem statement,
generic over the vertex set, graph, and physical dimension. -/
def FundamentalTheoremPEPSStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A B : Tensor G d)
    (_ : IsVertexInjective A) (_ : IsVertexInjective B)
    (_ : SameState A B),
    GaugeEquiv A B

/-- `fundamentalTheorem_PEPS` does not hold without a positive-bond hypothesis:
the witness `(G3, A3, B3)` satisfies all three hypotheses
(`IsVertexInjective A3`, `IsVertexInjective B3`, `SameState A3 B3`) yet
`GaugeEquiv A3 B3` is false. -/
theorem fundamentalTheoremPEPSStatement_false :
    ¬ FundamentalTheoremPEPSStatement := by
  intro hThm
  exact not_gaugeEquiv
    (hThm A3 B3 A3_vertexInjective B3_vertexInjective A3_B3_sameState)

/-! ### Refutation of the one-edge blocking-data step without positivity -/

/-- A region with a zero-dimensional boundary edge is vacuously injective: it has no
boundary configurations. -/
theorem regionBlockedTensorInjective_of_bondDim_eq_zero {V : Type*} [Fintype V]
    [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (A : Tensor G d)
    (R : Finset V) (f : Edge G) (hf : IsRegionBoundaryEdge (G := G) R f)
    (h0 : A.bondDim f = 0) : RegionBlockedTensorInjective (G := G) A R := by
  have : IsEmpty (RegionBoundaryConfig (G := G) A R) := ⟨fun c => by
    have h := c ⟨f, hf⟩
    rw [h0] at h
    exact h.elim0⟩
  exact linearIndependent_empty_type

/-- The blocking around `f3` into the singletons `{0}`, `{2}` and `{1}`, for a tensor whose
only nonzero bond is `f3`. -/
def blockingAtF3 (T : Tensor G3 2) (hT : ∀ h : Edge G3, h ≠ f3 → T.bondDim h = 0) :
    NormalEdgeBlockingData (regionInjectivityDataOf (G := G3) T) G3 f3 where
  red := {0}
  blue := {2}
  complement := {1}
  left_mem_red := by decide
  right_mem_blue := by decide
  red_injective :=
    regionBlockedTensorInjective_of_bondDim_eq_zero T {0} e3 (by decide) (hT e3 f3_ne_e3.symm)
  blue_injective :=
    regionBlockedTensorInjective_of_bondDim_eq_zero T {2} g3 (by decide) (hT g3 f3_ne_g3.symm)
  complement_injective :=
    regionBlockedTensorInjective_of_bondDim_eq_zero T {1} e3 (by decide) (hT e3 f3_ne_e3.symm)
  red_disjoint_blue := by decide
  red_disjoint_complement := by decide
  blue_disjoint_complement := by decide
  cover_univ := by decide

theorem A3_bondDim_of_ne {h : Edge G3} (hh : h ≠ f3) : A3.bondDim h = 0 := by
  simp [A3, bdA, hh]

theorem B3_bondDim_of_ne {h : Edge G3} (hh : h ≠ f3) : B3.bondDim h = 0 := by
  simp [B3, bdB, hh]

/-- The edge `f3` is the only edge joining the blocks `{0}` and `{2}`. -/
theorem isCrossingEdge_blockingAtF3 (g : Edge G3) :
    IsCrossingEdge (G := G3) A3 {0} {2} g ↔ g = f3 := by
  revert g
  decide

/-- The one-edge bond-dimension step of the general normal theorem, with the positivity
hypotheses removed: shared red and blue blocks, the same state, positive physical dimension
and a single crossing edge. -/
def BondDimOfBlockingDataStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A B : Tensor G d) (e : Edge G)
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e),
    DA.red = DB.red → DA.blue = DB.blue → SameState A B → 0 < d →
    (∀ g : Edge G, IsCrossingEdge (G := G) A DA.red DA.blue g ↔ g = e) →
    A.bondDim e = B.bondDim e

/-- `bondDim_apply_eq_of_blockingData` does not hold without its positivity hypotheses: the
witness `(G3, A3, B3)` with the singleton blocking around `f3` satisfies all the remaining
hypotheses, yet the bond dimensions on `f3` are `1` and `2`. -/
theorem bondDimOfBlockingDataStatement_false : ¬ BondDimOfBlockingDataStatement := by
  intro hThm
  have h := hThm A3 B3 f3 (blockingAtF3 A3 fun _ => A3_bondDim_of_ne)
    (blockingAtF3 B3 fun _ => B3_bondDim_of_ne) rfl rfl A3_B3_sameState (by norm_num)
    isCrossingEdge_blockingAtF3
  rw [A3_bondDim, B3_bondDim, bdA_f3, bdB_f3] at h
  exact absurd h (by decide)

end FundamentalTheoremCounterexample
end PEPS
end TNLean
