import TNLean.PEPS.FundamentalTheorem.GaugeAction

/-!
# `gaugeConsistency` and `fundamentalTheorem_PEPS` are false without connectivity

This file gives a counterexample. On a disconnected graph, vertex injectivity,
equality of all PEPS state coefficients, and positive bond dimensions do not
imply that the two tensors are related by one global edge-gauge family. The
reduction to per-vertex scalars from the source proof is correct, but absorbing
those scalars into edge gauges requires their reciprocal product to be `1` on
each connected component, which the state equality forces only when the graph
has a single component.

The witness is the empty graph on two vertices, with physical dimension `1` and
single-scalar tensors. Both vertex tensors are nonzero scalars, so both PEPS are
vertex injective; the two states agree because the products of the scalars
agree. There are no edges, so positivity holds vacuously and the only edge-gauge
family is the empty one. The empty gauge leaves every vertex tensor unchanged,
so the gauge-consistency conclusion forces the two tensors to be equal, which
they are not.

Concretely, take `G = (Bool, ∅)`, physical dimension `1`, and
\[
  A_0 = 2,\quad A_1 = 3,\qquad B_0 = 6,\quad B_1 = 1 .
\]
The states agree, `A_0 A_1 = 6 = B_0 B_1`, but `A_0 = 2 ≠ 6 = B_0`, so no empty
gauge can relate them.

Source: arXiv:1804.04964, Theorem 2, local source `paper_normal.tex`, line
1207 ("the constants $\lambda_v$ can be incorporated into the gauge
transformations"). The source's injective PEPS are implicitly connected; the
absorption step is invalid on a disconnected graph. Documented in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`.
-/

namespace TNLean
namespace PEPS
namespace GaugeConsistencyConnectivityCounterexample

open scoped BigOperators

/-- The two isolated vertices. -/
abbrev V2 := Bool

/-- The empty graph on two vertices: no edges, two isolated components. -/
abbrev G2 : SimpleGraph V2 := ⊥

instance : DecidableRel G2.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph V2).Adj)

/-- The empty graph has no edges. -/
instance instIsEmptyEdge : IsEmpty (Edge G2) := ⟨fun e => e.2.2⟩

/-- The empty graph has no incident edges at any vertex. -/
instance instIsEmptyIncident (v : V2) : IsEmpty (IncidentEdge G2 v) :=
  ⟨fun ie => instIsEmptyEdge.false ie.1⟩

/-- Bond dimension: trivial, there are no edges. -/
def bd : Edge G2 → ℕ := fun _ => 0

/-- `A` (physical dimension `1`): scalar values `A_0 = 2`, `A_1 = 3`. -/
noncomputable def A2 : Tensor G2 1 where
  bondDim := bd
  component := fun v _ _ => if v = false then 2 else 3

/-- `B` (physical dimension `1`): scalar values `B_0 = 6`, `B_1 = 1`. -/
noncomputable def B2 : Tensor G2 1 where
  bondDim := bd
  component := fun v _ _ => if v = false then 6 else 1

/-- The bond dimensions agree (both vacuous). -/
theorem bondDim_eq : A2.bondDim = B2.bondDim := rfl

/-- Positivity is vacuous for `A`: there are no edges. -/
theorem hpos_A : ∀ e : Edge G2, 0 < A2.bondDim e := fun e => (instIsEmptyEdge.false e).elim

/-- Positivity is vacuous for `B`: there are no edges. -/
theorem hpos_B : ∀ e : Edge G2, 0 < B2.bondDim e := fun e => (instIsEmptyEdge.false e).elim

/-! ### The two source hypotheses hold. -/

/-- `A` is vertex injective: at each vertex the unique local configuration gives a
nonzero physical vector. -/
theorem isVertexInjective_A2 : IsVertexInjective A2 := by
  intro v
  rw [linearIndependent_unique_iff]
  intro hzero
  have h0 := congr_fun hzero 0
  simp only [A2, Pi.zero_apply] at h0
  fin_cases v <;> simp_all

/-- `B` is vertex injective: at each vertex the unique local configuration gives a
nonzero physical vector. -/
theorem isVertexInjective_B2 : IsVertexInjective B2 := by
  intro v
  rw [linearIndependent_unique_iff]
  intro hzero
  have h0 := congr_fun hzero 0
  simp only [B2, Pi.zero_apply] at h0
  fin_cases v <;> simp_all

/-- The two PEPS represent the same state: each coefficient is the product of the
vertex scalars, and `2 * 3 = 6 = 6 * 1`. -/
theorem sameState_A2_B2 : SameState A2 B2 := by
  intro σ
  simp only [stateCoeff, Fintype.sum_unique]
  rw [Fintype.prod_bool, Fintype.prod_bool]
  simp only [A2, B2]
  norm_num

/-! ### With no edges, the gauge action is trivial. -/

/-- On the empty graph the only edge-gauge family is the empty one, and the
gauged vertex tensor equals the original vertex tensor. -/
theorem gaugeVertex_A2_eq (X : (e : Edge G2) → GL (Fin (A2.bondDim e)) ℂ) (v : V2)
    (η : (ie : IncidentEdge G2 v) → Fin (A2.bondDim ie.1)) (σ : Fin 1) :
    gaugeVertex A2 X v η σ = A2.component v η σ := by
  rw [gaugeVertex, Fintype.sum_unique, Finset.prod_of_isEmpty, one_mul]
  congr 1
  exact Subsingleton.elim _ _

/-! ### The gauge-consistency and gauge-equivalence conclusions both fail. -/

/-- The conclusion of `gaugeConsistency` for this input, as a standalone
proposition. -/
def GaugeConsistencyConclusion : Prop :=
  ∃ (X : (e : Edge G2) → GL (Fin (A2.bondDim e)) ℂ),
    ∀ (v : V2) (η : (ie : IncidentEdge G2 v) → Fin (A2.bondDim ie.1)) (σ : Fin 1),
      B2.component v (fun ie => Fin.cast (congr_fun bondDim_eq ie.1) (η ie)) σ =
        gaugeVertex A2 X v η σ

/-- The conclusion of `gaugeConsistency` fails for `(G2, A2, B2)`: the empty
gauge would force `B_0 = A_0`, that is `6 = 2`. -/
theorem not_gaugeConsistencyConclusion : ¬ GaugeConsistencyConclusion := by
  rintro ⟨X, hX⟩
  have h := hX false (fun ie => ((instIsEmptyIncident false).false ie).elim) 0
  rw [gaugeVertex_A2_eq] at h
  simp only [A2, B2] at h
  norm_num at h

/-- There is no gauge equivalence between `A2` and `B2`: with no edges, gauge
equivalence forces the vertex tensors to be equal, and `B_0 = 6 ≠ 2 = A_0`. -/
theorem not_gaugeEquiv : ¬ GaugeEquiv A2 B2 := by
  rintro ⟨hDim, X, hX⟩
  have h := hX false (fun ie => ((instIsEmptyIncident false).false ie).elim) 0
  rw [gaugeVertex_A2_eq] at h
  simp only [A2, B2] at h
  norm_num at h

/-! ### Refutation of the connectivity-free statements. -/

/-- The connectivity-free gauge-consistency statement, generic over the vertex
set, graph, and physical dimension. It keeps the positivity hypothesis to show
that connectivity, not positivity, is the missing assumption. -/
def GaugeConsistencyStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A B : Tensor G d)
    (_ : IsVertexInjective A) (_ : IsVertexInjective B)
    (_ : SameState A B) (hDim : A.bondDim = B.bondDim)
    (_ : ∀ e : Edge G, 0 < A.bondDim e),
    ∃ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          gaugeVertex A X v η σ

/-- `gaugeConsistency` is false without a connectivity hypothesis: the witness
`(G2, A2, B2)` satisfies vertex injectivity for both tensors, equality of all
state coefficients, bond-dimension equality, and (vacuously) positivity of every
bond, yet the gauge-consistency conclusion fails. -/
theorem gaugeConsistencyStatement_false : ¬ GaugeConsistencyStatement := by
  intro hThm
  exact not_gaugeConsistencyConclusion
    (hThm A2 B2 isVertexInjective_A2 isVertexInjective_B2 sameState_A2_B2 bondDim_eq hpos_A)

/-- The connectivity-free PEPS Fundamental Theorem statement, generic over the
vertex set, graph, and physical dimension. It keeps the positivity hypotheses to
show that connectivity, not positivity, is the missing assumption. -/
def FundamentalTheoremPEPSStatement : Prop :=
  ∀ {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (A B : Tensor G d)
    (_ : IsVertexInjective A) (_ : IsVertexInjective B)
    (_ : SameState A B)
    (_ : ∀ e : Edge G, 0 < A.bondDim e)
    (_ : ∀ e : Edge G, 0 < B.bondDim e),
    GaugeEquiv A B

/-- `fundamentalTheorem_PEPS` is false without a connectivity hypothesis: the
witness `(G2, A2, B2)` satisfies vertex injectivity for both tensors, equality of
all state coefficients, and (vacuously) positivity of every bond, yet there is no
gauge equivalence. -/
theorem fundamentalTheoremPEPS_false_without_connectivity :
    ¬ FundamentalTheoremPEPSStatement := by
  intro hThm
  exact not_gaugeEquiv
    (hThm A2 B2 isVertexInjective_A2 isVertexInjective_B2 sameState_A2_B2 hpos_A hpos_B)

end GaugeConsistencyConnectivityCounterexample
end PEPS
end TNLean
