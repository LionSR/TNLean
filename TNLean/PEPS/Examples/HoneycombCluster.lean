/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import TNLean.PEPS.Examples.ClusterStabilizer

/-!
# The honeycomb cluster state as a PEPS

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Section IV,
`Papers/2011.12127/TN-Review-main.tex` line 1445:

> The canonical example for an injective PEPS with global symmetries is the cluster
> state on the honeycomb lattice, which is the unique ground state of the commuting
> parent Hamiltonian $\sum_{ijkl}X_iZ_jZ_kZ_l$ of qubits where $j,k,l$ are the nearest
> neigbours of site $i$. This state has a very simple PEPS representation: [figure]
> with [GHZ tensor] $= \ket{0000}+\ket{1111}$, [bond matrix]
> $= \frac{1}{\sqrt{2}}\left(\begin{smallmatrix} 1 & 1\\ 1 & -1\end{smallmatrix}\right)$.

**Formalized here.** For an arbitrary simple graph, the PEPS with the copy tensor
$\ket{0\ldots0}+\ket{1\ldots1}$ at each vertex and the Hadamard matrix on each bond has
coefficient $2^{-|E|/2}\prod_{\{u,v\}\in E}(-1)^{\sigma_u\sigma_v}$, a multiple of the
controlled-Z circuit state. The bond matrix is absorbed into the vertex tensor at the
smaller endpoint of each bond, which leaves the contracted network unchanged. The
stabilizers $X_i\prod_{j\sim i}Z_j$ commute, and the stabilizer Hamiltonian
$-\sum_i X_i\prod_{j\sim i}Z_j$ is bounded below by $-|V|$ and attains it exactly on the
line of the PEPS: the state is its unique ground state. These statements are then
specialized to a brick-wall honeycomb on the torus, where each vertex has the three
nearest neighbours of the source.

**Local fix (sign of the parent Hamiltonian):** the printed Hamiltonian
$+\sum X_iZ_jZ_kZ_l$ has as unique ground state the common $-1$ eigenvector of the
stabilizers, which is $\prod_i Z_i$ applied to the cluster state, not the cluster state.
The Hamiltonian here is $-\sum X_iZ_jZ_kZ_l$, the stabilizer convention under which the
source's claim holds. Documented in `docs/paper-gaps/rmp_honeycomb_cluster_peps.tex`.

**False source (injectivity):** the source calls the PEPS injective, and the review defines
injectivity tensor by tensor (line 1929). The vertex tensor, read as a map from its virtual
legs to the qubit, has rank two, so a vertex with at least two bonds is not injective
(`not_isVertexInjective_honeycombClusterPEPS`); the source's two-site blocking maps a space
of dimension sixteen to one of dimension four. Injectivity holds after blocking over
hexagonal plaquettes; this is not formalized, and no injectivity of the honeycomb PEPS is
asserted. Documented in `docs/paper-gaps/rmp_honeycomb_cluster_injectivity.tex`.

**Scope restriction (torus size):** the brick wall on a `width × height` torus is the
honeycomb when both sides are even; the three neighbours are distinct for even height and
width at least three. Documented in `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*, Section IV, line 1445
-/

open scoped BigOperators

namespace TNLean.PEPS

section GraphState

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The entry of the normalized Hadamard matrix,
$\frac{1}{\sqrt2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$.
Source: arXiv:2011.12127, line 1445. -/
noncomputable def hadamardEntry (i j : Fin 2) : ℂ :=
  Complex.invSqrtTwo * (-1) ^ (i.val * j.val)

/-- The factor of one leg of the vertex tensor: the copy tensor
$\ket{0\ldots0}+\ket{1\ldots1}$ on every leg, with the bond Hadamard absorbed into the
leg at the smaller endpoint of the bond. -/
noncomputable def graphStateLeg (v : V) (e : Edge G) (β s : Fin 2) : ℂ :=
  if e.1.1 = v then hadamardEntry s β else if β = s then 1 else 0

/-- The PEPS of the graph state on `G`: a copy tensor at every vertex and a Hadamard matrix
on every bond. Source: arXiv:2011.12127, line 1445. -/
noncomputable def graphStatePEPS : Tensor G 2 where
  bondDim _ := 2
  component v η s := ∏ ie : IncidentEdge G v, graphStateLeg G v ie.1 (η ie) s

@[simp] theorem graphStatePEPS_bondDim (e : Edge G) : (graphStatePEPS G).bondDim e = 2 := rfl

theorem graphStatePEPS_component (v : V)
    (η : (ie : IncidentEdge G v) → Fin ((graphStatePEPS G).bondDim ie.1)) (s : Fin 2) :
    (graphStatePEPS G).component v η s = ∏ ie : IncidentEdge G v, graphStateLeg G v ie.1 (η ie) s :=
  rfl

omit [Fintype V] in
/-- An edge incident to `v` determines the other endpoint. -/
def IncidentEdge.other {v : V} (ie : IncidentEdge G v) : V :=
  if ie.1.1.1 = v then ie.1.1.2 else ie.1.1.1

omit [Fintype V] [DecidableRel G.Adj] in
theorem IncidentEdge.adj_other {v : V} (ie : IncidentEdge G v) : G.Adj v ie.other := by
  rcases ie with ⟨⟨⟨a, b⟩, hab, hadj⟩, hv⟩
  unfold IncidentEdge.other
  dsimp only
  split_ifs with h
  · subst h
    exact hadj
  · rcases hv with h' | h'
    · exact absurd h' h
    · subst h'
      exact hadj.symm

/-- Edges incident to `v` correspond to the neighbours of `v`. -/
def incidentEdgeEquivNeighborFinset (v : V) :
    IncidentEdge G v ≃ {w // w ∈ G.neighborFinset v} where
  toFun ie := ⟨ie.other, (G.mem_neighborFinset v _).mpr ie.adj_other⟩
  invFun w := ⟨Edge.ofAdj ((G.mem_neighborFinset v w).mp w.2), by
    rcases Edge.ofAdj_endpoints ((G.mem_neighborFinset v w).mp w.2) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2⟩
  left_inv ie := by
    apply Subtype.ext
    refine Edge.ofAdj_eq_of_endpoints (IncidentEdge.adj_other G ie) ie.1 ?_
    rcases ie with ⟨⟨⟨a, b⟩, hab, hadj⟩, hv⟩
    unfold IncidentEdge.other
    dsimp only
    split_ifs with h
    · exact Or.inl ⟨h.symm, rfl⟩
    · rcases hv with h' | h'
      · exact absurd h' h
      · exact Or.inr ⟨h'.symm, rfl⟩
  right_inv w := by
    apply Subtype.ext
    have hadj := (G.mem_neighborFinset v w).mp w.2
    change IncidentEdge.other G ⟨Edge.ofAdj hadj, _⟩ = w
    unfold IncidentEdge.other
    rcases Edge.ofAdj_endpoints hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · have hne : (w : V) ≠ v := (G.ne_of_adj hadj).symm
      simp [h1, hne]

/-- The degree of a vertex counts its incident edges. -/
theorem card_incidentEdge (v : V) : Fintype.card (IncidentEdge G v) = G.degree v := by
  rw [Fintype.card_congr (incidentEdgeEquivNeighborFinset G v), Fintype.card_coe]
  rfl

/-- A product over vertices of products over incident edges is the product over edges of
the factors at both endpoints. -/
theorem prod_incidentEdge_eq_prod_edge {M : Type*} [CommMonoid M] (F : V → Edge G → M) :
    ∏ v, ∏ ie : IncidentEdge G v, F v ie.1 = ∏ e : Edge G, F e.1.1 e * F e.1.2 e := by
  have h1 (v : V) : ∏ ie : IncidentEdge G v, F v ie.1 =
      ∏ e : Edge G, if e.1.1 = v ∨ e.1.2 = v then F v e else 1 := by
    rw [← Finset.prod_filter]
    exact (Finset.prod_subtype _ (fun e => by simp) (F v)).symm
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [← Finset.prod_filter]
  have hne : e.1.1 ≠ e.1.2 := e.2.1.ne
  have : Finset.univ.filter (fun v => e.1.1 = v ∨ e.1.2 = v) = {e.1.1, e.1.2} := by
    ext v
    simp [eq_comm]
  rw [this, Finset.prod_pair hne]

/-- The graph-state PEPS is the controlled-Z circuit sign, times `2^{-|E|/2}`.
Source: arXiv:2011.12127, line 1445. -/
theorem stateCoeff_graphStatePEPS (σ : V → Fin 2) :
    stateCoeff (graphStatePEPS G) σ =
      Complex.invSqrtTwo ^ Fintype.card (Edge G) *
        graphCircuitSign (fun e : Edge G => e.1.1) (fun e => e.1.2) σ := by
  have hedge (e : Edge G) : ∑ β : Fin 2, graphStateLeg G e.1.1 e β (σ e.1.1) *
      graphStateLeg G e.1.2 e β (σ e.1.2) =
      Complex.invSqrtTwo * (-1) ^ ((σ e.1.1).val * (σ e.1.2).val) := by
    have hne : e.1.1 ≠ e.1.2 := e.2.1.ne
    simp [graphStateLeg, hne, hadamardEntry]
  rw [stateCoeff]
  simp only [graphStatePEPS_component]
  rw [Finset.sum_congr rfl fun η _ =>
    prod_incidentEdge_eq_prod_edge G (fun v e => graphStateLeg G v e (η e) (σ v))]
  calc _ = ∏ e : Edge G, ∑ β : Fin 2, graphStateLeg G e.1.1 e β (σ e.1.1) *
        graphStateLeg G e.1.2 e β (σ e.1.2) := (Fintype.prod_sum _).symm
    _ = _ := by
      simp only [hedge, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        graphCircuitSign]

/-- A vertex with at least two bonds has a non-injective vertex tensor: it maps the
virtual space of dimension `2 ^ deg` onto the qubit, of dimension two. -/
theorem not_linearIndependent_graphStatePEPS_component (v : V) (hv : 2 ≤ G.degree v) :
    ¬ LinearIndependent ℂ ((graphStatePEPS G).component v) := by
  intro h
  have hc := h.fintype_card_le_finrank
  have hcard : Fintype.card ((ie : IncidentEdge G v) → Fin ((graphStatePEPS G).bondDim ie.1)) =
      2 ^ G.degree v := by
    rw [Fintype.card_pi, ← card_incidentEdge]
    calc ∏ i, Fintype.card (Fin ((graphStatePEPS G).bondDim i.1)) = ∏ _i : IncidentEdge G v, 2 :=
          Finset.prod_congr rfl fun i _ => Fintype.card_fin _
      _ = _ := by simp
  rw [hcard, Module.finrank_fin_fun] at hc
  have : 2 ^ 2 ≤ 2 ^ G.degree v := Nat.pow_le_pow_right (by norm_num) hv
  omega

/-- The neighbour factor of a graph stabilizer is `Z` at every neighbour. -/
theorem graphNeighborSign_edge (v : V) (s : V → Fin 2) :
    graphNeighborSign (fun e : Edge G => e.1.1) (fun e => e.1.2) v s =
      ∏ w ∈ G.neighborFinset v, (-1 : ℂ) ^ (s w).val := by
  have h1 : graphNeighborSign (fun e : Edge G => e.1.1) (fun e => e.1.2) v s =
      ∏ ie : IncidentEdge G v, (-1 : ℂ) ^ (s ie.other).val := by
    rw [graphNeighborSign]
    symm
    simp only [IncidentEdge.other]
    calc ∏ ie : IncidentEdge G v,
          (-1 : ℂ) ^ (s (if ie.1.1.1 = v then ie.1.1.2 else ie.1.1.1)).val
        = ∏ e ∈ Finset.univ.filter (fun e : Edge G => e.1.1 = v ∨ e.1.2 = v),
            (-1 : ℂ) ^ (s (if e.1.1 = v then e.1.2 else e.1.1)).val :=
          (Finset.prod_subtype (p := fun e : Edge G => e.1.1 = v ∨ e.1.2 = v)
            (Finset.univ.filter fun e : Edge G => e.1.1 = v ∨ e.1.2 = v)
            (fun e => by simp)
            (fun e : Edge G => (-1 : ℂ) ^ (s (if e.1.1 = v then e.1.2 else e.1.1)).val)).symm
      _ = _ := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun e _ => ?_
        by_cases ha : e.1.1 = v
        · simp [ha]
        · by_cases hb : e.1.2 = v <;> simp [ha, hb]
  have h2 : ∏ ie : IncidentEdge G v, (-1 : ℂ) ^ (s ie.other).val =
      ∏ w : {w // w ∈ G.neighborFinset v}, (-1 : ℂ) ^ (s w).val :=
    Fintype.prod_equiv (incidentEdgeEquivNeighborFinset G v) _ _ fun _ => rfl
  rw [h1, h2]
  exact Finset.prod_coe_sort (G.neighborFinset v) (fun w => (-1 : ℂ) ^ (s w).val)

end GraphState

section Honeycomb

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- A site of the brick wall whose vertical bond points up: the coordinate sum is even. -/
def honeycombUp (v : TorusVertex width height) : Prop :=
  (v.1.val + v.2.val) % 2 = 0

instance (v : TorusVertex width height) : Decidable (honeycombUp width height v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The brick-wall honeycomb on the torus: horizontal bonds to both horizontal neighbours,
and one vertical bond at each site, up from sites with even coordinate sum and down from the
others. Source: arXiv:2011.12127, line 1445 ("the honeycomb lattice"). -/
def honeycombGraph : SimpleGraph (TorusVertex width height) where
  Adj v w := (v.2 = w.2 ∧ (w.1 = v.1 + 1 ∨ v.1 = w.1 + 1)) ∨
    (v.1 = w.1 ∧ ((w.2 = v.2 + 1 ∧ honeycombUp width height v) ∨
      (v.2 = w.2 + 1 ∧ honeycombUp width height w)))
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun v h => by
    rcases h with ⟨_, h | h⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩ <;> simp at h⟩

instance : DecidableRel (honeycombGraph width height).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The cluster PEPS on the honeycomb torus. Source: arXiv:2011.12127, line 1445. -/
noncomputable abbrev honeycombClusterPEPS : Tensor (honeycombGraph width height) 2 :=
  graphStatePEPS (honeycombGraph width height)

/-- The stabilizer `X_i Z_j Z_k Z_l` of the honeycomb cluster state at `v`.
Source: arXiv:2011.12127, line 1445. -/
abbrev honeycombStabilizer (v : TorusVertex width height)
    (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    (TorusVertex width height → Fin 2) → ℂ :=
  graphStabilizer (fun e : Edge (honeycombGraph width height) => e.1.1) (fun e => e.1.2) v ψ

/-- The parent Hamiltonian `-∑ X_i Z_j Z_k Z_l` of the honeycomb cluster state.
Source: arXiv:2011.12127, line 1445, with the sign fixed as recorded in the module
docstring. -/
abbrev honeycombHamiltonian (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    (TorusVertex width height → Fin 2) → ℂ :=
  graphHamiltonian (fun e : Edge (honeycombGraph width height) => e.1.1) (fun e => e.1.2) ψ

private lemma edge_ne (e : Edge (honeycombGraph width height)) : e.1.1 ≠ e.1.2 := e.2.1.ne

/-- The honeycomb stabilizer is `X` at `v` times `Z` at each nearest neighbour.
Source: arXiv:2011.12127, line 1445. -/
theorem honeycombStabilizer_apply (v : TorusVertex width height)
    (ψ : (TorusVertex width height → Fin 2) → ℂ) (s : TorusVertex width height → Fin 2) :
    honeycombStabilizer width height v ψ s =
      (∏ w ∈ (honeycombGraph width height).neighborFinset v, (-1 : ℂ) ^ (s w).val) *
        ψ (graphFlip v s) := by
  rw [honeycombStabilizer, graphStabilizer, graphNeighborSign_edge]

/-- The vertical neighbour of a site of the brick wall. -/
def honeycombVertical (v : TorusVertex width height) : TorusVertex width height :=
  if honeycombUp width height v then (v.1, v.2 + 1) else (v.1, v.2 - 1)

omit [NeZero width] [Fact (1 < width)] in
private lemma honeycombUp_add_one [Fact (Even height)] (x : ZMod width) (y : ZMod height) :
    honeycombUp width height (x, y + 1) ↔ ¬ honeycombUp width height (x, y) := by
  have hdvd : 2 ∣ height := even_iff_two_dvd.mp (Fact.out : Even height)
  simp only [honeycombUp, ZMod.val_add, ZMod.val_one]
  have := Nat.mod_mod_of_dvd (y.val + 1) hdvd
  generalize (y.val + 1) % height = k at *
  omega

/-- On a torus of even height and width at least three, every site of the brick wall has
exactly the three nearest neighbours of the honeycomb lattice: its two horizontal neighbours
and its vertical neighbour. Source: arXiv:2011.12127, line 1445. -/
theorem honeycombGraph_neighborFinset [Fact (Even height)] [Fact (2 < width)]
    (v : TorusVertex width height) :
    (honeycombGraph width height).neighborFinset v =
      {(v.1 + 1, v.2), (v.1 - 1, v.2), honeycombVertical width height v} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  have hup := honeycombUp_add_one width height w.1 w.2
  by_cases hv : honeycombUp width height v
  · rw [show honeycombVertical width height v = (v.1, v.2 + 1) by simp [honeycombVertical, hv]]
    simp only [honeycombGraph, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    constructor
    · rintro (⟨h1, h2 | h2⟩ | ⟨h1, ⟨h2, -⟩ | ⟨h2, h3⟩⟩)
      · exact Or.inl ⟨h2, h1.symm⟩
      · exact Or.inr (Or.inl ⟨by rw [h2]; ring, h1.symm⟩)
      · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
      · exfalso
        have hvw : v = (w.1, w.2 + 1) := Prod.ext h1 h2
        rw [hvw] at hv
        exact hup.mp hv h3
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2.symm, Or.inl h1⟩
      · exact Or.inl ⟨h2.symm, Or.inr (by rw [h1]; ring)⟩
      · exact Or.inr ⟨h1.symm, Or.inl ⟨h2, hv⟩⟩
  · rw [show honeycombVertical width height v = (v.1, v.2 - 1) by simp [honeycombVertical, hv]]
    simp only [honeycombGraph, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    constructor
    · rintro (⟨h1, h2 | h2⟩ | ⟨h1, ⟨-, h3⟩ | ⟨h2, h3⟩⟩)
      · exact Or.inl ⟨h2, h1.symm⟩
      · exact Or.inr (Or.inl ⟨by rw [h2]; ring, h1.symm⟩)
      · exact absurd h3 hv
      · exact Or.inr (Or.inr ⟨h1.symm, by rw [h2]; ring⟩)
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2.symm, Or.inl h1⟩
      · exact Or.inl ⟨h2.symm, Or.inr (by rw [h1]; ring)⟩
      · refine Or.inr ⟨h1.symm, Or.inr ⟨by rw [h2]; ring, ?_⟩⟩
        have hvw : v = (w.1, w.2 + 1) := Prod.ext h1.symm (by rw [h2]; ring)
        by_contra hc
        rw [hvw] at hv
        exact hv (hup.mpr hc)

/-- On a torus of even height and width at least three, the brick wall is three-regular.
Source: arXiv:2011.12127, line 1445 ("$j,k,l$ are the nearest neigbours of site $i$"). -/
theorem honeycombGraph_degree [Fact (Even height)] [Fact (2 < width)]
    (v : TorusVertex width height) : (honeycombGraph width height).degree v = 3 := by
  have h1 : (1 : ZMod width) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod width) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 width).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    have := (Fact.out : 2 < width)
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, honeycombGraph_neighborFinset]
  have hvert : (honeycombVertical width height v).1 = v.1 := by
    unfold honeycombVertical; split_ifs <;> rfl
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · intro h
    rw [Finset.mem_singleton, Prod.ext_iff, hvert] at h
    exact h1 (by simpa using h.1)
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, hvert] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · apply h2
      have : (2 : ZMod width) = (v.1 + 1) - (v.1 - 1) := by ring
      rw [this, h, sub_self]
    · simp at h

/-- The honeycomb cluster PEPS is the controlled-Z circuit sign, times `2^{-|E|/2}`.
Source: arXiv:2011.12127, line 1445. -/
theorem stateCoeff_honeycombClusterPEPS :
    stateCoeff (honeycombClusterPEPS width height) =
      Complex.invSqrtTwo ^ Fintype.card (Edge (honeycombGraph width height)) •
        graphCircuitSign (fun e : Edge (honeycombGraph width height) => e.1.1)
          (fun e => e.1.2) := by
  funext σ
  exact stateCoeff_graphStatePEPS _ σ

/-- The honeycomb stabilizers commute. Source: arXiv:2011.12127, line 1445,
"the commuting parent Hamiltonian". -/
theorem honeycombStabilizer_comm (v w : TorusVertex width height)
    (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    honeycombStabilizer width height v (honeycombStabilizer width height w ψ) =
      honeycombStabilizer width height w (honeycombStabilizer width height v ψ) :=
  graphStabilizer_comm _ _ (edge_ne width height) v w ψ

/-- The common fixed space of the honeycomb stabilizers is the line of the honeycomb
cluster PEPS. Source: arXiv:2011.12127, line 1445. -/
theorem honeycombStabilizer_fixed_iff (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    (∀ v, honeycombStabilizer width height v ψ = ψ) ↔
      ∃ c : ℂ, ψ = c • stateCoeff (honeycombClusterPEPS width height) := by
  rw [graphStabilizer_fixed_iff _ _ (edge_ne width height), stateCoeff_honeycombClusterPEPS]
  have hk : Complex.invSqrtTwo ^ Fintype.card (Edge (honeycombGraph width height)) ≠ 0 :=
    pow_ne_zero _ Complex.invSqrtTwo_ne_zero
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c / _, by rw [smul_smul, div_mul_cancel₀ _ hk]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, smul_smul _ _ _⟩

/-- The parent Hamiltonian `-∑ X_i Z_j Z_k Z_l` is bounded below by minus the number of
sites. Source: arXiv:2011.12127, line 1445. -/
theorem neg_card_mul_le_re_honeycombHamiltonian
    (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    -(Fintype.card (TorusVertex width height) : ℝ) * ∑ s, Complex.normSq (ψ s) ≤
      (∑ s, star (ψ s) * honeycombHamiltonian width height ψ s).re :=
  neg_card_mul_le_re_sum_star_mul_graphHamiltonian _ _ (edge_ne width height) ψ

/-- The honeycomb cluster state is the unique ground state of the commuting parent
Hamiltonian `-∑ X_i Z_j Z_k Z_l`: the lower bound `-|V|` is attained exactly on its line.
Source: arXiv:2011.12127, line 1445, with the sign fixed as recorded in the module
docstring. -/
theorem honeycombHamiltonian_eq_neg_card_smul_iff
    (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    honeycombHamiltonian width height ψ =
        -(Fintype.card (TorusVertex width height) : ℂ) • ψ ↔
      ∃ c : ℂ, ψ = c • stateCoeff (honeycombClusterPEPS width height) := by
  rw [graphHamiltonian_eq_neg_card_smul_iff _ _ (edge_ne width height)]
  exact honeycombStabilizer_fixed_iff width height ψ

/-- The honeycomb cluster PEPS is nonzero. -/
theorem stateCoeff_honeycombClusterPEPS_ne_zero :
    stateCoeff (honeycombClusterPEPS width height) ≠ 0 := by
  intro h
  have h0 := congrFun h (fun _ => 0)
  rw [stateCoeff_honeycombClusterPEPS] at h0
  simp [graphCircuitSign, Complex.invSqrtTwo_ne_zero] at h0

/-- The vertex tensor of the honeycomb cluster PEPS is not injective: the origin has two
bonds and its tensor maps four or more virtual configurations to a qubit. The source's
injectivity holds only after blocking. Source: arXiv:2011.12127, line 1445. -/
theorem not_isVertexInjective_honeycombClusterPEPS :
    ¬ IsVertexInjective (honeycombClusterPEPS width height) := by
  intro h
  apply not_linearIndependent_graphStatePEPS_component _ 0 _ (h 0)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h1 : (1, 0) ∈ (honeycombGraph width height).neighborFinset 0 := by
    rw [SimpleGraph.mem_neighborFinset]
    exact Or.inl ⟨rfl, Or.inl (by simp)⟩
  have h2 : (0, 1) ∈ (honeycombGraph width height).neighborFinset 0 := by
    rw [SimpleGraph.mem_neighborFinset]
    exact Or.inr ⟨rfl, Or.inl ⟨by simp, by simp [honeycombUp]⟩⟩
  have hne : ((1, 0) : TorusVertex width height) ≠ (0, 1) := by
    simp [Prod.ext_iff]
  exact Finset.one_lt_card.mpr ⟨_, h1, _, h2, hne⟩

end Honeycomb

end TNLean.PEPS
