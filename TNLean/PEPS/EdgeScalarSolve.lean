import TNLean.PEPS.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Edge-scalar solve on a connected graph

This file proves the combinatorial heart of the absorption step in the
Fundamental Theorem for injective PEPS (arXiv:1804.04964, Section 3): on a
connected simple graph, a family of vertex scalars whose product is `1` can be
realized as the oriented incidence product of a family of edge scalars.

Concretely, for a vertex `v` and an edge `e` incident to `v`, the *oriented
endpoint contribution* of an edge scalar `s e` is `s e` when `v` is the lower
endpoint of `e` (`e.1.1 = v`) and `(s e)⁻¹` when `v` is the upper endpoint.
The main result `exists_edgeScalars_of_connected` states that for a connected
graph and any `t : V → ℂˣ` with `∏ v, t v = 1` there is `s : Edge G → ℂˣ` whose
oriented incidence product at every vertex `v` equals `t v`.

This is the spanning-tree coboundary step recorded in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`: the oriented
incidence product of any edge-scalar family has product `1` over all vertices,
so the constraint `∏ v, t v = 1` is exactly the solvability condition on a
connected graph.

The proof is by induction on `Fintype.card V`, removing one vertex whose
deletion keeps the graph connected
(`SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`).
-/

open scoped BigOperators
open SimpleGraph

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The oriented endpoint contribution of an edge scalar `s` at a vertex `v`
along an incident edge `ie`: `s` at the lower endpoint, `s⁻¹` at the upper. -/
def edgeScalarUnit (s : Edge G → ℂˣ) (v : V) (ie : IncidentEdge G v) : ℂˣ :=
  if ie.1.1.1 = v then s ie.1 else (s ie.1)⁻¹

/-- The oriented incidence product of an edge-scalar family at a vertex. -/
noncomputable def orientedIncidence (s : Edge G → ℂˣ) (v : V) : ℂˣ :=
  ∏ ie : IncidentEdge G v, edgeScalarUnit (G := G) s v ie

/-! ### Necessity: the global product of oriented incidences is `1`

The oriented incidence product cancels each edge scalar against its own inverse
across the edge's two endpoints, so the product over all vertices is `1`. This
is the solvability obstruction recorded in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`: any family that is
the oriented incidence product of edge scalars necessarily has product `1`. -/

/-- The two endpoints of an edge, as a finite index type. -/
def incVertex (e : Edge G) : Type _ := {v : V // e.1.1 = v ∨ e.1.2 = v}

instance (e : Edge G) : Fintype (incVertex (G := G) e) := by
  unfold incVertex; infer_instance

instance (e : Edge G) : DecidableEq (incVertex (G := G) e) := by
  unfold incVertex; infer_instance

/-- Swap the index of the disjoint union over incident edges from
"vertex, then incident edge" to "edge, then incident vertex". -/
noncomputable def sigmaSwap :
    (Σ v : V, IncidentEdge G v) ≃ (Σ e : Edge G, incVertex (G := G) e) :=
  ((Equiv.subtypeProdEquivSigmaSubtype
      (fun (v : V) (e : Edge G) => e.1.1 = v ∨ e.1.2 = v)).symm.trans
    ((Equiv.prodComm V (Edge G)).subtypeEquiv fun _ => Iff.rfl)).trans
      (Equiv.subtypeProdEquivSigmaSubtype
        (fun (e : Edge G) (v : V) => e.1.1 = v ∨ e.1.2 = v))

omit [DecidableRel G.Adj] in
/-- The product of the two oriented endpoint contributions of a single edge is
`1`: the lower endpoint carries `s e` and the upper endpoint carries `(s e)⁻¹`. -/
theorem prod_incVertex_endpoint (s : Edge G → ℂˣ) (e : Edge G) :
    (∏ x : incVertex (G := G) e, (if e.1.1 = x.1 then s e else (s e)⁻¹)) = 1 := by
  have hne : (e.1.1 : V) ≠ e.1.2 := ne_of_lt e.2.1
  have huniv : (Finset.univ : Finset (incVertex (G := G) e)) =
        {⟨e.1.1, Or.inl rfl⟩, ⟨e.1.2, Or.inr rfl⟩} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases x.2 with h | h
    · exact Or.inl (Subtype.ext h.symm)
    · exact Or.inr (Subtype.ext h.symm)
  rw [huniv,
    Finset.prod_insert
      (by rw [Finset.mem_singleton]; exact fun h => hne (congrArg Subtype.val h)),
    Finset.prod_singleton, if_pos rfl, if_neg hne, mul_inv_cancel]

/-- **Necessity of the product-one condition.** For any edge-scalar family, the
product of the oriented incidences over all vertices is `1`. -/
theorem prod_orientedIncidence_eq_one (s : Edge G → ℂˣ) :
    (∏ v : V, orientedIncidence (G := G) s v) = 1 := by
  have hsigma : (∏ v : V, orientedIncidence (G := G) s v)
      = ∏ p : (Σ v : V, IncidentEdge G v), edgeScalarUnit (G := G) s p.1 p.2 := by
    simp only [orientedIncidence]
    exact (Fintype.prod_sigma
      (fun p : (Σ v : V, IncidentEdge G v) => edgeScalarUnit (G := G) s p.1 p.2)).symm
  rw [hsigma, ← Equiv.prod_comp (sigmaSwap (G := G)).symm, Fintype.prod_sigma]
  calc (∏ e : Edge G, ∏ x : incVertex (G := G) e,
          edgeScalarUnit (G := G) s ((sigmaSwap (G := G)).symm ⟨e, x⟩).1
            ((sigmaSwap (G := G)).symm ⟨e, x⟩).2)
      = ∏ e : Edge G, ∏ x : incVertex (G := G) e,
          (if e.1.1 = x.1 then s e else (s e)⁻¹) :=
        Finset.prod_congr rfl fun e _ => Finset.prod_congr rfl fun x _ => rfl
    _ = ∏ _e : Edge G, (1 : ℂˣ) :=
        Finset.prod_congr rfl fun e _ => prod_incVertex_endpoint s e
    _ = 1 := Finset.prod_const_one

/-! ### Vertex deletion: transferring edges to and from `G.induce {v₀}ᶜ`

The existence (sufficiency) direction is proved by induction on the number of
vertices, removing one vertex `v₀` whose deletion keeps the graph connected. The
lemmas below transfer edges and oriented incidence products between `G` and the
induced subgraph `G.induce {v₀}ᶜ`. -/

/-- Lift an edge of the vertex-deleted subgraph `G.induce {v₀}ᶜ` to an edge of
`G`, by forgetting the subtype proofs on the endpoints. -/
noncomputable def liftEdge (v₀ : V) (e : Edge (G.induce ({v₀}ᶜ : Set V))) : Edge G :=
  ⟨((e.1.1 : V), (e.1.2 : V)), by
    refine ⟨Subtype.coe_lt_coe.mpr e.2.1, ?_⟩
    have := e.2.2; rwa [induce_adj] at this⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A lifted edge does not have `v₀` as its lower endpoint. -/
theorem liftEdge_ne_fst (v₀ : V) (e : Edge (G.induce ({v₀}ᶜ : Set V))) :
    (liftEdge (G := G) v₀ e).1.1 ≠ v₀ := by
  have h := e.1.1.2; rw [Set.mem_compl_iff, Set.mem_singleton_iff] at h; exact h

omit [Fintype V] [DecidableRel G.Adj] in
/-- A lifted edge does not have `v₀` as its upper endpoint. -/
theorem liftEdge_ne_snd (v₀ : V) (e : Edge (G.induce ({v₀}ᶜ : Set V))) :
    (liftEdge (G := G) v₀ e).1.2 ≠ v₀ := by
  have h := e.1.2.2; rw [Set.mem_compl_iff, Set.mem_singleton_iff] at h; exact h

/-- Restrict an edge of `G` that avoids `v₀` to an edge of `G.induce {v₀}ᶜ`. -/
noncomputable def restrictEdge (v₀ : V) (e : Edge G)
    (h1 : e.1.1 ≠ v₀) (h2 : e.1.2 ≠ v₀) : Edge (G.induce ({v₀}ᶜ : Set V)) :=
  ⟨(⟨e.1.1, by simp [h1]⟩, ⟨e.1.2, by simp [h2]⟩), by
    refine ⟨Subtype.coe_lt_coe.mpr e.2.1, ?_⟩
    rw [induce_adj]; exact e.2.2⟩

/-- The predicate that `v₀` is an endpoint of an edge of `G`. -/
def v0Inc (v₀ : V) (e : Edge G) : Prop := e.1.1 = v₀ ∨ e.1.2 = v₀

instance (v₀ : V) (e : Edge G) : Decidable (v0Inc (G := G) v₀ e) := by
  unfold v0Inc; infer_instance

/-- The bijection between edges of `G.induce {v₀}ᶜ` incident to `w` and edges of
`G` incident to `w` that avoid `v₀`. -/
noncomputable def incEquiv (v₀ : V) (w : (↑({v₀}ᶜ : Set V))) :
    IncidentEdge (G.induce ({v₀}ᶜ : Set V)) w ≃
      {ie : IncidentEdge G (w : V) // ¬ v0Inc (G := G) v₀ ie.1} where
  toFun ie := ⟨⟨liftEdge (G := G) v₀ ie.1, by
      rcases ie.2 with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)⟩, by
      rintro (h | h)
      · exact liftEdge_ne_fst (G := G) v₀ ie.1 h
      · exact liftEdge_ne_snd (G := G) v₀ ie.1 h⟩
  invFun p := ⟨restrictEdge (G := G) v₀ p.1.1
      (fun h => p.2 (Or.inl h)) (fun h => p.2 (Or.inr h)), by
      rcases p.1.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)⟩
  left_inv ie := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv p := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Prod.ext <;> rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The oriented endpoint contribution is preserved by `incEquiv` when the edge
scalars agree under lifting. -/
theorem edgeScalarUnit_incEquiv (v₀ : V) (w : (↑({v₀}ᶜ : Set V)))
    (s : Edge G → ℂˣ) (s' : Edge (G.induce ({v₀}ᶜ : Set V)) → ℂˣ)
    (hs : ∀ e, s (liftEdge (G := G) v₀ e) = s' e)
    (ie : IncidentEdge (G.induce ({v₀}ᶜ : Set V)) w) :
    edgeScalarUnit (G := G) s (w : V) ((incEquiv (G := G) v₀ w ie).1)
      = edgeScalarUnit (G := G.induce ({v₀}ᶜ : Set V)) s' w ie := by
  have hlift : ((incEquiv (G := G) v₀ w ie).1).1 = liftEdge (G := G) v₀ ie.1 := rfl
  have hcond : ((liftEdge (G := G) v₀ ie.1).1.1 = (w : V)) ↔ (ie.1.1.1 = w) :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  unfold edgeScalarUnit
  rw [hlift, hs]
  by_cases h : ie.1.1.1 = w
  · rw [if_pos h, if_pos (hcond.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hcond.mp hh))]

/-- The product of oriented endpoint contributions over the `v₀`-avoiding
incident edges of `w` equals the oriented incidence of `s'` in the
vertex-deleted subgraph. -/
theorem prod_free_eq (v₀ : V) (w : (↑({v₀}ᶜ : Set V)))
    (s : Edge G → ℂˣ) (s' : Edge (G.induce ({v₀}ᶜ : Set V)) → ℂˣ)
    (hs : ∀ e, s (liftEdge (G := G) v₀ e) = s' e) :
    (∏ ie : {ie : IncidentEdge G (w : V) // ¬ v0Inc (G := G) v₀ ie.1},
        edgeScalarUnit (G := G) s (w : V) ie.1)
      = orientedIncidence (G := G.induce ({v₀}ᶜ : Set V)) s' w := by
  rw [orientedIncidence, ← Equiv.prod_comp (incEquiv (G := G) v₀ w)]
  exact Finset.prod_congr rfl fun ie _ => edgeScalarUnit_incEquiv (G := G) v₀ w s s' hs ie

/-! ### The `v₀`-incident part of an oriented incidence product

For a vertex `w ≠ v₀`, the edges of `G` incident to both `w` and `v₀` form a
subsingleton (the unique edge `{v₀, w}`, if any). The lemmas below compute the
`v₀`-incident part of `w`'s oriented incidence product. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- The endpoint pair of an edge incident to both `w` and `v₀` (with `w ≠ v₀`) is
forced to be `(min v₀ w, max v₀ w)`. -/
theorem v0Inc_pair (v₀ w : V) (hw : w ≠ v₀) (e : Edge G)
    (hinc : e.1.1 = w ∨ e.1.2 = w) (hv0 : v0Inc (G := G) v₀ e) :
    e.1 = (min v₀ w, max v₀ w) := by
  have hlt := e.2.1
  rcases hinc with hw1 | hw2 <;> rcases hv0 with hv1 | hv2
  · exact absurd (hw1.symm.trans hv1) hw
  · have hwv : w < v₀ := hw1 ▸ hv2 ▸ hlt
    rw [Prod.ext_iff]; exact ⟨by rw [hw1, min_eq_right hwv.le], by rw [hv2, max_eq_left hwv.le]⟩
  · have hvw : v₀ < w := hv1 ▸ hw2 ▸ hlt
    rw [Prod.ext_iff]; exact ⟨by rw [hv1, min_eq_left hvw.le], by rw [hw2, max_eq_right hvw.le]⟩
  · exact absurd (hw2.symm.trans hv2) hw

/-- The edges of `G` incident to both `w` and `v₀` (with `w ≠ v₀`) form a
subsingleton. -/
theorem v0Inc_subsingleton (v₀ w : V) (hw : w ≠ v₀) :
    Subsingleton {ie : IncidentEdge G w // v0Inc (G := G) v₀ ie.1} := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [v0Inc_pair (G := G) v₀ w hw a.1.1 a.1.2 a.2,
      v0Inc_pair (G := G) v₀ w hw b.1.1 b.1.2 b.2]

/-- The edge `{v₀, w₀}` of `G`, ordered. -/
noncomputable def edge0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) : Edge G :=
  ⟨(min v₀ w₀, max v₀ w₀), by
    have hne : v₀ ≠ w₀ := G.ne_of_adj hadj
    refine ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    · rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact hadj
      · rw [min_eq_right h.le, max_eq_left h.le]; exact hadj.symm⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem edge0_inc_v0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) :
    (edge0 (G := G) v₀ w₀ hadj).1.1 = v₀ ∨ (edge0 (G := G) v₀ w₀ hadj).1.2 = v₀ := by
  rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
  · left
    change min v₀ w₀ = v₀
    exact min_eq_left h.le
  · right
    change max v₀ w₀ = v₀
    exact max_eq_left h.le

omit [Fintype V] [DecidableRel G.Adj] in
theorem edge0_inc_w0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) :
    (edge0 (G := G) v₀ w₀ hadj).1.1 = w₀ ∨ (edge0 (G := G) v₀ w₀ hadj).1.2 = w₀ := by
  rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
  · right
    change max v₀ w₀ = w₀
    exact max_eq_right h.le
  · left
    change min v₀ w₀ = w₀
    exact min_eq_right h.le

omit [Fintype V] [DecidableRel G.Adj] in
theorem edge0_v0Inc (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) :
    v0Inc (G := G) v₀ (edge0 (G := G) v₀ w₀ hadj) := by
  rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
  · left
    change min v₀ w₀ = v₀
    exact min_eq_left h.le
  · right
    change max v₀ w₀ = v₀
    exact max_eq_left h.le

/-- If the edge scalar is `1` on every `v₀`-incident edge other than `{v₀, w₀}`,
then the `v₀`-incident part of the oriented incidence product at a vertex
`v ≠ v₀, w₀` is `1`. -/
theorem v0Inc_prod_ne (v₀ w₀ v : V) (hv : v ≠ v₀) (hvw₀ : v ≠ w₀) (s : Edge G → ℂˣ)
    (hs1 : ∀ e : Edge G, v0Inc (G := G) v₀ e → e.1 ≠ (min v₀ w₀, max v₀ w₀) → s e = 1) :
    (∏ ie : {ie : IncidentEdge G v // v0Inc (G := G) v₀ ie.1},
        edgeScalarUnit (G := G) s v ie.1) = 1 := by
  refine Finset.prod_eq_one (fun ie _ => ?_)
  have hpair := v0Inc_pair (G := G) v₀ v hv ie.1.1 ie.1.2 ie.2
  have hne : ie.1.1.1 ≠ (min v₀ w₀, max v₀ w₀) := by
    rw [hpair]
    intro hc
    rw [Prod.ext_iff] at hc
    apply hvw₀
    rcases le_total v₀ v with h | h <;> rcases le_total v₀ w₀ with h' | h' <;>
      simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  rw [edgeScalarUnit, hs1 ie.1.1 ie.2 hne]
  simp

/-- The `v₀`-incident part of the oriented incidence product at `w₀` collapses to
the single contribution of the edge `{v₀, w₀}`. -/
theorem v0Inc_prod_w0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) (hw₀ne : w₀ ≠ v₀)
    (s : Edge G → ℂˣ) :
    (∏ ie : {ie : IncidentEdge G w₀ // v0Inc (G := G) v₀ ie.1},
        edgeScalarUnit (G := G) s w₀ ie.1)
      = edgeScalarUnit (G := G) s w₀
          ⟨edge0 (G := G) v₀ w₀ hadj, edge0_inc_w0 (G := G) v₀ w₀ hadj⟩ := by
  have : Subsingleton {ie : IncidentEdge G w₀ // v0Inc (G := G) v₀ ie.1} :=
    v0Inc_subsingleton (G := G) v₀ w₀ hw₀ne
  set a0 : {ie : IncidentEdge G w₀ // v0Inc (G := G) v₀ ie.1} :=
    ⟨⟨edge0 (G := G) v₀ w₀ hadj, edge0_inc_w0 (G := G) v₀ w₀ hadj⟩,
      edge0_v0Inc (G := G) v₀ w₀ hadj⟩
  refine Finset.prod_eq_single a0 ?_ ?_
  · intro b _ hb; exact absurd (Subsingleton.elim b a0) hb
  · intro hb; exact absurd (Finset.mem_univ a0) hb

/-- Splitting the oriented incidence product at `w` into its `v₀`-incident and
`v₀`-avoiding parts. -/
theorem orientedIncidence_split (v₀ : V) (s : Edge G → ℂˣ) (w : V) :
    orientedIncidence (G := G) s w
      = (∏ ie : {ie : IncidentEdge G w // v0Inc (G := G) v₀ ie.1},
            edgeScalarUnit (G := G) s w ie.1)
        * (∏ ie : {ie : IncidentEdge G w // ¬ v0Inc (G := G) v₀ ie.1},
            edgeScalarUnit (G := G) s w ie.1) := by
  classical
  rw [orientedIncidence,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun ie : IncidentEdge G w => v0Inc (G := G) v₀ ie.1)
      (fun ie => edgeScalarUnit (G := G) s w ie)]
  congr 1
  · exact Finset.prod_subtype _ (by intro x; simp) (fun ie => edgeScalarUnit (G := G) s w ie)
  · exact Finset.prod_subtype _ (by intro x; simp) (fun ie => edgeScalarUnit (G := G) s w ie)

/-- The oriented incidence product at `v₀` collapses to the single contribution
of the edge `{v₀, w₀}`, when the edge scalar is `1` on every other `v₀`-incident
edge. -/
theorem orientedIncidence_v0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) (s : Edge G → ℂˣ)
    (hs1 : ∀ e : Edge G, v0Inc (G := G) v₀ e → e.1 ≠ (min v₀ w₀, max v₀ w₀) → s e = 1) :
    orientedIncidence (G := G) s v₀
      = edgeScalarUnit (G := G) s v₀
          ⟨edge0 (G := G) v₀ w₀ hadj, edge0_inc_v0 (G := G) v₀ w₀ hadj⟩ := by
  rw [orientedIncidence]
  refine Finset.prod_eq_single
    (⟨edge0 (G := G) v₀ w₀ hadj, edge0_inc_v0 (G := G) v₀ w₀ hadj⟩ : IncidentEdge G v₀) ?_ ?_
  · intro b _ hb
    have hv0b : v0Inc (G := G) v₀ b.1 := by
      rcases b.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    rw [edgeScalarUnit, hs1 b.1 hv0b (by
      intro hc; apply hb; apply Subtype.ext; apply Subtype.ext; rw [hc]; rfl)]
    simp
  · intro hb; exact absurd (Finset.mem_univ _) hb

omit [Fintype V] [DecidableRel G.Adj] in
/-- When `s` carries the chosen scalar `t v₀^{±}` on the edge `{v₀, w₀}`, the
oriented contribution of that edge at `v₀` is `t v₀`. -/
theorem unit_at_v0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) (t : V → ℂˣ) (s : Edge G → ℂˣ)
    (hs0 : s (edge0 (G := G) v₀ w₀ hadj) = (if v₀ < w₀ then t v₀ else (t v₀)⁻¹))
    (hinc : (edge0 (G := G) v₀ w₀ hadj).1.1 = v₀ ∨ (edge0 (G := G) v₀ w₀ hadj).1.2 = v₀) :
    edgeScalarUnit (G := G) s v₀ ⟨edge0 (G := G) v₀ w₀ hadj, hinc⟩ = t v₀ := by
  have hne : v₀ ≠ w₀ := G.ne_of_adj hadj
  rw [edgeScalarUnit, hs0]
  change (if (edge0 (G := G) v₀ w₀ hadj).1.1 = v₀ then _ else _) = t v₀
  rcases lt_or_gt_of_ne hne with h | h
  · have hl : (edge0 (G := G) v₀ w₀ hadj).1.1 = v₀ := by
      change min v₀ w₀ = v₀; exact min_eq_left h.le
    rw [if_pos hl, if_pos h]
  · have hl : ¬ (edge0 (G := G) v₀ w₀ hadj).1.1 = v₀ := by
      change ¬ min v₀ w₀ = v₀; rw [min_eq_right h.le]; exact ne_of_lt h
    rw [if_neg hl, if_neg (not_lt.mpr h.le), inv_inv]

omit [Fintype V] [DecidableRel G.Adj] in
/-- When `s` carries the chosen scalar `t v₀^{±}` on the edge `{v₀, w₀}`, the
oriented contribution of that edge at `w₀` is `(t v₀)⁻¹`. -/
theorem unit_at_w0 (v₀ w₀ : V) (hadj : G.Adj v₀ w₀) (t : V → ℂˣ) (s : Edge G → ℂˣ)
    (hs0 : s (edge0 (G := G) v₀ w₀ hadj) = (if v₀ < w₀ then t v₀ else (t v₀)⁻¹))
    (hinc : (edge0 (G := G) v₀ w₀ hadj).1.1 = w₀ ∨ (edge0 (G := G) v₀ w₀ hadj).1.2 = w₀) :
    edgeScalarUnit (G := G) s w₀ ⟨edge0 (G := G) v₀ w₀ hadj, hinc⟩ = (t v₀)⁻¹ := by
  have hne : v₀ ≠ w₀ := G.ne_of_adj hadj
  rw [edgeScalarUnit, hs0]
  change (if (edge0 (G := G) v₀ w₀ hadj).1.1 = w₀ then _ else _) = (t v₀)⁻¹
  rcases lt_or_gt_of_ne hne with h | h
  · have hl : ¬ (edge0 (G := G) v₀ w₀ hadj).1.1 = w₀ := by
      change ¬ min v₀ w₀ = w₀; rw [min_eq_left h.le]; exact ne_of_lt h
    rw [if_neg hl, if_pos h]
  · have hl : (edge0 (G := G) v₀ w₀ hadj).1.1 = w₀ := by
      change min v₀ w₀ = w₀; exact min_eq_right h.le
    rw [if_pos hl, if_neg (not_lt.mpr h.le)]

/-! ### Existence: solving the oriented incidence equation -/

/-- **Existence of edge scalars**, by induction on the number of vertices. On a
connected graph, any vertex-scalar family with product `1` is the oriented
incidence product of an edge-scalar family. -/
theorem exists_edgeScalars_aux : ∀ (n : ℕ),
    ∀ {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → G.Connected → ∀ (t : V → ℂˣ), (∏ v, t v) = 1 →
    ∃ s : Edge G → ℂˣ, ∀ v : V, orientedIncidence (G := G) s v = t v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ G _ hcard hconn t ht
    rcases Nat.lt_or_ge (Fintype.card V) 2 with hlt | hge
    · -- At most one vertex: there are no edges, and `∏ t = 1` forces `t v = 1`.
      refine ⟨fun _ => 1, fun v => ?_⟩
      have hsub : Subsingleton V := by
        rw [← Fintype.card_le_one_iff_subsingleton]; omega
      have hempty : IsEmpty (IncidentEdge G v) :=
        ⟨fun ie => absurd (Subsingleton.elim ie.1.1.1 ie.1.1.2) (ne_of_lt ie.1.2.1)⟩
      rw [orientedIncidence, Finset.prod_of_isEmpty]
      have hsingle : (∏ w, t w) = t v := by
        refine Finset.prod_eq_single v (fun b _ hb => absurd (Subsingleton.elim b v) hb)
          (fun hb => absurd (Finset.mem_univ v) hb)
      rw [← hsingle, ht]
    · -- Remove a vertex `v₀` whose deletion keeps the graph connected.
      have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v₀, hG'conn⟩ :=
        hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
      obtain ⟨w₀, hadj⟩ := hconn.preconnected.exists_adj_of_nontrivial v₀
      have hw₀ne : w₀ ≠ v₀ := (G.ne_of_adj hadj).symm
      set W₀ : (↑({v₀}ᶜ : Set V)) := ⟨w₀, by simp [hw₀ne]⟩ with hW₀
      classical
      set t' : (↑({v₀}ᶜ : Set V)) → ℂˣ :=
        fun w => if w = W₀ then t w₀ * t v₀ else t (w : V) with ht'def
      have ht'val : ∀ w, t' w = if w = W₀ then t w₀ * t v₀ else t (w : V) := fun _ => rfl
      have hprodt' : (∏ w, t' w) = 1 := by
        have stepA : (∏ w, t' w) = (∏ w : (↑({v₀}ᶜ : Set V)), t (w : V)) * t v₀ := by
          rw [← Finset.mul_prod_erase Finset.univ t' (Finset.mem_univ W₀),
              ← Finset.mul_prod_erase Finset.univ (fun w : (↑({v₀}ᶜ : Set V)) => t (w : V))
                (Finset.mem_univ W₀)]
          have hW₀val : t' W₀ = t (W₀ : V) * t v₀ := by rw [ht'val, if_pos rfl, hW₀]
          have herase : (∏ w ∈ Finset.univ.erase W₀, t' w)
              = ∏ w ∈ Finset.univ.erase W₀, t (w : V) :=
            Finset.prod_congr rfl fun w hw => by
              rw [ht'val, if_neg (Finset.ne_of_mem_erase hw)]
          rw [hW₀val, herase, mul_assoc, mul_comm (t v₀), ← mul_assoc]
        rw [stepA]
        have stepB : (∏ w : (↑({v₀}ᶜ : Set V)), t (w : V))
            = ∏ v ∈ Finset.univ.erase v₀, t v := by
          rw [← Finset.prod_subtype (Finset.univ.erase v₀)
            (p := fun v => v ∈ ({v₀}ᶜ : Set V)) (by intro x; simp) t]
        rw [stepB, mul_comm, Finset.mul_prod_erase Finset.univ t (Finset.mem_univ v₀), ht]
      have hcard' : Fintype.card (↑({v₀}ᶜ : Set V)) < n := by
        rw [← hcard, Fintype.card_compl_set]
        simp only [Set.card_singleton]
        exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨v₀⟩) one_pos
      obtain ⟨s', hs'⟩ :=
        ih _ hcard' (G.induce ({v₀}ᶜ : Set V)) rfl hG'conn t' hprodt'
      -- Assemble the edge-scalar family on `G`.
      set s : Edge G → ℂˣ := fun e =>
        if h : e.1.1 ≠ v₀ ∧ e.1.2 ≠ v₀ then s' (restrictEdge (G := G) v₀ e h.1 h.2)
        else if e.1 = (min v₀ w₀, max v₀ w₀) then (if v₀ < w₀ then t v₀ else (t v₀)⁻¹)
        else 1 with hsdef
      -- `s` agrees with `s'` on lifted edges.
      have hs_lift : ∀ e' : Edge (G.induce ({v₀}ᶜ : Set V)),
          s (liftEdge (G := G) v₀ e') = s' e' := by
        intro e'
        have h1 : (liftEdge (G := G) v₀ e').1.1 ≠ v₀ := liftEdge_ne_fst (G := G) v₀ e'
        have h2 : (liftEdge (G := G) v₀ e').1.2 ≠ v₀ := liftEdge_ne_snd (G := G) v₀ e'
        rw [hsdef]; simp only []; rw [dif_pos ⟨h1, h2⟩]; congr 1
      -- `s` is `1` on every `v₀`-incident edge other than `{v₀, w₀}`.
      have hs_one : ∀ e : Edge G, v0Inc (G := G) v₀ e →
          e.1 ≠ (min v₀ w₀, max v₀ w₀) → s e = 1 := by
        intro e hv0 hne
        rw [hsdef]; simp only []
        rw [dif_neg (by rintro ⟨ha, hb⟩; rcases hv0 with h | h; exacts [ha h, hb h]),
          if_neg hne]
      -- `s` on the chosen edge.
      have hs0 : s (edge0 (G := G) v₀ w₀ hadj)
          = (if v₀ < w₀ then t v₀ else (t v₀)⁻¹) := by
        rw [hsdef]; simp only []
        rw [dif_neg (by
          rintro ⟨ha, hb⟩
          rcases edge0_v0Inc (G := G) v₀ w₀ hadj with h | h
          exacts [ha h, hb h]),
          if_pos (show (edge0 (G := G) v₀ w₀ hadj).1 = (min v₀ w₀, max v₀ w₀) from rfl)]
      refine ⟨s, fun v => ?_⟩
      by_cases hv : v = v₀
      · -- The chosen vertex `v₀`.
        subst hv
        rw [orientedIncidence_v0 (G := G) v w₀ hadj s hs_one,
          unit_at_v0 (G := G) v w₀ hadj t s hs0 (edge0_inc_v0 (G := G) v w₀ hadj)]
      · -- A vertex of the deleted subgraph.
        set w : (↑({v₀}ᶜ : Set V)) := ⟨v, by simp [hv]⟩ with hwdef
        rw [orientedIncidence_split (G := G) v₀ s v]
        rw [prod_free_eq (G := G) v₀ w s s' hs_lift, hs' w]
        by_cases hvw₀ : v = w₀
        · -- `v = w₀`: the `v₀`-incident part contributes `(t v₀)⁻¹`, folded into `t' W₀`.
          have hwW₀ : w = W₀ := by rw [hwdef, hW₀]; exact Subtype.ext hvw₀
          have hvinc : v0Inc (G := G) v₀ (edge0 (G := G) v₀ w₀ hadj) :=
            edge0_v0Inc (G := G) v₀ w₀ hadj
          have hsplit := v0Inc_prod_w0 (G := G) v₀ w₀ hadj hw₀ne s
          rw [hvw₀] at *
          rw [hsplit, unit_at_w0 (G := G) v₀ w₀ hadj t s hs0 (edge0_inc_w0 (G := G) v₀ w₀ hadj)]
          rw [ht'val, if_pos hwW₀]
          rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]
        · rw [v0Inc_prod_ne (G := G) v₀ w₀ v hv hvw₀ s hs_one, one_mul]
          rw [ht'val, if_neg (by rw [hwdef]; intro hc; exact hvw₀ (congrArg Subtype.val hc))]

/-- **Edge-scalar solve on a connected graph.** For a connected simple graph and
any vertex-scalar family `t : V → ℂˣ` whose product over all vertices is `1`,
there is an edge-scalar family `s : Edge G → ℂˣ` whose oriented incidence product
at every vertex `v` equals `t v`.

This is the spanning-tree coboundary step of the absorption argument in the
Fundamental Theorem for injective PEPS (arXiv:1804.04964, Section 3), recorded in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`. Together with
`prod_orientedIncidence_eq_one` it shows that, on a connected graph, the
product-one condition is exactly the solvability criterion. -/
theorem exists_edgeScalars_of_connected (hconn : G.Connected)
    (t : V → ℂˣ) (ht : (∏ v, t v) = 1) :
    ∃ s : Edge G → ℂˣ, ∀ v : V, orientedIncidence (G := G) s v = t v :=
  exists_edgeScalars_aux (Fintype.card V) G rfl hconn t ht

end PEPS
end TNLean
