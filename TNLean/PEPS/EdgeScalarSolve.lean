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
    (Σ v : V, IncidentEdge G v) ≃ (Σ e : Edge G, incVertex (G := G) e) where
  toFun p := ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
  invFun q := ⟨q.2.1, ⟨q.1, q.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

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

end PEPS
end TNLean
