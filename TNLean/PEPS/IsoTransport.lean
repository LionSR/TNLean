import Mathlib.Combinatorics.SimpleGraph.Maps

import TNLean.PEPS.Defs

/-!
# Transport of PEPS tensors along a graph isomorphism

A graph isomorphism `φ : G ≃g G'` carries the combinatorial data of a PEPS on `G`
to a PEPS on `G'`: each edge maps to an edge (`Edge.map`), each edge incident to
`v` maps to an edge incident to `φ v` (`IncidentEdge.equiv`), and a tensor `A` on
`G` transports to a tensor `A.transport φ` on `G'` whose bond dimensions and
components are those of `A` reindexed by `φ` (`Tensor.transport`). Transport
turns the state coefficient into the precomposed coefficient
(`stateCoeff_transport`), so it preserves `SameState`.

This is the geometric input to translation invariance: a tensor on the torus is
translation invariant when it is fixed by the transport along every translation
automorphism (`TNLean/PEPS/TorusTranslationInvariant.lean`). Here the
construction is stated for a general isomorphism so the edge action, the
incident-edge correspondence, and the coefficient identity are available once and
specialized to the torus translations.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W} {d : ℕ}

/-! ### The edge action of a graph isomorphism -/

omit [Fintype V] [Fintype W] in
/-- The image edge `Edge.ofAdj h` is independent of the incidence direction of the
adjacency `h`: orienting the pair `(u, v)` and the pair `(v, u)` gives the same
edge, since `Edge.ofAdj` places the smaller endpoint first either way. -/
theorem Edge.ofAdj_symm {u v : V} (h : G.Adj u v) :
    Edge.ofAdj h = Edge.ofAdj h.symm := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with huv | hvu
  · rw [Edge.ofAdj_of_lt h huv, Edge.ofAdj_of_gt h.symm huv]
  · rw [Edge.ofAdj_of_gt h hvu, Edge.ofAdj_of_lt h.symm hvu]

omit [Fintype V] [Fintype W] in
/-- An edge is determined by its unordered endpoint pair: if `(u, v)` is, in some
order, the ordered endpoint pair of `e`, then orienting `(u, v)` with `Edge.ofAdj`
recovers `e`.  This is the bookkeeping that makes the edge action of an
isomorphism well defined regardless of which order the isomorphism produces. -/
theorem Edge.ofAdj_eq_of_endpoints {u v : V} (h : G.Adj u v) (e : Edge G)
    (H : (u = e.1.1 ∧ v = e.1.2) ∨ (u = e.1.2 ∧ v = e.1.1)) :
    Edge.ofAdj h = e := by
  apply Subtype.ext
  rcases Edge.ofAdj_endpoints h with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;>
    rcases H with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Prod.ext (o1.trans hu) (o2.trans hv)
  · exfalso
    have hlt : (Edge.ofAdj h).1.1 < (Edge.ofAdj h).1.2 := (Edge.ofAdj h).2.1
    rw [o1, o2, hu, hv] at hlt
    exact absurd hlt (not_lt.mpr e.2.1.le)
  · exfalso
    have hlt : (Edge.ofAdj h).1.1 < (Edge.ofAdj h).1.2 := (Edge.ofAdj h).2.1
    rw [o1, o2, hu, hv] at hlt
    exact absurd hlt (not_lt.mpr e.2.1.le)
  · exact Prod.ext (o1.trans hv) (o2.trans hu)

omit [Fintype V] in
/-- Two `Edge.ofAdj` constructions agree when their adjacent pairs have the same
unordered endpoints: orienting `(u, v)` and `(u', v')` gives the same edge whenever
`{u, v} = {u', v'}`. -/
theorem Edge.ofAdj_eq_ofAdj {u v u' v' : V} (h1 : G.Adj u v) (h2 : G.Adj u' v')
    (H : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')) :
    Edge.ofAdj h1 = Edge.ofAdj h2 := by
  rw [Edge.ofAdj_eq_of_endpoints h1 (Edge.ofAdj h2)]
  rcases Edge.ofAdj_endpoints h2 with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;> rw [o1, o2] <;> tauto

/-- The edge of `G'` obtained by pushing an edge of `G` through the graph
isomorphism `φ`: apply `φ` to both endpoints and reorder them into the `Edge`
convention with `Edge.ofAdj`.  The isomorphism may swap the order of the two
endpoints, which `Edge.ofAdj` corrects. -/
def Edge.map (φ : G ≃g G') (e : Edge G) : Edge G' :=
  Edge.ofAdj ((φ.map_rel_iff').mpr e.2.2)

omit [Fintype V] [Fintype W] in
/-- The unordered endpoints of `Edge.map φ e` are the `φ`-images of the endpoints
of `e`. -/
theorem Edge.map_endpoints (φ : G ≃g G') (e : Edge G) :
    ((Edge.map φ e).1.1 = φ e.1.1 ∧ (Edge.map φ e).1.2 = φ e.1.2) ∨
      ((Edge.map φ e).1.1 = φ e.1.2 ∧ (Edge.map φ e).1.2 = φ e.1.1) :=
  Edge.ofAdj_endpoints ((φ.map_rel_iff').mpr e.2.2)

omit [Fintype V] [Fintype W] in
/-- Pushing an edge through `φ` and then through `φ.symm` recovers the original
edge.  The two passes return to the original unordered endpoint pair, and
`Edge.ofAdj` re-imposes the same `<`-order, so the round trip is the identity. -/
@[simp] theorem Edge.map_symm_map (φ : G ≃g G') (e : Edge G) :
    Edge.map φ.symm (Edge.map φ e) = e := by
  apply Edge.ofAdj_eq_of_endpoints
  rcases Edge.map_endpoints φ e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · exact Or.inr ⟨by rw [h1]; simp, by rw [h2]; simp⟩

omit [Fintype V] [Fintype W] in
/-- Pushing an edge through `φ.symm` and then through `φ` recovers it. -/
@[simp] theorem Edge.map_map_symm (φ : G ≃g G') (e : Edge G') :
    Edge.map φ (Edge.map φ.symm e) = e :=
  Edge.map_symm_map φ.symm e

/-- The edge action of `φ` as a bijection `Edge G ≃ Edge G'`. -/
def Edge.equiv (φ : G ≃g G') : Edge G ≃ Edge G' where
  toFun := Edge.map φ
  invFun := Edge.map φ.symm
  left_inv := Edge.map_symm_map φ
  right_inv := Edge.map_map_symm φ

omit [Fintype V] [Fintype W] in
@[simp] theorem Edge.equiv_apply (φ : G ≃g G') (e : Edge G) :
    Edge.equiv φ e = Edge.map φ e :=
  rfl

omit [Fintype V] [Fintype W] in
@[simp] theorem Edge.equiv_symm_apply (φ : G ≃g G') (e : Edge G') :
    (Edge.equiv φ).symm e = Edge.map φ.symm e :=
  rfl

/-! ### The incident-edge correspondence -/

omit [Fintype V] [Fintype W] in
/-- An edge incident to `v` maps, under `φ`, to an edge incident to `φ v`. -/
theorem Edge.map_incident (φ : G ≃g G') {v : V} {e : Edge G}
    (h : e.1.1 = v ∨ e.1.2 = v) :
    (Edge.map φ e).1.1 = φ v ∨ (Edge.map φ e).1.2 = φ v := by
  rcases Edge.map_endpoints φ e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h with hv | hv
    · exact Or.inl (by rw [h1, hv])
    · exact Or.inr (by rw [h2, hv])
  · rcases h with hv | hv
    · exact Or.inr (by rw [h2, hv])
    · exact Or.inl (by rw [h1, hv])

/-- The correspondence between edges incident to `v` and edges incident to `φ v`,
as a bijection.  The underlying map is the edge action `Edge.map φ`; the incidence
is preserved because `φ` sends the endpoint equal to `v` to one equal to `φ v`. -/
def IncidentEdge.equiv (φ : G ≃g G') (v : V) :
    IncidentEdge G v ≃ IncidentEdge G' (φ v) where
  toFun ie := ⟨Edge.map φ ie.1, Edge.map_incident φ ie.2⟩
  invFun ie := ⟨Edge.map φ.symm ie.1, by
    have h := Edge.map_incident φ.symm (v := φ v) ie.2
    simpa using h⟩
  left_inv ie := by apply Subtype.ext; simp
  right_inv ie := by apply Subtype.ext; simp

omit [Fintype V] [Fintype W] in
@[simp] theorem IncidentEdge.equiv_coe (φ : G ≃g G') (v : V)
    (ie : IncidentEdge G v) :
    (IncidentEdge.equiv φ v ie).1 = Edge.map φ ie.1 :=
  rfl

/-- The edge incident to `φ.symm w` carried to an edge incident to `w` (not merely
to `φ (φ.symm w)`).  The membership at `w` is recomputed from `Edge.map_incident`
through `φ (φ.symm w) = w`, avoiding a transport across the incidence-vertex index.
This is the form consumed in the transported tensor's component, where the vertex
of `G'` is `w` and its `G`-preimage is `φ.symm w`. -/
def IncidentEdge.toSymm (φ : G ≃g G') (w : W) (ie : IncidentEdge G (φ.symm w)) :
    IncidentEdge G' w :=
  ⟨Edge.map φ ie.1, by
    have h := Edge.map_incident φ ie.2
    rwa [φ.apply_symm_apply] at h⟩

omit [Fintype V] [Fintype W] in
@[simp] theorem IncidentEdge.toSymm_coe (φ : G ≃g G') (w : W)
    (ie : IncidentEdge G (φ.symm w)) :
    (IncidentEdge.toSymm φ w ie).1 = Edge.map φ ie.1 :=
  rfl

/-! ### Transport of a tensor along a graph isomorphism -/

variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- Transport of a PEPS tensor along the graph isomorphism `φ : G ≃g G'`.  Its bond
dimension at an edge `e'` of `G'` is the bond dimension of `A` at the preimage edge
`Edge.map φ.symm e'`, and its component at a vertex `w` is the component of `A` at
`φ.symm w`, with the incident virtual indices supplied through the edge action.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`, where the translationally invariant theorem
places one tensor at every site, i.e. the tensor is fixed by transport along every
translation. -/
noncomputable def Tensor.transport (A : Tensor G d) (φ : G ≃g G') : Tensor G' d where
  bondDim e' := A.bondDim (Edge.map φ.symm e')
  component w η' p :=
    A.component (φ.symm w)
      (fun ie : IncidentEdge G (φ.symm w) =>
        finCongr
          (show A.bondDim (Edge.map φ.symm (IncidentEdge.toSymm φ w ie).1) = A.bondDim ie.1 by
            simp only [IncidentEdge.toSymm_coe, Edge.map_symm_map])
          (η' (IncidentEdge.toSymm φ w ie))) p

omit [Fintype V] [Fintype W] in
@[simp] theorem Tensor.transport_bondDim (A : Tensor G d) (φ : G ≃g G') (e' : Edge G') :
    (A.transport φ).bondDim e' = A.bondDim (Edge.map φ.symm e') :=
  rfl

/-- The virtual configurations of `A.transport φ` correspond to those of `A` by the
edge action of `φ`: a configuration on the edges of `G'` is the same data as a
configuration on the edges of `G`, since the edges and their bond dimensions are
carried across by `φ`.  Concretely `(vcEquiv A φ).symm η e' = η (Edge.map φ.symm e')`. -/
noncomputable def vcEquiv (A : Tensor G d) (φ : G ≃g G') :
    VirtualConfig (A.transport φ) ≃ VirtualConfig A :=
  Equiv.piCongrLeft (fun e : Edge G => Fin (A.bondDim e)) (Edge.equiv φ.symm)

omit [Fintype V] [Fintype W] in
@[simp] theorem vcEquiv_symm_apply (A : Tensor G d) (φ : G ≃g G')
    (η : VirtualConfig A) (e' : Edge G') :
    (vcEquiv A φ).symm η e' = η (Edge.map φ.symm e') :=
  Equiv.piCongrLeft_symm_apply (fun e : Edge G => Fin (A.bondDim e)) (Edge.equiv φ.symm) η e'

omit [Fintype V] [Fintype W] in
/-- The virtual index that the transported configuration `(vcEquiv A φ).symm η`
supplies on the edge `e'` over `e0 := Edge.map φ.symm e'` is, up to the bond-dimension
reindexing, the original index `η e0`.  This is the bond-level content of the edge
action: pushing a configuration forward and reading it back recovers the original
indices.  It is the per-edge identity behind `stateCoeff_transport`. -/
theorem finCongr_vcEquiv_symm (A : Tensor G d) (φ : G ≃g G') (η : VirtualConfig A)
    (e' : Edge G') (e0 : Edge G) (he : Edge.map φ.symm e' = e0)
    (h : A.bondDim (Edge.map φ.symm e') = A.bondDim e0) :
    finCongr h (((vcEquiv A φ).symm η) e') = η e0 := by
  subst he
  rw [vcEquiv_symm_apply]
  simp

/-! ### The state coefficient of a transported tensor -/

omit [Fintype V] [Fintype W] in
/-- The component of `A.transport φ` at a vertex `w`, evaluated on the virtual
indices coming from `(vcEquiv A φ).symm η`, equals the component of `A` at the
preimage vertex `φ.symm w` evaluated on `η`.  This is the per-vertex matching used
in `stateCoeff_transport`. -/
theorem transport_component_vcEquiv (A : Tensor G d) (φ : G ≃g G') (η : VirtualConfig A)
    (σ : W → Fin d) (w : W) :
    (A.transport φ).component w (fun ie' : IncidentEdge G' w => ((vcEquiv A φ).symm η) ie'.1)
        (σ w)
      = A.component (φ.symm w) (fun ie => η ie.1) (σ w) := by
  change A.component (φ.symm w)
      (fun ie : IncidentEdge G (φ.symm w) =>
        finCongr _ (((vcEquiv A φ).symm η) (IncidentEdge.toSymm φ w ie).1)) (σ w)
    = A.component (φ.symm w) (fun ie => η ie.1) (σ w)
  congr 1
  funext ie
  exact finCongr_vcEquiv_symm A φ η (IncidentEdge.toSymm φ w ie).1 ie.1 (by
    rw [IncidentEdge.toSymm_coe, Edge.map_symm_map]) _

/-- **Transport of the state coefficient.**

The state coefficient of the transported tensor `A.transport φ` at a physical
configuration `σ` on the vertices of `G'` equals the state coefficient of `A` at
the precomposed configuration `σ ∘ φ` on the vertices of `G`.  Transport reindexes
the virtual configurations by the edge action and the vertices by `φ`, leaving the
contracted coefficient unchanged up to this relabelling.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem stateCoeff_transport (A : Tensor G d) (φ : G ≃g G') (σ : W → Fin d) :
    stateCoeff (A.transport φ) σ = stateCoeff A (fun v => σ (φ v)) := by
  unfold stateCoeff
  rw [← Equiv.sum_comp (vcEquiv A φ).symm
        (fun η' => ∏ w : W, (A.transport φ).component w (fun ie => η' ie.1) (σ w))]
  apply Finset.sum_congr rfl
  intro η _
  simp only
  rw [Finset.prod_congr rfl (fun w _ => transport_component_vcEquiv A φ η σ w)]
  rw [← Equiv.prod_comp φ.toEquiv (fun w => A.component (φ.symm w) (fun ie => η ie.1) (σ w))]
  apply Finset.prod_congr rfl
  intro v _
  simp only [RelIso.coe_fn_toEquiv]
  rw [φ.symm_apply_apply]

/-- Transport preserves `SameState`: if `A` and `B` agree on all state
coefficients, so do `A.transport φ` and `B.transport φ`.  Each side's coefficient
is the corresponding coefficient of `A` (respectively `B`) at the precomposed
configuration, which agree by hypothesis.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem SameState.transport {A B : Tensor G d} (φ : G ≃g G') (h : SameState A B) :
    SameState (A.transport φ) (B.transport φ) := by
  intro σ
  rw [stateCoeff_transport, stateCoeff_transport]
  exact h _

end PEPS
end TNLean
