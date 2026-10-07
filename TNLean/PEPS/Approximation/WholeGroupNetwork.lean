/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GroupTruncation
import TNLean.PEPS.DependentBondNetwork

/-!
# Whole-group contractions as edge-dependent networks

The whole-group tensor bound is stated for vertex tensors with one leg per incident edge,
contracted by the coordinate pairing. The edge-dependent networks of
`TNLean.PEPS.DependentBondNetwork` instead give each vertex one leg per endpoint incidence and
insert a matrix on every edge. With identity edge matrices the two contractions agree; without
edges from a vertex to itself, the endpoint incidences at a vertex are exactly its incident edges,
so the vertex norms agree as well. Hence the whole-group tensor bound applies verbatim to
edge-dependent networks with identity edge matrices.

## Main definitions

* `WholeGroup.ofLocalTensors`: the vertex tensors read off from edge-dependent network tensors.
* `WholeGroup.localConfigEquiv`: without self-edges, local endpoint configurations are
  configurations of the incident edges.

## Main statements

* `WholeGroup.network_one_eq_contraction`: the network with identity edge matrices is the
  coordinate contraction.
* `WholeGroup.network_norm_le_one`, `WholeGroup.nuclearNorm_flattening_network_le_one`,
  `WholeGroup.exists_simultaneous_network_truncation`: Lemma 6.2 of the polynomial-PEPS
  manuscript for edge-dependent networks.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`,
  05-frames.tex:125–141.
-/

open scoped BigOperators Matrix InnerProductSpace

noncomputable section

namespace TNLean.PEPS.WholeGroup

open DependentBondNetwork Matrix

variable {V E : Type*} {tail head : E → V} {D : E → Type*} {P : V → Type*}

/-- The edge of an endpoint incidence at `v` is incident to `v`. -/
theorem isIncident_of_incidentEndpoint {v : V} (q : IncidentEndpoint tail head v) :
    IsIncident tail head v q.1.1 := by
  obtain ⟨⟨e, b⟩, hq⟩ := q
  cases b
  · exact Or.inl (by simpa [endpointVertex] using hq)
  · exact Or.inr (by simpa [endpointVertex] using hq)

variable (D) in
/-- The local endpoint configuration at `v` that reads each endpoint label from its edge. -/
def localConfigOfIncident (v : V) (x : (e : {e // IsIncident tail head v e}) → D e) :
    LocalConfig tail head D v :=
  fun q ↦ x ⟨q.1.1, isIncident_of_incidentEndpoint q⟩

/-- The vertex tensors of an edge-dependent network tensor: each endpoint leg reads the label of
its edge. -/
def ofLocalTensors (A : (v : V) → LocalConfig tail head D v → P v → ℂ) :
    VertexTensors tail head D P :=
  fun v x p ↦ A v (localConfigOfIncident D v x) p

variable [DecidableEq V]

variable (D) in
/-- Without edges from a vertex to itself, the endpoint incidences at `v` are exactly the edges
incident to `v`, so local endpoint configurations are configurations of the incident edges. -/
def localConfigEquiv (hloop : ∀ e, tail e ≠ head e) (v : V) :
    ((e : {e // IsIncident tail head v e}) → D e) ≃ LocalConfig tail head D v where
  toFun := localConfigOfIncident D v
  invFun η e := η ⟨(e.1, decide (head e.1 = v)), by
    rcases e.2 with h | h <;> by_cases hh : head e.1 = v <;> simp [endpointVertex, hh, h]⟩
  left_inv _ := rfl
  right_inv η := by
    funext ⟨⟨e, b⟩, hq⟩
    have hb : decide (head e = v) = b := by
      cases b
      · have hq' : tail e = v := by simpa [endpointVertex] using hq
        simpa using fun h : head e = v ↦ hloop e (hq'.trans h.symm)
      · simpa [endpointVertex] using hq
    subst hb
    rfl

omit [DecidableEq V] in
/-- With identity edge matrices, the edge-dependent network is the coordinate contraction of the
vertex tensors that read each endpoint label from its edge. No hypothesis on self-edges is
needed. -/
theorem network_one_eq_contraction [Fintype V] [Fintype E] [DecidableEq E] [∀ e, Fintype (D e)]
    [∀ e, DecidableEq (D e)] (A : (v : V) → LocalConfig tail head D v → P v → ℂ)
    (σ : (v : V) → P v) :
    network tail head D A (fun _ ↦ 1) σ = contraction (ofLocalTensors A) σ := by
  classical
  unfold network contraction
  symm
  refine Fintype.sum_of_injective (fun (γ : (e : E) → D e) (p : Endpoint E) ↦ γ p.1)
    (fun γ γ' h ↦ funext fun e ↦ congrFun h (e, true)) _ _ (fun β hβ ↦ ?_) (fun γ ↦ ?_)
  · obtain ⟨e, he⟩ : ∃ e, β (e, true) ≠ β (e, false) := by
      by_contra h
      push Not at h
      exact hβ ⟨fun e ↦ β (e, true), funext fun ⟨e, b⟩ ↦ by cases b <;> simp [h e]⟩
    have h0 : bondWeight D (fun e ↦ (1 : Matrix (D e) (D e) ℂ)) β = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (Matrix.one_apply_ne he)
    rw [h0, zero_mul]
  · have h1 : bondWeight D (fun e ↦ (1 : Matrix (D e) (D e) ℂ)) (fun p ↦ γ p.1) = 1 :=
      Finset.prod_eq_one fun e _ ↦ Matrix.one_apply_eq (γ e)
    rw [h1, one_mul]
    rfl

/-- Without edges from a vertex to itself, the vertex norms of the two descriptions agree. -/
theorem vertexNormSq_ofLocalTensors [Fintype E] [DecidableEq E] [∀ e, Fintype (D e)]
    [∀ v, Fintype (P v)]
    (hloop : ∀ e, tail e ≠ head e) (A : (v : V) → LocalConfig tail head D v → P v → ℂ) (v : V) :
    vertexNormSq (ofLocalTensors A) v = ∑ η, ∑ p, ‖A v η p‖ ^ 2 :=
  (localConfigEquiv D hloop v).sum_comp fun η ↦ ∑ p, ‖A v η p‖ ^ 2

section Network

variable [Fintype V] [Fintype E] [DecidableEq E] [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ v, Fintype (P v)] (A : (v : V) → LocalConfig tail head D v → P v → ℂ)

/-- **Whole-group tensor bound, norm part, for edge-dependent networks.** A network with
identity edge matrices, no edges from a vertex to itself, and vertex tensors of norm at most one
has norm at most one.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, 05-frames.tex:125–131.
-/
theorem network_norm_le_one (hloop : ∀ e, tail e ≠ head e)
    (hA : ∀ v, ∑ η, ∑ p, ‖A v η p‖ ^ 2 ≤ 1) :
    ‖(WithLp.toLp 2 (network tail head D A (fun _ ↦ 1)) :
        EuclideanSpace ℂ ((v : V) → P v))‖ ≤ 1 := by
  rw [show network tail head D A (fun _ ↦ 1) = contraction (ofLocalTensors A) from
    funext (network_one_eq_contraction A)]
  exact contraction_norm_le_one _ hloop fun v ↦ (vertexNormSq_ofLocalTensors hloop A v).trans_le
    (hA v)

/-- **Whole-group tensor bound, nuclear part, for edge-dependent networks.** Across every
bipartition into whole open-leg groups, a network with identity edge matrices, no edges from a
vertex to itself, and vertex tensors of norm at most one has nuclear norm at most one.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, 05-frames.tex:125–131.
-/
theorem nuclearNorm_flattening_network_le_one [∀ v, DecidableEq (P v)]
    (hloop : ∀ e, tail e ≠ head e) (hA : ∀ v, ∑ η, ∑ p, ‖A v η p‖ ^ 2 ≤ 1) (T : Finset V) :
    Matrix.nuclearNorm (flattening (network tail head D A (fun _ ↦ 1)) T) ≤ 1 := by
  rw [show network tail head D A (fun _ ↦ 1) = contraction (ofLocalTensors A) from
    funext (network_one_eq_contraction A)]
  exact nuclearNorm_flattening_le_one _ hloop
    (fun v ↦ (vertexNormSq_ofLocalTensors hloop A v).trans_le (hA v)) T

/-- **Whole-group tensor bound, truncation part, for edge-dependent networks.** For a network
with identity edge matrices, no edges from a vertex to itself, and vertex tensors of norm at most
one, and for a finite set `G` of vertices containing every group with more than one
configuration, there are orthonormal families of at most `k` vectors per group whose
tensor-product projection sends `Z` to `Z_k` with `‖Z - Z_k‖ ≤ |G| / √k`, and `Z_k` has at most
`k ^ |G|` product terms with coefficients of modulus at most one.

Polynomial-PEPS manuscript (Sept 24 2026), Lemma 6.2 `lem:group-tensor`, 05-frames.tex:133–141.
-/
theorem exists_simultaneous_network_truncation [∀ v, DecidableEq (P v)]
    (hloop : ∀ e, tail e ≠ head e) (hA : ∀ v, ∑ η, ∑ p, ‖A v η p‖ ^ 2 ≤ 1) (G : Finset V)
    (hG : ∀ v ∉ G, Fintype.card (P v) ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (r : V → ℕ) (e : (v : V) → Fin (r v) → EuclideanSpace ℂ (P v)),
      (∀ v, r v ≤ k) ∧ (∀ v, Orthonormal ℂ (e v)) ∧
      ‖WithLp.toLp 2 (network tail head D A (fun _ ↦ 1)) -
          toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v))
            (WithLp.toLp 2 (network tail head D A (fun _ ↦ 1)))‖ ≤ G.card / √k ∧
      Fintype.card ((v : V) → Fin (r v)) ≤ k ^ G.card ∧
      ∃ c : ((v : V) → Fin (r v)) → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
        toEuclideanLin (factorMatrix fun v ↦ orthonormalProjector (e v))
            (WithLp.toLp 2 (network tail head D A (fun _ ↦ 1))) =
          ∑ i, c i • productVector e i := by
  rw [show network tail head D A (fun _ ↦ 1) = contraction (ofLocalTensors A) from
    funext (network_one_eq_contraction A)]
  exact exists_simultaneous_group_truncation _ hloop
    (fun v ↦ (vertexNormSq_ofLocalTensors hloop A v).trans_le (hA v)) G hG k hk

end Network

end TNLean.PEPS.WholeGroup
