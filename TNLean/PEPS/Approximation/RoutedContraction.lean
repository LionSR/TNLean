/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Routing a party network through a graph

A *party network* is a finite tensor network whose nodes, the parties, are joined by
links carrying finite virtual alphabets. Every party has one tensor, which reads the
labels of its incident links and one physical index. Placing every party at a vertex of
a finite simple graph `G` and routing every link along a walk of `G` from the vertex of
its first party to the vertex of its second turns the network into a PEPS on `G`:

* every step of a routed walk carries an identity tensor on the virtual index of its link,
  so the walk transports one link label;
* at a vertex, the indices of all walks passing through it are kept independently
  (crossings are permitted), and the party tensors located there are multiplied;
* all walk steps traversing one graph edge are grouped into one product alphabet.

Zero-length links (both parties at the same vertex) and several parties at one vertex are
contracted inside the vertex tensor. The resulting PEPS has exactly the coefficients of the
party network, and an edge traversed `m` times by links of dimension at most `D` has bond
dimension at most `D ^ m`.

No injectivity, isometry, translation-invariance, or uniform-dimension assumption is made.

## Main results

* `TNLean.PEPS.Approximation.Routing.toTensor_stateCoeff`: the routed PEPS has the
  coefficients of the party network.
* `TNLean.PEPS.Approximation.Routing.toTensor_bondDim_le`: the bond dimension of an edge
  traversed `m` times is at most `D ^ m`.
* `TNLean.PEPS.Approximation.Routing.exists_tensor_of_congestion_le`: a routing with
  congestion at most `χ` of links of dimension at most `D` yields a PEPS with the same
  coefficients and every bond dimension at most `D ^ χ`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.3, the paragraph following Lemma 8.2
  `lem:routing` and equation `eq:final-bond`, `07-assembly.tex:164–177`.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- The links incident to a party `p`: those having `p` as first or second endpoint.
A link joining `p` to itself occurs once. -/
abbrev IncidentLink {P Λ : Type*} (src tgt : Λ → P) (p : P) : Type _ :=
  {ℓ : Λ // src ℓ = p ∨ tgt ℓ = p}

/-- A finite party network with physical alphabet `Fin d`.

Every link `ℓ` joins the parties `src ℓ` and `tgt ℓ` and carries the virtual alphabet
`Fin (dim ℓ)`; the orientation is arbitrary bookkeeping. Every party tensor reads the labels
of its incident links and one physical index.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, the ket network on the party graph
obtained from Lemma 8.1 `lem:columns`, `07-assembly.tex:56–99`. -/
structure PartyNetwork (P Λ : Type*) (d : ℕ) where
  /-- The dimension of the virtual alphabet of a link. -/
  dim : Λ → ℕ
  /-- The first endpoint party of a link. -/
  src : Λ → P
  /-- The second endpoint party of a link. -/
  tgt : Λ → P
  /-- The tensor of a party. -/
  tensor : (p : P) → ((i : IncidentLink src tgt p) → Fin (dim i.1)) → Fin d → ℂ

namespace PartyNetwork

variable {P Λ : Type*} [Fintype P] [Fintype Λ] [DecidableEq Λ] {d : ℕ}
variable {V : Type*}

/-- The coefficient of the party network when the physical index of party `p` is read at
the site `site p`: the sum over all link labellings of the product of the party tensors. -/
def coeff (N : PartyNetwork P Λ d) (site : P → V) (σ : V → Fin d) : ℂ :=
  ∑ lab : (ℓ : Λ) → Fin (N.dim ℓ), ∏ p, N.tensor p (fun i => lab i.1) (σ (site p))

end PartyNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {P Λ : Type*} [Fintype P] [Fintype Λ] [DecidableEq Λ] {d : ℕ}

/-- The step from `a` to `b` traverses the edge `e` in one of its two directions. -/
def Crosses (a b : V) (e : Edge G) : Prop :=
  (a = e.1.1 ∧ b = e.1.2) ∨ (a = e.1.2 ∧ b = e.1.1)

instance (a b : V) (e : Edge G) : Decidable (Crosses a b e) := by
  unfold Crosses; infer_instance

/-- A routing of a party network through `G`.

Party `p` sits at the vertex `site p`. Link `ℓ` is routed along the walk
`route ℓ 0, …, route ℓ (len ℓ)` of `G` from the vertex of its first party to the vertex of
its second; `len ℓ = 0` is a zero-length link.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 8.2 `lem:routing`,
`07-assembly.tex:128–161`. -/
structure Routing (G : SimpleGraph V) (N : PartyNetwork P Λ d) (site : P → V) where
  /-- The number of steps of the walk of a link. -/
  len : Λ → ℕ
  /-- The vertices of the walk of a link. -/
  route : (ℓ : Λ) → Fin (len ℓ + 1) → V
  route_zero : ∀ ℓ, route ℓ 0 = site (N.src ℓ)
  route_last : ∀ ℓ, route ℓ (Fin.last _) = site (N.tgt ℓ)
  route_adj : ∀ ℓ (i : Fin (len ℓ)), G.Adj (route ℓ i.castSucc) (route ℓ i.succ)

namespace Routing

variable {N : PartyNetwork P Λ d} {site : P → V} (R : Routing G N site)

/-- The traversals of an edge `e`: the walk steps, over all links, that traverse `e`.
Their number is the traversal multiplicity of `e`, counted with repetition. -/
abbrev Traversal (e : Edge G) : Type _ :=
  {t : Σ ℓ : Λ, Fin (R.len ℓ) // Crosses (R.route t.1 t.2.castSucc) (R.route t.1 t.2.succ) e}

/-- The bond alphabet of an edge: one label of the link of every traversal. -/
abbrev BondAlphabet (e : Edge G) : Type _ :=
  (t : R.Traversal e) → Fin (N.dim t.1.1)

/-- The links whose walk visits the vertex `v`. -/
abbrev LocalLink (v : V) : Type _ := {ℓ : Λ // ∃ i, R.route ℓ i = v}

/-- An assignment of link labels at a vertex. -/
abbrev LocalLabel (v : V) : Type _ := (ℓ : R.LocalLink v) → Fin (N.dim ℓ.1)

omit [Fintype V] [DecidableRel G.Adj] [Fintype P] [Fintype Λ] [DecidableEq Λ] in
/-- The link of a traversal of an edge incident to `v` visits `v`. -/
theorem traversal_visits {v : V} (ie : IncidentEdge G v) (t : R.Traversal ie.1) :
    ∃ i, R.route t.1.1 i = v := by
  rcases t with ⟨⟨ℓ, i⟩, ht⟩
  rcases ie with ⟨e, he⟩
  simp only [Crosses] at ht
  rcases he with rfl | rfl <;> rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, h1⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, h1⟩

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] [Fintype P] [Fintype Λ]
  [DecidableEq Λ] in
/-- A link incident to a party located at `v` visits `v`. -/
theorem incident_visits {v : V} (p : {p : P // site p = v})
    (i : IncidentLink N.src N.tgt p.1) : ∃ j, R.route i.1 j = v := by
  rcases i.2 with h | h
  · exact ⟨0, by rw [R.route_zero, h, p.2]⟩
  · exact ⟨Fin.last _, by rw [R.route_last, h, p.2]⟩

/-- The identity tensors on the walks through `v` hold: every traversal of an edge at `v`
carries the label that the vertex assigns to its link. -/
def Consistent (v : V) (η : (ie : IncidentEdge G v) → R.BondAlphabet ie.1)
    (μ : R.LocalLabel v) : Prop :=
  ∀ (ie : IncidentEdge G v) (t : R.Traversal ie.1),
    η ie t = μ ⟨t.1.1, R.traversal_visits ie t⟩

open Classical in
/-- The routed vertex tensor: the identity tensors on all walks through `v`, kept
independently, times the party tensors located at `v`, with every link label visible at
`v` summed internally. Zero-length links and coincident parties are thereby contracted
locally.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:164–177`. -/
def vertexTensor (v : V) (η : (ie : IncidentEdge G v) → R.BondAlphabet ie.1) (s : Fin d) :
    ℂ :=
  ∑ μ : R.LocalLabel v,
    if R.Consistent v η μ then
      ∏ p : {p : P // site p = v}, N.tensor p.1 (fun i => μ ⟨i.1, R.incident_visits p i⟩) s
    else 0

/-- The contraction of the routed network with the grouped bond alphabets. -/
def routedCoeff (σ : V → Fin d) : ℂ :=
  ∑ η : (e : Edge G) → R.BondAlphabet e, ∏ v, R.vertexTensor v (fun ie => η ie.1) (σ v)

/-- The globally consistent configurations of edge labels and vertex-local labels. -/
abbrev ConsistentConfig : Type _ :=
  {x : ((e : Edge G) → R.BondAlphabet e) × ((v : V) → R.LocalLabel v) //
    ∀ v, R.Consistent v (fun ie => x.1 ie.1) (x.2 v)}

omit [Fintype V] [DecidableRel G.Adj] [Fintype P] [Fintype Λ] [DecidableEq Λ] in
/-- Along a walk, the identity tensors force every visited vertex to carry the label that
the first vertex assigns to the link. -/
theorem consistent_route_eq (x : R.ConsistentConfig) (ℓ : Λ) (i : Fin (R.len ℓ + 1)) :
    x.1.2 (R.route ℓ i) ⟨ℓ, i, rfl⟩ = x.1.2 (R.route ℓ 0) ⟨ℓ, 0, rfl⟩ := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hadj := R.route_adj ℓ i
    let e : Edge G := Edge.ofAdj hadj
    have hcr : Crosses (R.route ℓ i.castSucc) (R.route ℓ i.succ) e := by
      rcases Edge.ofAdj_endpoints hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    let t : R.Traversal e := ⟨⟨ℓ, i⟩, hcr⟩
    have hea : e.1.1 = R.route ℓ i.castSucc ∨ e.1.2 = R.route ℓ i.castSucc := by
      rcases hcr with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    have heb : e.1.1 = R.route ℓ i.succ ∨ e.1.2 = R.route ℓ i.succ := by
      rcases hcr with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inr h2.symm
      · exact Or.inl h2.symm
    have ha := x.2 (R.route ℓ i.castSucc) ⟨e, hea⟩ t
    have hb := x.2 (R.route ℓ i.succ) ⟨e, heb⟩ t
    exact hb.symm.trans (ha.trans ih)

omit [Fintype V] [DecidableRel G.Adj] [Fintype P] [Fintype Λ] [DecidableEq Λ] in
/-- Consistency determines every vertex-local label by the global label of its link. -/
theorem consistent_local_eq (x : R.ConsistentConfig) (v : V) (ℓ : R.LocalLink v) :
    x.1.2 v ℓ = x.1.2 (R.route ℓ.1 0) ⟨ℓ.1, 0, rfl⟩ := by
  rcases ℓ with ⟨ℓ, i, rfl⟩
  exact R.consistent_route_eq x ℓ i

omit [Fintype V] [DecidableRel G.Adj] [Fintype P] [Fintype Λ] [DecidableEq Λ] in
/-- Consistency determines every bond label by the global label of its link. -/
theorem consistent_bond_eq (x : R.ConsistentConfig) (e : Edge G) (t : R.Traversal e) :
    x.1.1 e t = x.1.2 (R.route t.1.1 0) ⟨t.1.1, 0, rfl⟩ := by
  have h := x.2 e.1.1 ⟨e, Or.inl rfl⟩ t
  exact h.trans (R.consistent_local_eq x _ _)

/-- Globally consistent configurations are exactly the link labellings of the party
network. -/
def consistentConfigEquiv : ((ℓ : Λ) → Fin (N.dim ℓ)) ≃ R.ConsistentConfig where
  toFun lab := ⟨(fun _ t => lab t.1.1, fun _ ℓ => lab ℓ.1), fun _ _ _ => rfl⟩
  invFun x ℓ := x.1.2 (R.route ℓ 0) ⟨ℓ, 0, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext e t
      exact (R.consistent_bond_eq x e t).symm
    · funext v ℓ
      exact (R.consistent_local_eq x v ℓ).symm

/-- **Exact contraction of the routed network.** Contracting the routed vertex tensors over
the grouped bond alphabets gives the coefficients of the party network.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:164–177`: “Each
continued path carries an identity tensor on its virtual index … Thus the ket network is a
PEPS on the same physical square.” -/
theorem routedCoeff_eq (σ : V → Fin d) : R.routedCoeff σ = N.coeff site σ := by
  classical
  unfold routedCoeff vertexTensor
  simp_rw [Fintype.prod_sum, Fintype.prod_ite_zero]
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => ∀ v, R.Consistent v
      (fun ie => x.1 ie.1) (x.2 v)) _ (by simp)]
  rw [← R.consistentConfigEquiv.sum_comp]
  unfold PartyNetwork.coeff
  refine Finset.sum_congr rfl fun lab _ => ?_
  rw [← Fintype.prod_fiberwise site fun p => N.tensor p (fun i => lab i.1) (σ (site p))]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun p _ => ?_
  rw [p.2]
  rfl

/-- The PEPS on `G` obtained from the routing: the bond alphabet of every edge is numbered
by `Fin`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:164–177`. -/
def toTensor : Tensor G d where
  bondDim e := Fintype.card (R.BondAlphabet e)
  component v η s := R.vertexTensor v (fun ie => (Fintype.equivFin _).symm (η ie)) s

/-- The routed PEPS has exactly the coefficients of the party network.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:164–177`. -/
theorem toTensor_stateCoeff (σ : V → Fin d) :
    stateCoeff R.toTensor σ = N.coeff site σ := by
  rw [← R.routedCoeff_eq]
  let E : ((e : Edge G) → R.BondAlphabet e) ≃ VirtualConfig R.toTensor :=
    Equiv.piCongrRight fun _ => Fintype.equivFin _
  rw [stateCoeff, ← E.sum_comp, routedCoeff]
  refine Finset.sum_congr rfl fun η _ => Finset.prod_congr rfl fun v _ => ?_
  change R.vertexTensor v (fun ie => (Fintype.equivFin _).symm (Fintype.equivFin _ (η ie.1)))
    (σ v) = _
  simp only [Equiv.symm_apply_apply]

omit [Fintype V] in
/-- The bond dimension of an edge is the product of the dimensions of the links of its
traversals. -/
theorem toTensor_bondDim (e : Edge G) :
    R.toTensor.bondDim e = ∏ t : R.Traversal e, N.dim t.1.1 := by
  simp [toTensor, Fintype.card_pi]

omit [Fintype V] in
/-- **Bond estimate.** If every link has dimension at most `D`, an edge traversed
`m` times has bond dimension at most `D ^ m`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:final-bond`,
`07-assembly.tex:166–171`. -/
theorem toTensor_bondDim_le {D : ℕ} (hdim : ∀ ℓ, N.dim ℓ ≤ D) (e : Edge G) :
    R.toTensor.bondDim e ≤ D ^ Fintype.card (R.Traversal e) := by
  rw [toTensor_bondDim]
  exact Finset.prod_le_pow_card _ _ _ fun t _ => hdim t.1.1

/-- **Routing to a PEPS.** If every link has dimension at most `D ≥ 1` and every edge is
traversed at most `χ` times, the party network is exactly a PEPS on `G` with every bond
dimension at most `D ^ χ`. Unused edges carry bond dimension one.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:final-bond` and the
following paragraph, `07-assembly.tex:164–177`. -/
theorem exists_tensor_of_congestion_le {D χ : ℕ} (hD : 1 ≤ D) (hdim : ∀ ℓ, N.dim ℓ ≤ D)
    (hχ : ∀ e, Fintype.card (R.Traversal e) ≤ χ) :
    ∃ A : Tensor G d, (∀ σ, stateCoeff A σ = N.coeff site σ) ∧ ∀ e, A.bondDim e ≤ D ^ χ :=
  ⟨R.toTensor, R.toTensor_stateCoeff, fun e =>
    (R.toTensor_bondDim_le hdim e).trans (Nat.pow_le_pow_right hD (hχ e))⟩

end Routing

end TNLean.PEPS.Approximation
