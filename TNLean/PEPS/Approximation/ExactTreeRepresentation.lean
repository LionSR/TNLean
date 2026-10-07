/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-!
# Exact PEPS from a spanning tree

Every coefficient function on a finite connected graph with at least two vertices
is the literal contraction of a native PEPS. Each edge in a chosen connected
spanning subgraph carries the whole physical configuration; every other edge has
bond dimension one. Equality tensors copy the configuration between vertices,
and one distinguished vertex contributes its coefficient. A spanning tree is a
special case, obtained from Mathlib's spanning-tree theorem.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `07-assembly.tex`, lines 203–211, at immutable manuscript
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proof below works for any
connected spanning subgraph; it does not assume the contraction identity.
-/

noncomputable section

open scoped BigOperators

/-!
## Declaration provenance

Provenance-ID: 8773-configurationequiv
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.configurationEquiv
Provenance-ID: 8773-bonddim
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.bondDim
Provenance-ID: 8773-decode
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.decode
Provenance-ID: 8773-encode
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.encode
Provenance-ID: 8773-decode_encode
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.decode_encode
Provenance-ID: 8773-decode_injective
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.decode_injective
Provenance-ID: 8773-bonddim_pos
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.bondDim_pos
Provenance-ID: 8773-bonddim_le
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.bondDim_le
Provenance-ID: 8773-ports
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.Ports
Provenance-ID: 8773-ports-ofconnected
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.Ports.ofConnected
Provenance-ID: 8773-locallabel
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.localLabel
Provenance-ID: 8773-isconsistent
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.IsConsistent
Provenance-ID: 8773-tensor
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.tensor
Provenance-ID: 8773-locallabel_encode
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.localLabel_encode
Provenance-ID: 8773-isconsistent_encode
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.isConsistent_encode
Provenance-ID: 8773-tensor_component_encode
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.tensor_component_encode
Provenance-ID: 8773-isconsistent_of_component_ne_zero
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.isConsistent_of_component_ne_zero
Provenance-ID: 8773-locallabel_eq_of_adj
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_adj
Provenance-ID: 8773-locallabel_eq_of_consistent
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.localLabel_eq_of_consistent
Provenance-ID: 8773-eq_encode_of_consistent
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.eq_encode_of_consistent
Provenance-ID: 8773-tensor_product_eq_zero
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.tensor_product_eq_zero
Provenance-ID: 8773-statecoeff_tensor
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor
Provenance-ID: 8773-statecoeff_tensor_eq
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_eq
Provenance-ID: 8773-statecoeff_tensor_ne_zero
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.stateCoeff_tensor_ne_zero
Provenance-ID: 8773-exists_exact_tree_tensor
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.exists_exact_tree_tensor
Provenance-ID: 8773-singletontensor
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.singletonTensor
Provenance-ID: 8773-statecoeff_singletontensor
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.stateCoeff_singletonTensor
Provenance-ID: 8773-exists_exact_tensor
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.exists_exact_tensor
Provenance-ID: 8773-statecoeff_of_isempty
Downstream declaration: TNLean.PEPS.ExactTreeRepresentation.stateCoeff_of_isEmpty
Source: September 24, 2026, sec:assembly.
The finite-size construction is in lines 203–214 of the cited assembly section.
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex>
Independently formalized; no upstream Lean proof text reused.
Auxiliary geometry and finite-size exact PEPS results do not establish the large-size theorem.
-/

namespace TNLean.PEPS.ExactTreeRepresentation

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (T : SimpleGraph V) (q : ℕ)

/-- The common virtual index numbers all physical configurations. -/
def configurationEquiv : (V → Fin q) ≃ Fin (q ^ Fintype.card V) :=
  Fintype.equivFinOfCardEq (by simp)

open Classical in
/-- Active edges carry a complete physical configuration; the other edges have
one-dimensional virtual spaces. Source: manuscript, assembly, lines 203–211. -/
def bondDim (e : Edge G) : ℕ :=
  if T.Adj e.1.1 e.1.2 then q ^ Fintype.card V else 1

/-- An active edge index, decoded as a physical configuration. -/
def decode (e : Edge G) (he : T.Adj e.1.1 e.1.2)
    (j : Fin (bondDim T q e)) : V → Fin q :=
  (configurationEquiv q).symm ⟨j.val, by simpa [bondDim, he] using j.isLt⟩

open Classical in
/-- The unique edge assignment carrying the same physical configuration on
all active edges. -/
def encode (σ : V → Fin q) (e : Edge G) : Fin (bondDim T q e) :=
  if he : T.Adj e.1.1 e.1.2 then
    ⟨(configurationEquiv q σ).val, by
      simp [bondDim, he]⟩
  else ⟨0, by simp [bondDim, he]⟩

omit [DecidableRel G.Adj] in
@[simp] theorem decode_encode (σ : V → Fin q) (e : Edge G)
    (he : T.Adj e.1.1 e.1.2) :
    decode T q e he (encode T q σ e) = σ := by
  classical
  simp [decode, encode, he]

omit [DecidableRel G.Adj] in
/-- The decoded configuration determines an active virtual index. -/
theorem decode_injective (e : Edge G) (he : T.Adj e.1.1 e.1.2) :
    Function.Injective (decode T q e he) := by
  classical
  intro i j hij
  have h := (configurationEquiv q).symm.injective hij
  exact Fin.ext (congrArg (fun x : Fin (q ^ Fintype.card V) => x.val) h)

omit [DecidableRel G.Adj] in
/-- Bond dimensions are positive when the physical dimension is positive. -/
theorem bondDim_pos (hq : 0 < q) (e : Edge G) : 0 < bondDim T q e := by
  classical
  unfold bondDim
  split_ifs
  · exact pow_pos hq _
  · exact Nat.zero_lt_one

omit [DecidableRel G.Adj] in
/-- Every bond is bounded by the number of physical configurations. -/
theorem bondDim_le (hq : 0 < q) (e : Edge G) :
    bondDim T q e ≤ q ^ Fintype.card V := by
  classical
  unfold bondDim
  split_ifs
  · exact le_rfl
  · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hq))

/-- One active incident edge at each vertex, used only to read the locally
copied configuration. -/
structure Ports where
  edge : (v : V) → IncidentEdge G v
  active : ∀ v, T.Adj (edge v).1.1.1 (edge v).1.1.2

variable {T q}

/-- A connected spanning subgraph on at least two vertices has an active
incident edge at every vertex. -/
def Ports.ofConnected [Nontrivial V] (hT : T ≤ G) (hconn : T.Connected) :
    Ports (G := G) T where
  edge v := by
    classical
    let w := (hconn.preconnected.exists_adj_of_nontrivial v).choose
    have hvw : T.Adj v w :=
      (hconn.preconnected.exists_adj_of_nontrivial v).choose_spec
    let e := Edge.ofAdj (hT hvw)
    refine ⟨e, ?_⟩
    rcases Edge.ofAdj_endpoints (hT hvw) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  active v := by
    classical
    let w := (hconn.preconnected.exists_adj_of_nontrivial v).choose
    have hvw : T.Adj v w :=
      (hconn.preconnected.exists_adj_of_nontrivial v).choose_spec
    change T.Adj (Edge.ofAdj (hT hvw)).1.1 (Edge.ofAdj (hT hvw)).1.2
    rcases Edge.ofAdj_endpoints (hT hvw) with h | h
    · simpa only [h.1, h.2] using hvw
    · simpa only [h.1, h.2] using hvw.symm

variable (P : Ports (G := G) T) (q)

/-- Read the configuration from the chosen active incident edge. -/
def localLabel (v : V) (η : (ie : IncidentEdge G v) → Fin (bondDim T q ie.1)) :
    V → Fin q :=
  decode T q (P.edge v).1 (P.active v) (η (P.edge v))

/-- The equality tensor checks the physical index and every active incident
edge against the locally read configuration. -/
def IsConsistent (v : V)
    (η : (ie : IncidentEdge G v) → Fin (bondDim T q ie.1)) (i : Fin q) : Prop :=
  localLabel q P v η v = i ∧
    ∀ (ie : IncidentEdge G v) (he : T.Adj ie.1.1.1 ie.1.1.2),
      decode T q ie.1 he (η ie) = localLabel q P v η

open Classical in
/-- Equality-copy tensors with the coefficient stored at exactly one root.
Source: manuscript, assembly, lines 203–211. -/
def tensor (root : V) (ψ : (V → Fin q) → ℂ) : Tensor G q where
  bondDim := bondDim T q
  component v η i :=
    if IsConsistent q P v η i then
      if v = root then ψ (localLabel q P v η) else 1
    else 0

omit [DecidableRel G.Adj] in
@[simp] theorem localLabel_encode (σ : V → Fin q) (v : V) :
    localLabel q P v (fun ie => encode T q σ ie.1) = σ :=
  decode_encode T q σ (P.edge v).1 (P.active v)

omit [DecidableRel G.Adj] in
/-- The canonical virtual assignment satisfies every local equality tensor. -/
theorem isConsistent_encode (σ : V → Fin q) (v : V) :
    IsConsistent q P v (fun ie => encode T q σ ie.1) (σ v) := by
  classical
  constructor
  · simp
  · intro ie he
    simp

@[simp] theorem tensor_component_encode (root : V) (ψ : (V → Fin q) → ℂ)
    (σ : V → Fin q) (v : V) :
    (tensor q P root ψ).component v (fun ie => encode T q σ ie.1) (σ v) =
      if v = root then ψ σ else 1 := by
  classical
  simp [tensor, isConsistent_encode]

/-- A nonzero local tensor entry satisfies both of its equality constraints. -/
theorem isConsistent_of_component_ne_zero (root : V) (ψ : (V → Fin q) → ℂ)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (bondDim T q ie.1)) (i : Fin q)
    (h : (tensor q P root ψ).component v η i ≠ 0) : IsConsistent q P v η i := by
  classical
  by_contra hc
  exact h (by simp [tensor, hc])

omit [DecidableRel G.Adj] in
/-- Consistent incident configurations have equal labels at both endpoints of
an active edge. The ordering used to store native edges is irrelevant. -/
theorem localLabel_eq_of_adj (η : (e : Edge G) → Fin (bondDim T q e))
    (σ : V → Fin q)
    (hc : ∀ v, IsConsistent q P v (fun ie => η ie.1) (σ v))
    (hT : T ≤ G) {u v : V} (huv : T.Adj u v) :
    localLabel q P u (fun ie => η ie.1) = localLabel q P v (fun ie => η ie.1) := by
  classical
  let e := Edge.ofAdj (hT huv)
  have he : T.Adj e.1.1 e.1.2 := by
    change T.Adj (Edge.ofAdj (hT huv)).1.1 (Edge.ofAdj (hT huv)).1.2
    rcases Edge.ofAdj_endpoints (hT huv) with h | h
    · simpa only [h.1, h.2] using huv
    · simpa only [h.1, h.2] using huv.symm
  have heu : e.1.1 = u ∨ e.1.2 = u := by
    rcases Edge.ofAdj_endpoints (hT huv) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  have hev : e.1.1 = v ∨ e.1.2 = v := by
    rcases Edge.ofAdj_endpoints (hT huv) with h | h
    · exact Or.inr h.2
    · exact Or.inl h.1
  exact ((hc u).2 ⟨e, heu⟩ he).symm.trans ((hc v).2 ⟨e, hev⟩ he)

omit [DecidableRel G.Adj] in
/-- Connectivity makes every local copy equal to the physical configuration. -/
theorem localLabel_eq_of_consistent (η : (e : Edge G) → Fin (bondDim T q e))
    (σ : V → Fin q)
    (hc : ∀ v, IsConsistent q P v (fun ie => η ie.1) (σ v))
    (hT : T ≤ G) (hconn : T.Connected) (v : V) :
    localLabel q P v (fun ie => η ie.1) = σ := by
  classical
  have hconstant : ∀ u w : V,
      localLabel q P u (fun ie => η ie.1) =
        localLabel q P w (fun ie => η ie.1) := by
    intro u w
    exact Relation.reflTransGen_le_of_equivalence_of_le
      (Setoid.ker (fun v => localLabel q P v (fun ie => η ie.1))).iseqv
      (fun _ _ hadj => localLabel_eq_of_adj q P η σ hc hT hadj) u w
      ((SimpleGraph.reachable_iff_reflTransGen u w).mp (hconn.preconnected u w))
  funext w
  exact (congrFun (hconstant v w) w).trans (hc w).1

omit [DecidableRel G.Adj] in
/-- All virtual indices are forced by the local equality tensors. -/
theorem eq_encode_of_consistent (η : (e : Edge G) → Fin (bondDim T q e))
    (σ : V → Fin q)
    (hc : ∀ v, IsConsistent q P v (fun ie => η ie.1) (σ v))
    (hT : T ≤ G) (hconn : T.Connected) : η = encode T q σ := by
  classical
  funext e
  by_cases he : T.Adj e.1.1 e.1.2
  · apply decode_injective T q e he
    rw [decode_encode]
    exact ((hc e.1.1).2 ⟨e, Or.inl rfl⟩ he).trans
      (localLabel_eq_of_consistent q P η σ hc hT hconn e.1.1)
  · apply Fin.ext
    have hi := (η e).isLt
    have hj := (encode T q σ e).isLt
    simp only [bondDim, he, ite_false] at hi hj
    omega

/-- Every summand other than the encoded physical configuration vanishes. -/
theorem tensor_product_eq_zero (hT : T ≤ G) (hconn : T.Connected)
    (root : V) (ψ : (V → Fin q) → ℂ) (σ : V → Fin q)
    (η : VirtualConfig (tensor q P root ψ)) (hη : η ≠ encode T q σ) :
    (∏ v : V, (tensor q P root ψ).component v (fun ie => η ie.1) (σ v)) = 0 := by
  classical
  by_contra hp
  apply hη
  apply eq_encode_of_consistent q P η σ _ hT hconn
  intro v
  apply isConsistent_of_component_ne_zero
  exact (Finset.prod_ne_zero_iff.mp hp) v (Finset.mem_univ v)

/-- The literal native PEPS contraction equals the supplied coefficient.
Source: manuscript, assembly, lines 203–211. -/
theorem stateCoeff_tensor (hT : T ≤ G) (hconn : T.Connected)
    (root : V) (ψ : (V → Fin q) → ℂ) (σ : V → Fin q) :
    stateCoeff (tensor q P root ψ) σ = ψ σ := by
  classical
  let η₀ : VirtualConfig (tensor q P root ψ) := encode T q σ
  rw [stateCoeff, Fintype.sum_eq_single η₀]
  · change (∏ v, (tensor q P root ψ).component v
      (fun ie => encode T q σ ie.1) (σ v)) = ψ σ
    simp only [tensor_component_encode, Fintype.prod_ite_eq']
  · intro η hη
    exact tensor_product_eq_zero q P hT hconn root ψ σ η hη

/-- Exactness is equality of the full coefficient functions. -/
theorem stateCoeff_tensor_eq (hT : T ≤ G) (hconn : T.Connected)
    (root : V) (ψ : (V → Fin q) → ℂ) :
    stateCoeff (tensor q P root ψ) = ψ :=
  funext (stateCoeff_tensor q P hT hconn root ψ)

/-- A nonzero input has nonzero native contraction; no normalization factor is
introduced by the equality-copy construction. -/
theorem stateCoeff_tensor_ne_zero (hT : T ≤ G) (hconn : T.Connected)
    (root : V) {ψ : (V → Fin q) → ℂ} (hψ : ψ ≠ 0) :
    stateCoeff (tensor q P root ψ) ≠ 0 := by
  classical
  simpa only [stateCoeff_tensor_eq q P hT hconn root ψ] using hψ

open Classical in
/-- Every vector on a finite connected graph with at least two vertices has an
exact PEPS on a spanning tree, with positive bonds bounded by the number of
physical configurations. Source: manuscript, assembly, lines 203–211. -/
theorem exists_exact_tree_tensor [Nontrivial V] (hG : G.Connected) (hq : 0 < q)
    (ψ : (V → Fin q) → ℂ) :
    ∃ (T : SimpleGraph V) (A : Tensor G q), T ≤ G ∧ T.IsTree ∧
      (∀ e, A.bondDim e = if T.Adj e.1.1 e.1.2 then q ^ Fintype.card V else 1) ∧
      (∀ e, 0 < A.bondDim e) ∧ (∀ e, A.bondDim e ≤ q ^ Fintype.card V) ∧
      stateCoeff A = ψ := by
  classical
  obtain ⟨T, hT, ht⟩ := hG.exists_isTree_le
  let P := Ports.ofConnected hT ht.connected
  let root : V := Classical.choice hG.nonempty
  refine ⟨T, tensor q P root ψ, hT, ht, fun _ => rfl, ?_, ?_, ?_⟩
  · exact bondDim_pos T q hq
  · exact bondDim_le T q hq
  · exact stateCoeff_tensor_eq q P hT ht.connected root ψ

/-- The one-site tensor stores the entire one-site coefficient function. -/
def singletonTensor (ψ : (V → Fin q) → ℂ) : Tensor G q where
  bondDim _ := 1
  component _ _ i := ψ (fun _ => i)

/-- The singleton case needs no virtual configuration index. -/
theorem stateCoeff_singletonTensor [Subsingleton V] (root : V)
    (ψ : (V → Fin q) → ℂ) (σ : V → Fin q) :
    stateCoeff (singletonTensor (G := G) q ψ) σ = ψ σ := by
  classical
  let : Unique (VirtualConfig (singletonTensor (G := G) q ψ)) := by
    change Unique (Edge G → Fin 1)
    infer_instance
  rw [stateCoeff, Fintype.sum_unique, Fintype.prod_subsingleton _ root]
  change ψ (fun _ => σ root) = ψ σ
  congr 1
  funext v
  exact congrArg σ (Subsingleton.elim root v)

/-- The connected-graph representation includes singleton graphs. -/
theorem exists_exact_tensor (hG : G.Connected) (hq : 0 < q)
    (ψ : (V → Fin q) → ℂ) :
    ∃ A : Tensor G q, (∀ e, 0 < A.bondDim e) ∧
      (∀ e, A.bondDim e ≤ q ^ Fintype.card V) ∧ stateCoeff A = ψ := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hV =>
      let := hV
      let root : V := Classical.choice hG.nonempty
      refine ⟨singletonTensor q ψ, fun _ => Nat.zero_lt_one, ?_, ?_⟩
      · intro e
        exact ((G.ne_of_adj e.2.2) (Subsingleton.elim _ _)).elim
      · exact funext (stateCoeff_singletonTensor (G := G) q root ψ)
  | inr hV =>
      let := hV
      obtain ⟨T, A, _, _, _, hpos, hbound, hstate⟩ := exists_exact_tree_tensor q hG hq ψ
      exact ⟨A, hpos, hbound, hstate⟩

/-- On a graph with no vertices the native empty product is one. Thus an
arbitrary scalar on the empty configuration cannot be represented by changing
vertex tensors; nonemptiness in the connected-graph theorem is essential. -/
theorem stateCoeff_of_isEmpty [IsEmpty V] (A : Tensor G q) (σ : V → Fin q) :
    stateCoeff A σ = 1 := by
  classical
  simp [stateCoeff]

end TNLean.PEPS.ExactTreeRepresentation
