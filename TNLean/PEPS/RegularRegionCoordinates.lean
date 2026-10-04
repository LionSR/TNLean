/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionCycleRank
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Subtype

/-!
# Spanning-tree coordinates for regular physical half-edge labels

The reversible changes of regular-group coordinates in SCP10,
arXiv:1001.3807, lines 1765–1920, extend along a spanning tree of a connected
region. Tree edge ratios determine a unique vertex labelling equal to the
identity at a chosen root. Removing this vertex labelling leaves boundary
coordinates, one reference coordinate on each internal edge, and one residual
coordinate on each edge outside the tree.

These are bijections of basis labels. No factorization of a contracted tensor,
region isometry, or entropy formula is assumed.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {W G : Type*} [Fintype W] [LinearOrder W] [Group G] [Fintype G]

/-- Vertex labels normalized to the identity at a chosen root. -/
abbrev RootedGroupLabels (o : W) := {r : W → G // r o = 1}

/-- Omitting the fixed root coordinate identifies normalized labels with the
unconstrained labels on the remaining vertices. -/
noncomputable def rootedGroupLabelsEquiv (o : W) :
    ({v : W // v ≠ o} → G) ≃ RootedGroupLabels (G := G) o where
  toFun r := ⟨fun v => if h : v = o then 1 else r ⟨v, h⟩, by simp⟩
  invFun r v := r.1 v.1
  left_inv r := by funext v; simp [v.2]
  right_inv r := by
    apply Subtype.ext
    funext v
    by_cases h : v = o
    · subst v; simp [r.2]
    · simp [h]

/-- The transport from the smaller to the larger endpoint of a tree edge. -/
def rootedTreeGradient (T : SimpleGraph W) (o : W)
    (r : RootedGroupLabels (G := G) o) : Edge T → G :=
  fun e => r.1 e.1.2 * (r.1 e.1.1)⁻¹

omit [Fintype W] [Fintype G] in
private theorem rootedTreeGradient_injective (T : SimpleGraph W) (hT : T.Connected)
    (o : W) : Function.Injective (rootedTreeGradient (G := G) T o) := by
  intro r s hrs
  have hAdj (u v : W) (h : T.Adj u v) :
      (r.1 u)⁻¹ * s.1 u = (r.1 v)⁻¹ * s.1 v := by
    have he := congrFun hrs (Edge.ofAdj h)
    change r.1 (Edge.ofAdj h).1.2 * (r.1 (Edge.ofAdj h).1.1)⁻¹ =
      s.1 (Edge.ofAdj h).1.2 * (s.1 (Edge.ofAdj h).1.1)⁻¹ at he
    have hc : (r.1 (Edge.ofAdj h).1.1)⁻¹ * s.1 (Edge.ofAdj h).1.1 =
        (r.1 (Edge.ofAdj h).1.2)⁻¹ * s.1 (Edge.ofAdj h).1.2 := by
      calc
        _ = (r.1 (Edge.ofAdj h).1.2)⁻¹ *
            (r.1 (Edge.ofAdj h).1.2 * (r.1 (Edge.ofAdj h).1.1)⁻¹) *
            s.1 (Edge.ofAdj h).1.1 := by group
        _ = _ := by rw [he]; group
    rcases Edge.ofAdj_endpoints h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa [h₁, h₂] using hc
    · simpa [h₁, h₂] using hc.symm
  have hconst (v : W) : (r.1 v)⁻¹ * s.1 v = (r.1 o)⁻¹ * s.1 o := by
    obtain ⟨p⟩ := hT v o
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hAdj _ _ h).trans (ih hrs hAdj)
  apply Subtype.ext
  funext v
  have hv := hconst v
  simp only [r.2, s.2, inv_one, one_mul] at hv
  exact inv_mul_eq_one.mp hv

/-- On a tree, arbitrary edge transports determine a unique normalized vertex
labelling. Injectivity follows along paths; the tree edge count gives
surjectivity for finite groups. Source: SCP10, lines 1765–1920. -/
noncomputable def rootedTreeGradientEquiv (T : SimpleGraph W) [DecidableRel T.Adj]
    (hT : T.IsTree) (o : W) : RootedGroupLabels (G := G) o ≃ (Edge T → G) :=
  Equiv.ofBijective (rootedTreeGradient T o) (by
    classical
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨rootedTreeGradient_injective T hT.connected o, ?_⟩
    rw [← Fintype.card_congr (rootedGroupLabelsEquiv (G := G) o), Fintype.card_fun,
      Fintype.card_fun]
    congr 1
    have hc := hT.card_edgeFinset
    have he : Fintype.card (Edge T) = T.edgeFinset.card := by
      rw [Fintype.card_congr (orderedEdgeEquivEdgeSet (Γ := T))]
      simp [SimpleGraph.edgeFinset]
    rw [← he] at hc
    simp only [Fintype.card_subtype_compl (fun v : W => v = o), Fintype.card_subtype_eq]
    omega)

section Region

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

private abbrev Boundary (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
private abbrev Internal (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}

private def boundaryVertex (R : Finset V) (e : Boundary (Γ := Γ) R) : {v // v ∈ R} :=
  if h : e.1.1.1 ∈ R then ⟨e.1.1.1, h⟩ else
    ⟨e.1.1.2, by
      rcases e.2 with h' | h'
      · exact False.elim (h h'.1)
      · exact h'.2⟩

private def boundaryHalfEdge (R : Finset V) (e : Boundary (Γ := Γ) R) :
    (v : {v // v ∈ R}) × IncidentEdge Γ v.1 :=
  ⟨boundaryVertex R e, e.1, by
    unfold boundaryVertex
    split_ifs <;> simp⟩

private def internalTail (R : Finset V) (e : Internal (Γ := Γ) R) : {v // v ∈ R} :=
  ⟨e.1.1.1, e.2.1⟩

private def internalHead (R : Finset V) (e : Internal (Γ := Γ) R) : {v // v ∈ R} :=
  ⟨e.1.1.2, e.2.2⟩

private def halfEdgeIndex (R : Finset V) :
    Boundary (Γ := Γ) R ⊕ (Internal (Γ := Γ) R ⊕ Internal (Γ := Γ) R) →
      (v : {v // v ∈ R}) × IncidentEdge Γ v.1
  | .inl e => boundaryHalfEdge R e
  | .inr (.inl e) => ⟨internalTail R e, e.1, Or.inl rfl⟩
  | .inr (.inr e) => ⟨internalHead R e, e.1, Or.inr rfl⟩

private def halfEdgeIndexInverse (R : Finset V)
    (s : (v : {v // v ∈ R}) × IncidentEdge Γ v.1) :
    Boundary (Γ := Γ) R ⊕ (Internal (Γ := Γ) R ⊕ Internal (Γ := Γ) R) :=
  if h : s.2.1.1.1 ∈ R ∧ s.2.1.1.2 ∈ R then
    if ht : s.2.1.1.1 = s.1.1 then .inr (.inl ⟨s.2.1, h⟩)
    else .inr (.inr ⟨s.2.1, h⟩)
  else .inl ⟨s.2.1, by
    rcases s.2.2 with ht | ht
    · left
      have hv : s.2.1.1.1 ∈ R := by simpa only [ht] using s.1.2
      exact ⟨hv, fun hh => h ⟨hv, hh⟩⟩
    · right
      have hv : s.2.1.1.2 ∈ R := by simpa only [ht] using s.1.2
      exact ⟨fun hh => h ⟨hh, hv⟩, hv⟩⟩

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem halfEdgeIndex_left_inv (R : Finset V)
    (s : Boundary (Γ := Γ) R ⊕ (Internal (Γ := Γ) R ⊕ Internal (Γ := Γ) R)) :
    halfEdgeIndexInverse R (halfEdgeIndex R s) = s := by
  rcases s with e | e | e
  · have hn : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
      rcases e.2 with h | h
      · exact fun hh => h.2 hh.2
      · exact fun hh => h.1 hh.1
    simp [halfEdgeIndexInverse, halfEdgeIndex, boundaryHalfEdge, hn]
  · simp [halfEdgeIndexInverse, halfEdgeIndex, internalTail, e.2]
  · simp [halfEdgeIndexInverse, halfEdgeIndex, internalHead, e.2, ne_of_lt e.1.2.1]

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem halfEdgeIndex_right_inv (R : Finset V)
    (s : (v : {v // v ∈ R}) × IncidentEdge Γ v.1) :
    halfEdgeIndex R (halfEdgeIndexInverse R s) = s := by
  rcases s with ⟨v, e⟩
  unfold halfEdgeIndexInverse
  split_ifs with hi ht
  · apply Sigma.ext (Subtype.ext ht)
    exact (Subtype.heq_iff_coe_eq (fun f => by
      simp only [halfEdgeIndex, internalTail]
      rw [ht])).mpr rfl
  · have hh : e.1.1.2 = v.1 := e.2.resolve_left ht
    apply Sigma.ext (Subtype.ext hh)
    exact (Subtype.heq_iff_coe_eq (fun f => by
      simp only [halfEdgeIndex, internalHead]
      rw [hh])).mpr rfl
  · have hb : IsRegionBoundaryEdge R e.1 := by
      rcases e.2 with ht | ht
      · exact Or.inl ⟨by simpa only [ht] using v.2,
          fun hh => hi ⟨by simpa only [ht] using v.2, hh⟩⟩
      · exact Or.inr ⟨fun hh => hi ⟨hh, by simpa only [ht] using v.2⟩,
          by simpa only [ht] using v.2⟩
    change halfEdgeIndex R (.inl ⟨e.1, hb⟩) = ⟨v, e⟩
    have hv : boundaryVertex R ⟨e.1, hb⟩ = v := by
      unfold boundaryVertex
      split_ifs with htail
      · apply Subtype.ext
        rcases e.2 with h | h
        · exact h
        · exact False.elim (hi ⟨htail, by simpa only [h] using v.2⟩)
      · apply Subtype.ext
        exact e.2.resolve_left (fun h => htail (by simpa only [h] using v.2))
    apply Sigma.ext hv
    exact (Subtype.heq_iff_coe_eq (fun f => by
      simp only [halfEdgeIndex, boundaryHalfEdge]
      rw [hv])).mpr rfl

private def halfEdgeIndexEquiv (R : Finset V) :
    Boundary (Γ := Γ) R ⊕ (Internal (Γ := Γ) R ⊕ Internal (Γ := Γ) R) ≃
      (v : {v // v ∈ R}) × IncidentEdge Γ v.1 where
  toFun := halfEdgeIndex R
  invFun := halfEdgeIndexInverse R
  left_inv := halfEdgeIndex_left_inv R
  right_inv := halfEdgeIndex_right_inv R

private def halfEdgeLabelEquiv (R : Finset V) :
    ((v : {v // v ∈ R}) → IncidentEdge Γ v.1 → G) ≃
      (Boundary (Γ := Γ) R → G) ×
        (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G) :=
  ((Equiv.piCurry fun (_ : {v // v ∈ R}) (_ : IncidentEdge Γ _) => G).symm.trans
    ((halfEdgeIndexEquiv R).symm.arrowCongr (Equiv.refl G))).trans
    ((Equiv.sumArrowEquivProdArrow _ _ G).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ G)))

private def regionTreeEdgeEquiv (R : Finset V) (T : SimpleGraph {v : V // v ∈ R})
    (hT : T ≤ Γ.induce (R : Set V)) :
    Edge T ≃ {e : Internal (Γ := Γ) R // T.Adj (internalTail R e) (internalHead R e)} where
  toFun e := ⟨⟨⟨(e.1.1.1, e.1.2.1), e.2.1, hT e.2.2⟩, e.1.1.2, e.1.2.2⟩, e.2.2⟩
  invFun e := ⟨(internalTail R e.1, internalHead R e.1), e.1.1.2.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def regionTreeGradientEquiv (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R}) :
    RootedGroupLabels (G := G) o ≃
      ({e : Internal (Γ := Γ) R // T.Adj (internalTail R e) (internalHead R e)} → G) :=
  (rootedTreeGradientEquiv T htree o).trans
    ((regionTreeEdgeEquiv R T hT).arrowCongr (Equiv.refl G))

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem regionTreeGradientEquiv_apply (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (r : RootedGroupLabels (G := G) o)
    (e : {e : Internal (Γ := Γ) R // T.Adj (internalTail R e) (internalHead R e)}) :
    regionTreeGradientEquiv R T hT htree o r e =
      r.1 (internalHead R e.1) * (r.1 (internalTail R e.1))⁻¹ := rfl

/-- Boundary coordinates, internal-edge references, normalized vertex labels,
and residual coordinates on the edges outside the chosen spanning tree. -/
abbrev RegularRegionCoordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) (o : {v // v ∈ R}) :=
  ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) ×
    ({e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G) ×
    RootedGroupLabels (G := G) o ×
    ({e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G)

private noncomputable def decodeCoordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (β : (Boundary (Γ := Γ) R → G) ×
      (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G)) :
    RegularRegionCoordinates (Γ := Γ) (G := G) R T o :=
  let r := (regionTreeGradientEquiv R T hT htree o).symm
    (fun e => β.2.2 e.1 * (β.2.1 e.1)⁻¹)
  (fun e => (r.1 (boundaryVertex R e))⁻¹ * β.1 e,
    fun e => (r.1 (internalTail R e))⁻¹ * β.2.1 e,
    r, fun e => (r.1 (internalHead R e.1))⁻¹ * β.2.2 e.1 *
      ((r.1 (internalTail R e.1))⁻¹ * β.2.1 e.1)⁻¹)

private def encodeCoordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj] (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    (Boundary (Γ := Γ) R → G) ×
      (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G) :=
  (fun e => c.2.2.1.1 (boundaryVertex R e) * c.1 e,
    fun e => c.2.2.1.1 (internalTail R e) * c.2.1 e,
    fun e => c.2.2.1.1 (internalHead R e) *
      (if h : T.Adj (internalTail R e) (internalHead R e) then 1 else c.2.2.2 ⟨e, h⟩) *
      c.2.1 e)

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem decode_encodeCoordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    decodeCoordinates R T hT htree o (encodeCoordinates R T o c) = c := by
  have hr : (regionTreeGradientEquiv R T hT htree o).symm
      (fun e => (encodeCoordinates R T o c).2.2 e.1 *
        ((encodeCoordinates R T o c).2.1 e.1)⁻¹) = c.2.2.1 := by
    apply (regionTreeGradientEquiv R T hT htree o).injective
    rw [Equiv.apply_symm_apply]
    funext e
    simp only [encodeCoordinates, dite_eq_left e.2, mul_one, regionTreeGradientEquiv_apply]
    group
  unfold decodeCoordinates
  rw [hr]
  apply Prod.ext
  · funext e
    simp [encodeCoordinates, mul_assoc]
  · apply Prod.ext
    · funext e
      simp [encodeCoordinates, mul_assoc]
    · apply Prod.ext
      · rfl
      · funext e
        simp only [encodeCoordinates]
        group
        split_ifs with he
        · exact False.elim (e.2 he)
        · rfl

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem encode_decodeCoordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (β : (Boundary (Γ := Γ) R → G) ×
      (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G)) :
    encodeCoordinates R T o (decodeCoordinates R T hT htree o β) = β := by
  let r := (regionTreeGradientEquiv R T hT htree o).symm
    (fun e => β.2.2 e.1 * (β.2.1 e.1)⁻¹)
  have hr (e : Internal (Γ := Γ) R)
      (he : T.Adj (internalTail R e) (internalHead R e)) :
      r.1 (internalHead R e) * (r.1 (internalTail R e))⁻¹ =
        β.2.2 e * (β.2.1 e)⁻¹ := by
    exact congrFun ((regionTreeGradientEquiv R T hT htree o).apply_symm_apply
      (fun f => β.2.2 f.1 * (β.2.1 f.1)⁻¹)) ⟨e, he⟩
  apply Prod.ext
  · funext e
    simp [encodeCoordinates, decodeCoordinates, mul_assoc]
  · apply Prod.ext
    · funext e
      simp [encodeCoordinates, decodeCoordinates, mul_assoc]
    · funext e
      change r.1 (internalHead R e) *
        (if he : T.Adj (internalTail R e) (internalHead R e) then 1 else
          (r.1 (internalHead R e))⁻¹ * β.2.2 e *
            ((r.1 (internalTail R e))⁻¹ * β.2.1 e)⁻¹) *
        ((r.1 (internalTail R e))⁻¹ * β.2.1 e) = β.2.2 e
      split_ifs with he
      · rw [mul_one, ← mul_assoc, hr e he]
        group
      · group

/-- Source: SCP10, accessible regular virtual labels and reversible blocking,
lines 1765–1920. Every physical half-edge configuration has unique spanning-tree
coordinates. The inverse reconstructs its labels by left multiplication by the
normalized vertex label and the appropriate boundary, reference, or cycle label. -/
noncomputable def regularRegionCoordinatesEquiv (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R}) :
    ((v : {v : V // v ∈ R}) → IncidentEdge Γ v.1 → G) ≃
      RegularRegionCoordinates (Γ := Γ) (G := G) R T o :=
  (halfEdgeLabelEquiv R).trans
    { toFun := decodeCoordinates R T hT htree o
      invFun := encodeCoordinates R T o
      left_inv := encode_decodeCoordinates R T hT htree o
      right_inv := decode_encodeCoordinates R T hT htree o }

omit [Group G] [Fintype G] [Fintype V] [DecidableRel Γ.Adj] in
private theorem halfEdgeLabelEquiv_symm_tail (R : Finset V)
    (β : (Boundary (Γ := Γ) R → G) ×
      (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G))
    (e : Internal (Γ := Γ) R) :
    (halfEdgeLabelEquiv R).symm β (internalTail R e) ⟨e.1, Or.inl rfl⟩ = β.2.1 e :=
  congrArg (fun γ => γ.2.1 e) ((halfEdgeLabelEquiv R).apply_symm_apply β)

omit [Group G] [Fintype G] [Fintype V] [DecidableRel Γ.Adj] in
private theorem halfEdgeLabelEquiv_symm_head (R : Finset V)
    (β : (Boundary (Γ := Γ) R → G) ×
      (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G))
    (e : Internal (Γ := Γ) R) :
    (halfEdgeLabelEquiv R).symm β (internalHead R e) ⟨e.1, Or.inr rfl⟩ = β.2.2 e :=
  congrArg (fun γ => γ.2.2 e) ((halfEdgeLabelEquiv R).apply_symm_apply β)

omit [Group G] [Fintype G] [Fintype V] [DecidableRel Γ.Adj] in
private theorem halfEdgeLabelEquiv_symm_boundary (R : Finset V)
    (β : (Boundary (Γ := Γ) R → G) ×
      (Internal (Γ := Γ) R → G) × (Internal (Γ := Γ) R → G))
    (e : Boundary (Γ := Γ) R) :
    (halfEdgeLabelEquiv R).symm β (boundaryHalfEdge R e).1 (boundaryHalfEdge R e).2 =
      β.1 e :=
  congrArg (fun γ => γ.1 e) ((halfEdgeLabelEquiv R).apply_symm_apply β)

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Reconstruction at the smaller endpoint of an internal edge. -/
theorem regularRegionCoordinatesEquiv_symm_internal_tail (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm c
        ⟨e.1.1.1, e.2.1⟩ ⟨e.1, Or.inl rfl⟩ =
      c.2.2.1.1 ⟨e.1.1.1, e.2.1⟩ * c.2.1 e :=
  halfEdgeLabelEquiv_symm_tail R (encodeCoordinates R T o c) e

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Reconstruction at the larger endpoint of an internal edge. Tree edges have
unit residual; each remaining edge carries its own cycle residual. -/
theorem regularRegionCoordinatesEquiv_symm_internal_head (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm c
        ⟨e.1.1.2, e.2.2⟩ ⟨e.1, Or.inr rfl⟩ =
      c.2.2.1.1 ⟨e.1.1.2, e.2.2⟩ *
        (if h : T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩ then 1 else c.2.2.2 ⟨e, h⟩) *
        c.2.1 e :=
  halfEdgeLabelEquiv_symm_head R (encodeCoordinates R T o c) e

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Reconstruction on a boundary edge whose smaller endpoint lies in the region. -/
theorem regularRegionCoordinatesEquiv_symm_boundary_tail (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (e : Edge Γ) (ht : e.1.1 ∈ R) (hh : e.1.2 ∉ R) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm c
        ⟨e.1.1, ht⟩ ⟨e, Or.inl rfl⟩ =
      c.2.2.1.1 ⟨e.1.1, ht⟩ * c.1 ⟨e, Or.inl ⟨ht, hh⟩⟩ := by
  have h := halfEdgeLabelEquiv_symm_boundary R (encodeCoordinates R T o c)
    ⟨e, Or.inl ⟨ht, hh⟩⟩
  have hv : boundaryVertex R ⟨e, Or.inl ⟨ht, hh⟩⟩ = ⟨e.1.1, ht⟩ := by
    unfold boundaryVertex
    exact dite_eq_left ht
  have hs : boundaryHalfEdge R ⟨e, Or.inl ⟨ht, hh⟩⟩ =
      ⟨⟨e.1.1, ht⟩, ⟨e, Or.inl rfl⟩⟩ := by
    apply Sigma.ext hv
    exact (Subtype.heq_iff_coe_eq (fun f => by
      simp only [boundaryHalfEdge]
      rw [hv])).mpr rfl
  have hval := congrArg (fun s => (halfEdgeLabelEquiv R).symm
    (encodeCoordinates R T o c) s.1 s.2) hs
  calc
    _ = _ := hval.symm
    _ = _ := h
    _ = _ := by change c.2.2.1.1 (boundaryVertex R _) * _ = _; rw [hv]

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Reconstruction on a boundary edge whose larger endpoint lies in the region. -/
theorem regularRegionCoordinatesEquiv_symm_boundary_head (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (e : Edge Γ) (ht : e.1.1 ∉ R) (hh : e.1.2 ∈ R) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm c
        ⟨e.1.2, hh⟩ ⟨e, Or.inr rfl⟩ =
      c.2.2.1.1 ⟨e.1.2, hh⟩ * c.1 ⟨e, Or.inr ⟨ht, hh⟩⟩ := by
  have h := halfEdgeLabelEquiv_symm_boundary R (encodeCoordinates R T o c)
    ⟨e, Or.inr ⟨ht, hh⟩⟩
  have hv : boundaryVertex R ⟨e, Or.inr ⟨ht, hh⟩⟩ = ⟨e.1.2, hh⟩ := by
    unfold boundaryVertex
    exact dite_eq_right ht
  have hs : boundaryHalfEdge R ⟨e, Or.inr ⟨ht, hh⟩⟩ =
      ⟨⟨e.1.2, hh⟩, ⟨e, Or.inr rfl⟩⟩ := by
    apply Sigma.ext hv
    exact (Subtype.heq_iff_coe_eq (fun f => by
      simp only [boundaryHalfEdge]
      rw [hv])).mpr rfl
  have hval := congrArg (fun s => (halfEdgeLabelEquiv R).symm
    (encodeCoordinates R T o c) s.1 s.2) hs
  calc
    _ = _ := hval.symm
    _ = _ := h
    _ = _ := by change c.2.2.1.1 (boundaryVertex R _) * _ = _; rw [hv]

end Region

end TNLean.PEPS
