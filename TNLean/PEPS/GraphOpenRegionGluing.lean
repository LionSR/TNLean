/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenRegionContraction
import TNLean.Algebra.FinSumPermutation

/-!
# Joining two actual open regions with fixed external labels

Source: SCP10, arXiv:1001.3807, finite-region blocking, lines 1765–1920,
and the independent column contractions in `eq:anyons:chargeon-move-setting`,
lines 2489–2507. Only labels on bonds joining the two disjoint regions are
summed; every label on the external boundary remains fixed.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- Bonds internal to the union but internal to neither part are its joining bonds.
Source: SCP10, independent column blocking, lines 2489–2507. -/
abbrev RegionJoiningEdge (L S : Finset V) :=
  {e : Edge Γ // (e.1.1 ∈ L ∪ S ∧ e.1.2 ∈ L ∪ S) ∧
    ¬ (e.1.1 ∈ L ∧ e.1.2 ∈ L) ∧ ¬ (e.1.1 ∈ S ∧ e.1.2 ∈ S)}

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Each joining bond is a boundary bond of both disjoint parts.
Source: SCP10, independent column contractions, lines 2489–2507. -/
theorem regionJoiningEdge_boundary (L S : Finset V) (hd : Disjoint L S)
    (e : RegionJoiningEdge (Γ := Γ) L S) :
    IsRegionBoundaryEdge L e.1 ∧ IsRegionBoundaryEdge S e.1 := by
  rcases Finset.mem_union.mp e.2.1.1 with ht | ht <;>
    rcases Finset.mem_union.mp e.2.1.2 with hh | hh
  · exact (e.2.2.1 ⟨ht,hh⟩).elim
  · have hnt : e.1.1.1 ∉ S := fun h => Finset.disjoint_left.mp hd ht h
    have hnh : e.1.1.2 ∉ L := fun h => Finset.disjoint_left.mp hd h hh
    exact ⟨Or.inl ⟨ht,hnh⟩,Or.inr ⟨hnt,hh⟩⟩
  · have hnt : e.1.1.1 ∉ L := fun h => Finset.disjoint_left.mp hd h ht
    have hnh : e.1.1.2 ∉ S := fun h => Finset.disjoint_left.mp hd hh h
    exact ⟨Or.inr ⟨hnt,hh⟩,Or.inl ⟨ht,hnh⟩⟩
  · exact (e.2.2.2 ⟨ht,hh⟩).elim

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Adjacency between disjoint parts supplies an actual joining bond,
independently of the ordering of its endpoints.
Source: SCP10, independent column contractions, lines 2489–2507. -/
def regionJoiningEdge_ofAdj (L S : Finset V) (hd : Disjoint L S)
    {x y : V} (hxy : Γ.Adj x y) (hx : x ∈ L) (hy : y ∈ S) :
    RegionJoiningEdge (Γ := Γ) L S := by
  have hnx : x ∉ S := fun h => Finset.disjoint_left.mp hd hx h
  have hny : y ∉ L := fun h => Finset.disjoint_left.mp hd h hy
  refine ⟨Edge.ofAdj hxy,?_⟩
  rcases Edge.ofAdj_endpoints hxy with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;>
    simp only [ht,hh]
  · exact ⟨⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy⟩,
      fun h => hny h.2,fun h => hnx h.1⟩
  · exact ⟨⟨Finset.mem_union_right _ hy,Finset.mem_union_left _ hx⟩,
      fun h => hny h.1,fun h => hnx h.2⟩

private def unionInternalSplit (L S : Finset V) (hd : Disjoint L S) :
    RI (Γ := Γ) (L ∪ S) ≃
      RI (Γ := Γ) L ⊕ (RI (Γ := Γ) S ⊕ RegionJoiningEdge (Γ := Γ) L S) where
  toFun e := if hL : e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L then .inl ⟨e.1,hL⟩ else
    if hS : e.1.1.1 ∈ S ∧ e.1.1.2 ∈ S then .inr (.inl ⟨e.1,hS⟩) else
      .inr (.inr ⟨e.1,e.2,hL,hS⟩)
  invFun
    | .inl e => ⟨e.1, by exact ⟨Finset.mem_union_left _ e.2.1,
        Finset.mem_union_left _ e.2.2⟩⟩
    | .inr (.inl e) => ⟨e.1, by exact ⟨Finset.mem_union_right _ e.2.1,
        Finset.mem_union_right _ e.2.2⟩⟩
    | .inr (.inr e) => ⟨e.1,e.2.1⟩
  left_inv e := by dsimp only; split_ifs <;> rfl
  right_inv e := by
    rcases e with e | e | e
    · simp only [dite_eq_left e.2]
    · have hn : ¬ (e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L) := by
        intro h
        exact Finset.disjoint_left.mp hd h.1 e.2.1
      simp only [dite_eq_right hn, dite_eq_left e.2]
    · simp only [dite_eq_right e.2.2.1, dite_eq_right e.2.2.2]

variable {G : Type*} [Group G] [Fintype G]

private def unionInternalConfigEquiv (L S : Finset V) (hd : Disjoint L S) :
    (RI (Γ := Γ) (L ∪ S) → G) ≃
      (RI (Γ := Γ) L → G) × (RI (Γ := Γ) S → G) ×
        (RegionJoiningEdge (Γ := Γ) L S → G) :=
  ((unionInternalSplit L S hd).arrowCongr (Equiv.refl G)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ G).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ G)))

/-- A common full label family with prescribed joining and external boundary labels.
Internal labels in each part are filled by the identity only in this auxiliary
boundary assembly. Source: SCP10, lines 2489–2507. -/
def regionGluingLabels (L S : Finset V)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (θ : RB (Γ := Γ) (L ∪ S) → G) :
    Edge Γ → G := fun e =>
  if h : (e.1.1 ∈ L ∪ S ∧ e.1.2 ∈ L ∪ S) ∧
      ¬ (e.1.1 ∈ L ∧ e.1.2 ∈ L) ∧ ¬ (e.1.1 ∈ S ∧ e.1.2 ∈ S) then μ ⟨e,h⟩
  else if h : IsRegionBoundaryEdge (L ∪ S) e then θ ⟨e,h⟩ else 1

/-- The original crossing labels of either part, read from the same label family.
Source: SCP10, independent column contractions, lines 2489–2507. -/
def regionGluingBoundary (L S R : Finset V)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (θ : RB (Γ := Γ) (L ∪ S) → G) :
    RB (Γ := Γ) R → G := fun e => regionGluingLabels L S μ θ e.1

omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] in
private theorem unionInternalConfigEquiv_symm_left (L S : Finset V) (hd : Disjoint L S)
    (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (e : RI (Γ := Γ) L) :
    (unionInternalConfigEquiv L S hd).symm (ξ,ζ,μ)
      ⟨e.1,Finset.mem_union_left _ e.2.1,Finset.mem_union_left _ e.2.2⟩ = ξ e := by
  simp [unionInternalConfigEquiv, unionInternalSplit, e.2]

omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] in
private theorem unionInternalConfigEquiv_symm_right (L S : Finset V) (hd : Disjoint L S)
    (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (e : RI (Γ := Γ) S) :
    (unionInternalConfigEquiv L S hd).symm (ξ,ζ,μ)
      ⟨e.1,Finset.mem_union_right _ e.2.1,Finset.mem_union_right _ e.2.2⟩ = ζ e := by
  have hn : ¬ (e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L) := by
    intro h
    exact Finset.disjoint_left.mp hd h.1 e.2.1
  simp [unionInternalConfigEquiv, unionInternalSplit, hn, e.2]

omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] in
private theorem unionInternalConfigEquiv_symm_joining (L S : Finset V)
    (hd : Disjoint L S) (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (e : RegionJoiningEdge (Γ := Γ) L S) :
    (unionInternalConfigEquiv L S hd).symm (ξ,ζ,μ) ⟨e.1,e.2.1⟩ = μ e := by
  simp [unionInternalConfigEquiv, unionInternalSplit, e.2]


omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] in
private theorem incidentCompletion (R : Finset V) (q : Edge Γ → G) :
    (graphRegionIncidentConfigEquiv R).symm
      ((fun e : RI (Γ := Γ) R => q e.1), (fun e : RB (Γ := Γ) R => q e.1)) =
        (fun e => q e.1) := by
  exact (graphRegionIncidentConfigEquiv R).symm_apply_apply (fun e => q e.1)

private def joinedLabel (L S : Finset V) (ξ : RI (Γ := Γ) L → G)
    (ζ : RI (Γ := Γ) S → G) (μ : RegionJoiningEdge (Γ := Γ) L S → G)
    (θ : RB (Γ := Γ) (L ∪ S) → G) : Edge Γ → G := fun e =>
  if h : e.1.1 ∈ L ∧ e.1.2 ∈ L then ξ ⟨e,h⟩ else
  if h : e.1.1 ∈ S ∧ e.1.2 ∈ S then ζ ⟨e,h⟩ else regionGluingLabels L S μ θ e

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
private theorem joinedLabel_internal (L S : Finset V) (hd : Disjoint L S)
    (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (θ : RB (Γ := Γ) (L ∪ S) → G) :
    (fun e : RI (Γ := Γ) (L ∪ S) => joinedLabel L S ξ ζ μ θ e.1) =
      (unionInternalConfigEquiv L S hd).symm (ξ,ζ,μ) := by
  funext e
  by_cases hL : e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L
  · rw [joinedLabel, dite_eq_left hL]
    exact (unionInternalConfigEquiv_symm_left L S hd ξ ζ μ ⟨e.1,hL⟩).symm
  · by_cases hS : e.1.1.1 ∈ S ∧ e.1.1.2 ∈ S
    · rw [joinedLabel, dite_eq_right hL, dite_eq_left hS]
      exact (unionInternalConfigEquiv_symm_right L S hd ξ ζ μ ⟨e.1,hS⟩).symm
    · rw [joinedLabel, dite_eq_right hL, dite_eq_right hS,
        regionGluingLabels, dite_eq_left ⟨e.2,hL,hS⟩]
      exact (unionInternalConfigEquiv_symm_joining L S hd ξ ζ μ ⟨e.1,e.2,hL,hS⟩).symm

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
private theorem joinedLabel_boundary (L S : Finset V)
    (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (θ : RB (Γ := Γ) (L ∪ S) → G) :
    (fun e : RB (Γ := Γ) (L ∪ S) => joinedLabel L S ξ ζ μ θ e.1) = θ := by
  funext e
  have hn : ¬ (e.1.1.1 ∈ L ∪ S ∧ e.1.1.2 ∈ L ∪ S) := by
    rcases e.2 with ht | hh
    · exact fun h => ht.2 h.2
    · exact fun h => hh.1 h.1
  have hL : ¬ (e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L) := by
    intro h
    exact hn ⟨Finset.mem_union_left _ h.1,Finset.mem_union_left _ h.2⟩
  have hS : ¬ (e.1.1.1 ∈ S ∧ e.1.1.2 ∈ S) := by
    intro h
    exact hn ⟨Finset.mem_union_right _ h.1,Finset.mem_union_right _ h.2⟩
  have hc : ¬ ((e.1.1.1 ∈ L ∪ S ∧ e.1.1.2 ∈ L ∪ S) ∧
      ¬ (e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L) ∧ ¬ (e.1.1.1 ∈ S ∧ e.1.1.2 ∈ S)) :=
    fun h => hn h.1
  simp only [joinedLabel, dite_eq_right hL, dite_eq_right hS, regionGluingLabels,
    dite_eq_right hc, dite_eq_left e.2]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
private theorem joinedLabel_part_boundary (L S R : Finset V) (hd : Disjoint L S)
    (hR : R = L ∨ R = S) (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (θ : RB (Γ := Γ) (L ∪ S) → G) :
    (fun e : RB (Γ := Γ) R => joinedLabel L S ξ ζ μ θ e.1) =
      regionGluingBoundary L S R μ θ := by
  funext e
  have hnL : ¬ (e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L) := by
    intro h
    rcases hR with rfl | rfl <;> rcases e.2 with ht | hh
    · exact ht.2 h.2
    · exact hh.1 h.1
    · exact Finset.disjoint_left.mp hd h.1 ht.1
    · exact Finset.disjoint_left.mp hd h.2 hh.2
  have hnS : ¬ (e.1.1.1 ∈ S ∧ e.1.1.2 ∈ S) := by
    intro h
    rcases hR with rfl | rfl <;> rcases e.2 with ht | hh
    · exact Finset.disjoint_left.mp hd ht.1 h.1
    · exact Finset.disjoint_left.mp hd hh.2 h.2
    · exact ht.2 h.2
    · exact hh.1 h.1
  simp only [joinedLabel, dite_eq_right hnL, dite_eq_right hnS, regionGluingBoundary]



/-- Joining two disjoint original open regions sums only their common bonds;
all external boundary labels remain fixed. The contraction identity is derived,
not supplied. Source: SCP10, column blocking, lines 2489–2507. -/
theorem graphOpenRegionNetwork_union {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (L S : Finset V) (hd : Disjoint L S)
    (θ : RB (Γ := Γ) (L ∪ S) → G) (σ : (v : RV (L ∪ S)) → P v.1) :
    graphOpenRegionNetwork a (L ∪ S) θ σ =
      ∑ μ : RegionJoiningEdge (Γ := Γ) L S → G,
        graphOpenRegionNetwork a L (regionGluingBoundary L S L μ θ)
          (fun v => σ ⟨v.1,Finset.mem_union_left _ v.2⟩) *
        graphOpenRegionNetwork a S (regionGluingBoundary L S S μ θ)
          (fun v => σ ⟨v.1,Finset.mem_union_right _ v.2⟩) := by
  classical
  let : Fintype (RI (Γ := Γ) L → G) := inferInstance
  let : Fintype (RI (Γ := Γ) S → G) := inferInstance
  let : Fintype (RegionJoiningEdge (Γ := Γ) L S → G) := inferInstance
  have hterm (ξ : RI (Γ := Γ) L → G) (ζ : RI (Γ := Γ) S → G)
      (μ : RegionJoiningEdge (Γ := Γ) L S → G) :
      (∏ v : RV (L ∪ S), a v.1 (fun e =>
        (graphRegionIncidentConfigEquiv (L ∪ S)).symm
          ((unionInternalConfigEquiv L S hd).symm (ξ,ζ,μ),θ)
            ⟨e.1,isRegionIncidentEdge_of_regionVertex (L ∪ S) v e⟩) (σ v)) =
      (∏ v : RV L, a v.1 (fun e => (graphRegionIncidentConfigEquiv L).symm
        (ξ,regionGluingBoundary L S L μ θ)
          ⟨e.1,isRegionIncidentEdge_of_regionVertex L v e⟩)
          (σ ⟨v.1,Finset.mem_union_left _ v.2⟩)) *
      (∏ v : RV S, a v.1 (fun e => (graphRegionIncidentConfigEquiv S).symm
        (ζ,regionGluingBoundary L S S μ θ)
          ⟨e.1,isRegionIncidentEdge_of_regionVertex S v e⟩)
          (σ ⟨v.1,Finset.mem_union_right _ v.2⟩)) := by
    let q := joinedLabel L S ξ ζ μ θ
    have hu : (graphRegionIncidentConfigEquiv (L ∪ S)).symm
        ((unionInternalConfigEquiv L S hd).symm (ξ,ζ,μ),θ) = (fun e => q e.1) := by
      calc
        _ = (graphRegionIncidentConfigEquiv (L ∪ S)).symm
            ((fun e => q e.1),(fun e => q e.1)) := by
          apply congrArg (graphRegionIncidentConfigEquiv (L ∪ S)).symm
          exact Prod.ext (joinedLabel_internal L S hd ξ ζ μ θ).symm
            (joinedLabel_boundary L S ξ ζ μ θ).symm
        _ = _ := incidentCompletion (L ∪ S) q
    have hξ : (fun e : RI (Γ := Γ) L => q e.1) = ξ := by
      funext e
      simp only [q, joinedLabel, dite_eq_left e.2]
    have hζ : (fun e : RI (Γ := Γ) S => q e.1) = ζ := by
      funext e
      have hn : ¬ (e.1.1.1 ∈ L ∧ e.1.1.2 ∈ L) := by
        intro h
        exact Finset.disjoint_left.mp hd h.1 e.2.1
      simp only [q, joinedLabel, dite_eq_right hn, dite_eq_left e.2]
    have hl : (graphRegionIncidentConfigEquiv L).symm
        (ξ,regionGluingBoundary L S L μ θ) = (fun e => q e.1) := by
      rw [← hξ, ← joinedLabel_part_boundary L S L hd (Or.inl rfl) ξ ζ μ θ]
      exact incidentCompletion L q
    have hs : (graphRegionIncidentConfigEquiv S).symm
        (ζ,regionGluingBoundary L S S μ θ) = (fun e => q e.1) := by
      rw [← hζ, ← joinedLabel_part_boundary L S S hd (Or.inr rfl) ξ ζ μ θ]
      exact incidentCompletion S q
    rw [hu,hl,hs, ← (Equiv.Finset.union L S hd).prod_comp]
    simp only [Fintype.prod_sum_type, Equiv.Finset.union_inl, Equiv.Finset.union_inr]
  rw [graphOpenRegionNetwork_eq_sum_internal,
    ← (unionInternalConfigEquiv L S hd).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_comm]
  simp_rw [hterm]
  rw [graphOpenRegionNetwork_eq_sum_internal, graphOpenRegionNetwork_eq_sum_internal]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
end TNLean.PEPS
