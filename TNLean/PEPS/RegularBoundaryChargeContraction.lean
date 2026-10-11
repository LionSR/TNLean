/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenRegionGluing
import TNLean.PEPS.RegularEdgeChargeContraction

/-!
# A diagonal charge on an open boundary bond

On the part containing its ordered tail, a prescribed boundary label turns the
charge insertion into its literal scalar character weight. On the other part
no site factor changes. Source: SCP10, arXiv:1001.3807,
`eq:anyons:chargeon-def` and `eq:anyons:chargeon-move-setting`,
lines 2432–2453 and 2489–2507.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem prod_charge_at_tail
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (e : Edge Γ) (ht : e.1.1 ∈ R) (χ : G → ℂ) (p : G)
    (α : (v : RV R) → IncidentEdge Γ v.1 → G) (σ : RV R → Fin d) :
    (∏ v : RV R, regularEdgeCharacterSite a e χ p v.1 (α v) (σ v)) =
      χ (p * α ⟨e.1.1,ht⟩ (edgeLeftIncident e)) *
        ∏ v : RV R, a v.1 (α v) (σ v) := by
  classical
  let o : RV R := ⟨e.1.1,ht⟩
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ o,
    Fintype.prod_eq_mul_prod_subtype_ne (fun v : RV R => a v.1 (α v) (σ v)) o]
  have hr : (∏ v : {v : RV R // v ≠ o},
      regularEdgeCharacterSite a e χ p v.1.1 (α v.1) (σ v.1)) =
      ∏ v : {v : RV R // v ≠ o}, a v.1.1 (α v.1) (σ v.1) := by
    apply Finset.prod_congr rfl
    intro v _
    have hv : v.1.1 ≠ e.1.1 := fun h => v.2 (Subtype.ext h)
    simp only [regularEdgeCharacterSite, dite_eq_right hv]
  rw [hr]
  simp only [o, regularEdgeCharacterSite, dite_true, edgeLeftIncident, mul_assoc]

omit [DecidableEq G] in
/-- The actual open contraction retains exactly the prescribed diagonal weight
at the tail endpoint of a crossing bond. Source: SCP10, lines 2489–2507. -/
theorem graphOpenRegionNetwork_regularEdgeCharacterSite_boundary
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (e : RB (Γ := Γ) R) (χ : G → ℂ) (p : G)
    (θ : RB (Γ := Γ) R → G) (σ : RV R → Fin d) :
    graphOpenRegionNetwork (regularEdgeCharacterSite a e.1 χ p) R θ σ =
      (if e.1.1.1 ∈ R then χ (p * θ e) else 1) * graphOpenRegionNetwork a R θ σ := by
  classical
  rw [graphOpenRegionNetwork_eq_sum_internal, graphOpenRegionNetwork_eq_sum_internal,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases ht : e.1.1.1 ∈ R
  · rw [ite_eq_left ht, prod_charge_at_tail a R e.1 ht]
    congr 3
    change (graphRegionIncidentConfigEquiv R).symm (ξ,θ)
      ⟨e.1,isRegionBoundaryEdge_touches R e.2⟩ = θ e
    exact congrArg (fun z => z.2 e)
      ((graphRegionIncidentConfigEquiv R).apply_symm_apply (ξ,θ))
  · rw [ite_eq_right ht, one_mul]
    apply Finset.prod_congr rfl
    intro v _
    have hv : v.1 ≠ e.1.1.1 := fun h => ht (h ▸ v.2)
    simp only [regularEdgeCharacterSite, dite_eq_right hv]


omit [DecidableEq G] in
/-- The charge-inserted union is the actual joined contraction with precisely one
character weight on its shared bond label. Source: SCP10, lines 2489–2507. -/
theorem graphOpenRegionNetwork_regularEdgeCharacterSite_union
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (L S : Finset V) (hd : Disjoint L S) (e : RegionJoiningEdge (Γ := Γ) L S)
    (χ : G → ℂ) (p : G) (θ : RB (Γ := Γ) (L ∪ S) → G)
    (σ : RV (L ∪ S) → Fin d) :
    graphOpenRegionNetwork (regularEdgeCharacterSite a e.1 χ p) (L ∪ S) θ σ =
      ∑ μ : RegionJoiningEdge (Γ := Γ) L S → G, χ (p * μ e) *
        (graphOpenRegionNetwork a L (regionGluingBoundary L S L μ θ)
          (fun v => σ ⟨v.1,Finset.mem_union_left _ v.2⟩) *
        graphOpenRegionNetwork a S (regionGluingBoundary L S S μ θ)
          (fun v => σ ⟨v.1,Finset.mem_union_right _ v.2⟩)) := by
  classical
  rw [graphOpenRegionNetwork_union _ L S hd]
  apply Finset.sum_congr rfl
  intro μ _
  obtain ⟨heL,heS⟩ := regionJoiningEdge_boundary L S hd e
  rw [graphOpenRegionNetwork_regularEdgeCharacterSite_boundary a L ⟨e.1,heL⟩,
    graphOpenRegionNetwork_regularEdgeCharacterSite_boundary a S ⟨e.1,heS⟩]
  have hL : regionGluingBoundary L S L μ θ ⟨e.1,heL⟩ = μ e := by
    simp only [regionGluingBoundary, regionGluingLabels, dite_eq_left e.2]
  have hS : regionGluingBoundary L S S μ θ ⟨e.1,heS⟩ = μ e := by
    simp only [regionGluingBoundary, regionGluingLabels, dite_eq_left e.2]
  rw [hL,hS]
  rcases Finset.mem_union.mp e.2.1.1 with ht | ht
  · have hn : e.1.1.1 ∉ S := fun h => Finset.disjoint_left.mp hd ht h
    simp only [ite_eq_left ht, ite_eq_right hn, one_mul, mul_assoc]
  · have hn : e.1.1.1 ∉ L := fun h => Finset.disjoint_left.mp hd h ht
    simp only [ite_eq_left ht, ite_eq_right hn, one_mul]
    ring
end TNLean.PEPS
