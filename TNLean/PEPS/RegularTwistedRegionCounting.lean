/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionCounting
import TNLean.Algebra.FinSumPermutation

/-!
# Regular-bond counting with a restricted translation

The internal labels remain independent when the common translation is restricted
to the intertwiners of two bond-operator assignments. Their contribution is one
factor of the group order per internal edge. Only the boundary translation sum
is restricted.

These are finite counting identities used in the actual twisted-region
contraction for Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of
Theorem 6.9, `Papers/1001.3807/paper_v3.tex`, lines 1935–1990 and 2043–2072.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {ι G : Type*} [Fintype ι] [DecidableEq ι]
variable [Group G] [Fintype G] [DecidableEq G]

open Classical in
/-- Restricting the common translation leaves the same independent internal labels.
Source: SCP10, proof of Theorem 6.9, lines 1935–1990. -/
theorem sum_boundaryRestriction_filtered_translations_eq_card
    (p : ι → Prop) [DecidablePred p] (μ ν : {i // p i} → G)
    (t : G → Prop) [DecidablePred t] :
    (∑ η : ι → G, ∑ θ : ι → G, ∑ g : G,
      if (fun i : {i // p i} => η i.1) = μ ∧
        (fun i : {i // p i} => θ i.1) = ν ∧
        η = (fun i => g * θ i) ∧ t g then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) ^ Fintype.card {i // ¬ p i} *
        ∑ g : G, if μ = (fun i => g * ν i) ∧ t g then 1 else 0 := by
  classical
  have hcount (g : G) :
      (∑ θ : ι → G, ∑ η : ι → G,
        if (fun i : {i // p i} => η i.1) = μ ∧
          (fun i : {i // p i} => θ i.1) = ν ∧
          η = (fun i => g * θ i) ∧ t g then (1 : ℂ) else 0) =
        if μ = (fun i => g * ν i) ∧ t g
          then (Fintype.card G : ℂ) ^ Fintype.card {i // ¬ p i} else 0 := by
    rw [Finset.sum_comm]
    by_cases ht : t g
    · simp only [ht, and_true]
      exact sum_translated_boundaryRestriction_eq_card p μ ν g
    · simp [ht]
  rw [Fintype.sum_reverse_three]
  simp only [hcount]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> simp

section Region

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

open Classical in
/-- Source: SCP10, proof of Theorem 6.9, lines 1935–1990. A restricted
translation sum on a region still leaves one free label per internal bond. -/
theorem sum_regionBoundary_filtered_translations_eq_card (R : Finset V)
    (μ ν : {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (t : G → Prop) [DecidablePred t] :
    (∑ η : {e : Edge Γ // IsRegionIncidentEdge R e} → G,
      ∑ θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G, ∑ g : G,
      if (fun e : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
          η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = μ ∧
        (fun e : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
          θ ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = ν ∧
        η = (fun e => g * θ e) ∧ t g then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) ^ Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} *
        ∑ g : G, if μ = (fun e => g * ν e) ∧ t g then 1 else 0 := by
  classical
  let p : {e : Edge Γ // IsRegionIncidentEdge R e} → Prop :=
    fun e => IsRegionBoundaryEdge R e.1
  have hrestrict (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G)
      (β : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
      ((fun e : {e // p e} => η e.1) = (fun e => β ⟨e.1.1, e.2⟩)) ↔
        (fun e : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
          η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = β := by
    exact regionBoundaryLabel_eq_iff R
      (fun e => η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) β
  have htranslation (g : G) :
      ((fun e : {e // p e} => μ ⟨e.1.1, e.2⟩) =
        (fun e => g * ν ⟨e.1.1, e.2⟩)) ↔ μ = (fun e => g * ν e) := by
    exact regionBoundaryLabel_eq_iff R μ (fun e => g * ν e)
  have h := sum_boundaryRestriction_filtered_translations_eq_card p
    (fun e => μ ⟨e.1.1, e.2⟩) (fun e => ν ⟨e.1.1, e.2⟩) t
  simp only [hrestrict, htranslation] at h
  rw [card_regionIncident_not_boundary] at h
  exact h

end Region

end TNLean.PEPS
