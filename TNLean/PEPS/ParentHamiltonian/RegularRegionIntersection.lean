/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionalProjectorRange

/-!
# Intersection for regular regions meeting at one vertex

Two regular regional ranges intersect in the range of their union when they
share exactly one vertex and no edge joins their disjoint parts. All exterior
half-edge labels remain arbitrary. Local flatness potentials are glued by a
constant right translation on one region; no commutativity of the group is used.

This is the regular-coordinate intersection step for the three-block geometry
of SCP10, arXiv:1001.3807, Theorem 5.4. The statement concerns actual regional
ranges, rather than closed vectors or a one-dimensional replacement of the
external legs. Transport to arbitrary G-injective site maps is a separate step.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Flatness restricts to every smaller region. -/
theorem IsRegularRegionHalfEdgeFlat.of_subset {R S : Finset V} (hRS : R ⊆ S)
    {α : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ}
    (hα : IsRegularRegionHalfEdgeFlat S (restrictRegularRegionHalfEdges S α)) :
    IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) := by
  obtain ⟨k, hk⟩ := hα
  exact ⟨fun v => k ⟨v.1, hRS v.2⟩, fun e =>
    hk ⟨e.1, hRS e.2.1, hRS e.2.2⟩⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
/-- Without edges between the disjoint parts, each internal edge of a union
already lies in one of the two regions. -/
theorem internalEdge_union_of_no_cross {R S : Finset V}
    (hcross : ∀ u ∈ R \ S, ∀ v ∈ S \ R, ¬ Γ.Adj u v)
    {e : Edge Γ} (ht : e.1.1 ∈ R ∪ S) (hh : e.1.2 ∈ R ∪ S) :
    (e.1.1 ∈ R ∧ e.1.2 ∈ R) ∨ (e.1.1 ∈ S ∧ e.1.2 ∈ S) := by
  by_cases htR : e.1.1 ∈ R <;> by_cases hhR : e.1.2 ∈ R
  · exact Or.inl ⟨htR, hhR⟩
  · have hhS : e.1.2 ∈ S := (Finset.mem_union.mp hh).resolve_left hhR
    by_cases htS : e.1.1 ∈ S
    · exact Or.inr ⟨htS, hhS⟩
    · exact False.elim (hcross _ (Finset.mem_sdiff.mpr ⟨htR, htS⟩) _
        (Finset.mem_sdiff.mpr ⟨hhS, hhR⟩) e.2.2)
  · have htS : e.1.1 ∈ S := (Finset.mem_union.mp ht).resolve_left htR
    by_cases hhS : e.1.2 ∈ S
    · exact Or.inr ⟨htS, hhS⟩
    · exact False.elim (hcross _ (Finset.mem_sdiff.mpr ⟨hhR, hhS⟩) _
        (Finset.mem_sdiff.mpr ⟨htS, htR⟩) e.2.2.symm)
  · exact Or.inr ⟨(Finset.mem_union.mp ht).resolve_left htR,
      (Finset.mem_union.mp hh).resolve_left hhR⟩

omit [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Potentials on regions meeting at one vertex glue after a constant right
translation. In particular, cycles through both regions create no new flatness
condition under the no-cross-edge hypothesis. -/
theorem isRegularRegionHalfEdgeFlat_union_iff {R S : Finset V} {b : V}
    (hoverlap : R ∩ S = {b})
    (hcross : ∀ u ∈ R \ S, ∀ v ∈ S \ R, ¬ Γ.Adj u v)
    (α : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) :
    IsRegularRegionHalfEdgeFlat (R ∪ S) (restrictRegularRegionHalfEdges (R ∪ S) α) ↔
      IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) ∧
      IsRegularRegionHalfEdgeFlat S (restrictRegularRegionHalfEdges S α) := by
  constructor
  · intro h
    exact ⟨h.of_subset Finset.subset_union_left, h.of_subset Finset.subset_union_right⟩
  · rintro ⟨⟨kR, hkR⟩, ⟨kS, hkS⟩⟩
    have hb : b ∈ R ∩ S := by rw [hoverlap]; exact Finset.mem_singleton_self b
    have hbR := (Finset.mem_inter.mp hb).1
    have hbS := (Finset.mem_inter.mp hb).2
    let t : G := (kS ⟨b, hbS⟩)⁻¹ * kR ⟨b, hbR⟩
    let k (v : {v : V // v ∈ R ∪ S}) : G :=
      if h : v.1 ∈ R then kR ⟨v.1, h⟩
      else kS ⟨v.1, (Finset.mem_union.mp v.2).resolve_left h⟩ * t
    have hk_left (v : {v : V // v ∈ R ∪ S}) (hv : v.1 ∈ R) :
        k v = kR ⟨v.1, hv⟩ := by simp [k, hv]
    have hk_right (v : {v : V // v ∈ R ∪ S}) (hv : v.1 ∈ S) :
        k v = kS ⟨v.1, hv⟩ * t := by
      by_cases hvR : v.1 ∈ R
      · have hvb : v.1 = b := Finset.mem_singleton.mp
          (hoverlap ▸ Finset.mem_inter.mpr ⟨hvR, hv⟩)
        subst b
        simp [k, hvR, t]
      · simp [k, hvR]
    refine ⟨k, fun e => ?_⟩
    rcases internalEdge_union_of_no_cross hcross e.2.1 e.2.2 with he | he
    · rw [hk_left _ he.1, hk_left _ he.2]
      exact hkR ⟨e.1, he⟩
    · rw [hk_right _ he.1, hk_right _ he.2]
      simpa only [restrictRegularRegionHalfEdges, mul_inv_rev, mul_assoc] using
        congrArg (fun g => t⁻¹ * g) (hkS ⟨e.1, he⟩)

/-- Atomic invariance and flat support characterize the actual lifted regional
range, including every complementary slice. -/
theorem mem_regularGlobalRegionRange_iff_fixed_flat (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    x ∈ regularGlobalRegionRange R ↔
      (∀ v ∈ R, regularGlobalVertexAverage (Γ := Γ) (G := G) v *ᵥ x = x) ∧
      (∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R →
        regularRegionEdgeAverage (G := G) Finset.univ e *ᵥ x = x) ∧
      (∀ α, ¬ IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) →
        x α = 0) := by
  rw [mem_regularGlobalRegionRange_iff_invariant_flat,
    regularRegionalVertexAverages_fixed_iff, regularRegionalEdgeAverages_fixed_iff]

/-- Enlarging a region strengthens its actual regular range condition. -/
theorem regularGlobalRegionRange_antitone {R S : Finset V} (hRS : R ⊆ S) :
    regularGlobalRegionRange (Γ := Γ) (G := G) S ≤ regularGlobalRegionRange R := by
  intro x hx
  obtain ⟨hv, he, hf⟩ := (mem_regularGlobalRegionRange_iff_fixed_flat S x).mp hx
  apply (mem_regularGlobalRegionRange_iff_fixed_flat R x).mpr
  exact ⟨fun v h => hv v (hRS h), fun e ht hh => he e (hRS ht) (hRS hh),
    fun α hα => hf α (fun h => hα (h.of_subset hRS))⟩

/-- The actual regular ranges of two regions meeting at one vertex intersect
in the range of their union, provided their disjoint parts have no joining edge.
No conditions are imposed on exterior half-edge labels. This is the regular
three-block intersection step of SCP10, Theorem 5.4. -/
theorem regularGlobalRegionRange_inf_eq_union {R S : Finset V} {b : V}
    (hoverlap : R ∩ S = {b})
    (hcross : ∀ u ∈ R \ S, ∀ v ∈ S \ R, ¬ Γ.Adj u v) :
    regularGlobalRegionRange (Γ := Γ) (G := G) R ⊓ regularGlobalRegionRange S =
      regularGlobalRegionRange (R ∪ S) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hvR, heR, hfR⟩ := (mem_regularGlobalRegionRange_iff_fixed_flat R x).mp hx.1
    obtain ⟨hvS, heS, hfS⟩ := (mem_regularGlobalRegionRange_iff_fixed_flat S x).mp hx.2
    apply (mem_regularGlobalRegionRange_iff_fixed_flat (R ∪ S) x).mpr
    refine ⟨fun v hv => (Finset.mem_union.mp hv).elim (hvR v) (hvS v), ?_, ?_⟩
    · intro e ht hh
      exact (internalEdge_union_of_no_cross hcross ht hh).elim
        (fun he => heR e he.1 he.2) (fun he => heS e he.1 he.2)
    · intro α hα
      by_cases hR : IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α)
      · exact hfS α (fun hS => hα
          ((isRegularRegionHalfEdgeFlat_union_iff hoverlap hcross α).mpr ⟨hR, hS⟩))
      · exact hfR α hR
  · exact le_inf (regularGlobalRegionRange_antitone Finset.subset_union_left)
      (regularGlobalRegionRange_antitone Finset.subset_union_right)

end TNLean.PEPS
