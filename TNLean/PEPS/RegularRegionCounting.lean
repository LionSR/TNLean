/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularOpenRegion

/-!
# Counting regular-bond assignments with a fixed boundary

Once a common group translation has been fixed, every internal bond of a region
can be assigned independently. The number of assignments is therefore a power
of the group order. These finite counting identities are used in the region
contraction of Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of
Theorem 6.9, local source lines 1935–1957 and 2043–2072.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace TNLean.PEPS

section Restriction

variable {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq ι] [DecidableEq G]

open Classical in
/-- Fixing a subfamily of finite labels leaves one independent label at every
remaining index. -/
theorem sum_boundaryRestriction_eq_card (p : ι → Prop) [DecidablePred p]
    (μ : {i // p i} → G) :
    (∑ η : ι → G, if (fun i : {i // p i} => η i.1) = μ then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) ^ Fintype.card {i // ¬ p i} := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => G)
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have hrestrict (x : ({i // p i} → G) × ({i // ¬ p i} → G)) :
      (fun i : {i // p i} => e.symm x i.1) = x.1 := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  simp only [hrestrict]
  simp

variable [Group G]

open Classical in
/-- Given one simultaneous translation, a pair of compatible label assignments
is determined by the second assignment. Both prescribed boundaries agree exactly
when they are related by that translation. -/
theorem sum_translated_boundaryRestriction_eq_card (p : ι → Prop) [DecidablePred p]
    (μ ν : {i // p i} → G) (g : G) :
    (∑ η : ι → G, ∑ θ : ι → G,
      if (fun i : {i // p i} => η i.1) = μ ∧
          (fun i : {i // p i} => θ i.1) = ν ∧ η = (fun i => g * θ i)
      then (1 : ℂ) else 0) =
      if μ = (fun i => g * ν i)
      then (Fintype.card G : ℂ) ^ Fintype.card {i // ¬ p i} else 0 := by
  classical
  rw [Finset.sum_comm]
  have hinner (θ : ι → G) :
      (∑ η : ι → G,
        if (fun i : {i // p i} => η i.1) = μ ∧
            (fun i : {i // p i} => θ i.1) = ν ∧ η = (fun i => g * θ i)
        then (1 : ℂ) else 0) =
        if (fun i : {i // p i} => θ i.1) = ν ∧ μ = (fun i => g * ν i)
        then 1 else 0 := by
    rw [Finset.sum_eq_single (fun i => g * θ i)]
    · by_cases hθ : (fun i : {i // p i} => θ i.1) = ν
      · simp only [hθ, and_true]
        have heq : (fun i : {i // p i} => g * θ i.1) = (fun i => g * ν i) :=
          congrArg (fun x : ({i // p i} → G) => fun i => g * x i) hθ
        simp only [heq, eq_comm, ite_and, ite_true]
      · simp [hθ]
    · intro η _ hη
      simp [hη]
    · simp
  simp only [hinner]
  by_cases hμ : μ = (fun i => g * ν i)
  · simp only [hμ, and_true, ite_true]
    exact sum_boundaryRestriction_eq_card p ν
  · simp [hμ]

open Classical in
/-- Summing over the common translation counts each free internal assignment
once for every translation relating the two fixed boundaries. -/
theorem sum_boundaryRestriction_translations_eq_card (p : ι → Prop) [DecidablePred p]
    (μ ν : {i // p i} → G) :
    (∑ η : ι → G, ∑ θ : ι → G, ∑ g : G,
      if (fun i : {i // p i} => η i.1) = μ ∧
          (fun i : {i // p i} => θ i.1) = ν ∧ η = (fun i => g * θ i)
      then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) ^ Fintype.card {i // ¬ p i} *
        ∑ g : G, if μ = (fun i => g * ν i) then 1 else 0 := by
  classical
  calc
    _ = ∑ η : ι → G, ∑ g : G, ∑ θ : ι → G,
        if (fun i : {i // p i} => η i.1) = μ ∧
            (fun i : {i // p i} => θ i.1) = ν ∧ η = (fun i => g * θ i)
        then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro η _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ η : ι → G, ∑ θ : ι → G,
        if (fun i : {i // p i} => η i.1) = μ ∧
            (fun i : {i // p i} => θ i.1) = ν ∧ η = (fun i => g * θ i)
        then (1 : ℂ) else 0 := Finset.sum_comm
    _ = _ := by
      simp only [sum_translated_boundaryRestriction_eq_card]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp

end Restriction

section Region

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Incident edges that do not cross the boundary are exactly the internal
edges, with both endpoints in the region. -/
def regionInternalEdgeEquiv (R : Finset V) :
    {e : {e : Edge Γ // IsRegionIncidentEdge R e} // ¬ IsRegionBoundaryEdge R e.1} ≃
      {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} where
  toFun e := ⟨e.1.1, by
    have hi := e.1.2
    have hb := e.2
    simp only [IsRegionIncidentEdge, IsRegionBoundaryEdge] at hi hb
    tauto⟩
  invFun e := ⟨⟨e.1, Or.inl e.2.1⟩, by
    simp [IsRegionBoundaryEdge, e.2.1, e.2.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of free incident-edge labels is the number of internal bonds. -/
theorem card_regionIncident_not_boundary (R : Finset V) :
    Fintype.card
      {e : {e : Edge Γ // IsRegionIncidentEdge R e} // ¬ IsRegionBoundaryEdge R e.1} =
      Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} :=
  Fintype.card_congr (regionInternalEdgeEquiv R)

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- Two boundary functions agree exactly when their pullbacks to the boundary
subtype of incident edges agree. Source: SCP10, finite-region contraction,
lines 1935–1957. -/
theorem regionBoundaryLabel_eq_iff (R : Finset V) {H : Type*}
    (μ ν : {e : Edge Γ // IsRegionBoundaryEdge R e} → H) :
    ((fun e : {e : {e : Edge Γ // IsRegionIncidentEdge R e} //
        IsRegionBoundaryEdge R e.1} => μ ⟨e.1.1, e.2⟩) =
      (fun e => ν ⟨e.1.1, e.2⟩)) ↔ μ = ν := by
  constructor
  · intro h
    funext e
    exact congrFun h ⟨⟨e.1, isRegionBoundaryEdge_touches R e.2⟩, e.2⟩
  · intro h
    funext e
    exact congrFun h ⟨e.1.1, e.2⟩

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

open Classical in
/-- Source: SCP10, finite-region contraction, lines 1935–1957. For a common
translation, the two fixed crossing configurations leave precisely one free
group label per internal bond. -/
theorem sum_regionBoundary_translations_eq_card (R : Finset V)
    (μ ν : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    (∑ η : {e : Edge Γ // IsRegionIncidentEdge R e} → G,
      ∑ θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G, ∑ g : G,
      if (fun e : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
          η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = μ ∧
        (fun e : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
          θ ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = ν ∧
        η = (fun e => g * θ e)
      then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) ^ Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} *
        ∑ g : G, if μ = (fun e => g * ν e) then 1 else 0 := by
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
  have h := sum_boundaryRestriction_translations_eq_card p
    (fun e => μ ⟨e.1.1, e.2⟩) (fun e => ν ⟨e.1.1, e.2⟩)
  simp only [hrestrict, htranslation] at h
  rw [card_regionIncident_not_boundary] at h
  exact h

end Region

end TNLean.PEPS
