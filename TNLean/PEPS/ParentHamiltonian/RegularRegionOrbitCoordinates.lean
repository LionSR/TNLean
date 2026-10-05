/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionCommutingConstraints

/-!
# Internal quotients and boundary references of a regular region

Each internal edge contributes its oriented head-to-tail quotient and one
reference label. A boundary edge contributes only its label at the regional
endpoint. These coordinates retain the actual dangling boundary legs.

Source: SCP10, arXiv:1001.3807, accessible regular coordinates,
lines 1765–1920, and the two-dimensional commutation claim, lines 2131–2153.
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The internal edges of the original region. -/
abbrev RegularRegionInternalEdge (R : Finset V) :=
  {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}

/-- Extend internal quotients by the identity on every other original edge. -/
def regularRegionInternalExtension (R : Finset V)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G) : Edge Γ → G :=
  fun e => if h : e.1.1 ∈ R ∧ e.1.2 ∈ R then u ⟨e, h⟩ else 1

/-- Half-edge labels reconstructed from internal quotients and one reference
on each incident edge. Boundary labels are not identified with one another. -/
def regularRegionHalfEdgesOfBonds (R : Finset V)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    RegionHalfEdgeConfig (Γ := Γ) G R :=
  fun v => regularTwistedLabels (regularRegionInternalExtension R u) v.1
    (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩)

/-- The head-to-tail quotient on the original internal edges. -/
def regularRegionHalfEdgeQuotients (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) : RegularRegionInternalEdge (Γ := Γ) R → G :=
  fun e => α ⟨e.1.1.2, e.2.2⟩ ⟨e.1, Or.inr rfl⟩ *
    (α ⟨e.1.1.1, e.2.1⟩ ⟨e.1, Or.inl rfl⟩)⁻¹

/-- Reference at the tail when it belongs to the region, and otherwise at
the head. -/
def regularRegionHalfEdgeReferences (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    {e : Edge Γ // IsRegionIncidentEdge R e} → G :=
  fun e => if h : e.1.1.1 ∈ R then α ⟨e.1.1.1, h⟩ ⟨e.1, Or.inl rfl⟩
    else α ⟨e.1.1.2, e.2.resolve_left h⟩ ⟨e.1, Or.inr rfl⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- The internal tail label is the reference label. -/
theorem regularRegionHalfEdgesOfBonds_tail (R : Finset V)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G)
    (e : Edge Γ) (h : e.1.1 ∈ R) :
    regularRegionHalfEdgesOfBonds R u η ⟨e.1.1, h⟩ ⟨e, Or.inl rfl⟩ =
      η ⟨e, Or.inl h⟩ := by
  simp only [regularRegionHalfEdgesOfBonds, regularTwistedLabels,
    ne_of_lt e.2.1, ↓reduceIte]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- The internal head label is the quotient times the reference. -/
theorem regularRegionHalfEdgesOfBonds_head (R : Finset V)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G)
    (e : RegularRegionInternalEdge (Γ := Γ) R) :
    regularRegionHalfEdgesOfBonds R u η ⟨e.1.1.2, e.2.2⟩ ⟨e.1, Or.inr rfl⟩ =
      u e * η ⟨e.1, Or.inr e.2.2⟩ := by
  simp only [regularRegionHalfEdgesOfBonds, regularTwistedLabels, ↓reduceIte,
    regularRegionInternalExtension, dite_eq_left e.2]

/-- Internal quotients and incident reference labels parametrize all actual
regional half-edge configurations bijectively. -/
def regularRegionHalfEdgeConfigEquiv (R : Finset V) :
    ((RegularRegionInternalEdge (Γ := Γ) R → G) ×
      ({e : Edge Γ // IsRegionIncidentEdge R e} → G)) ≃
        RegionHalfEdgeConfig (Γ := Γ) G R where
  toFun p := regularRegionHalfEdgesOfBonds R p.1 p.2
  invFun α := (regularRegionHalfEdgeQuotients R α, regularRegionHalfEdgeReferences R α)
  left_inv p := by
    apply Prod.ext
    · funext e
      simp only [regularRegionHalfEdgeQuotients, regularRegionHalfEdgesOfBonds_head,
        regularRegionHalfEdgesOfBonds_tail, mul_inv_cancel_right]
    · funext e
      dsimp only [regularRegionHalfEdgeReferences]
      split_ifs with h
      · exact regularRegionHalfEdgesOfBonds_tail R p.1 p.2 e.1 h
      · simp only [regularRegionHalfEdgesOfBonds, regularTwistedLabels, ↓reduceIte,
          regularRegionInternalExtension, h, false_and, ↓reduceDIte, one_mul]
  right_inv α := by
    dsimp only
    funext v e
    rcases v with ⟨v, hv⟩
    rcases e with ⟨e, ht | hh⟩
    · change e.1.1 = v at ht
      subst v
      rw [regularRegionHalfEdgesOfBonds_tail]
      simp only [regularRegionHalfEdgeReferences, dite_eq_left hv]
    · change e.1.2 = v at hh
      subst v
      by_cases ht : e.1.1 ∈ R
      · rw [regularRegionHalfEdgesOfBonds_head R _ _ ⟨e, ht, hv⟩]
        simp only [regularRegionHalfEdgeQuotients, regularRegionHalfEdgeReferences, ht,
          ↓reduceDIte, inv_mul_cancel_right]
      · simp only [regularRegionHalfEdgesOfBonds, regularTwistedLabels, ↓reduceIte,
          regularRegionInternalExtension, ht, false_and, ↓reduceDIte, one_mul,
          regularRegionHalfEdgeReferences]

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_of_incident_not_internal (R : Finset V)
    (e : {e : Edge Γ // IsRegionIncidentEdge R e})
    (h : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R)) : IsRegionBoundaryEdge R e.1 := by
  rcases e.2 with ht | hh
  · exact Or.inl ⟨ht, fun hh => h ⟨ht, hh⟩⟩
  · exact Or.inr ⟨fun ht => h ⟨ht, hh⟩, hh⟩

/-- Identity reference on internal edges, with the given boundary references. -/
def regularRegionCanonicalReferences (R : Finset V)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    {e : Edge Γ // IsRegionIncidentEdge R e} → G :=
  fun e => if h : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R then 1
    else θ ⟨e.1, boundary_of_incident_not_internal R e h⟩

/-- The original boundary restriction of an incident reference assignment. -/
def regularRegionReferenceBoundary (R : Finset V)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    {e : Edge Γ // IsRegionBoundaryEdge R e} → G :=
  fun e => η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Right translations on internal edges change the references freely and leave
all boundary references unchanged. -/
theorem regularRegionHalfEdgesOfBonds_right_normalize (R : Finset V)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    regularRegionHalfEdgeRightMul R
        (fun e => if h : e.1.1 ∈ R ∧ e.1.2 ∈ R then η ⟨e, Or.inl h.1⟩ else 1)
        (regularRegionHalfEdgesOfBonds R u
          (regularRegionCanonicalReferences R (regularRegionReferenceBoundary R η))) =
      regularRegionHalfEdgesOfBonds R u η := by
  funext v e
  simp only [regularRegionHalfEdgeRightMul, regularRegionHalfEdgesOfBonds,
    regularTwistedLabels, regularRegionCanonicalReferences, regularRegionReferenceBoundary]
  split_ifs <;> simp only [mul_one, one_mul]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Right-invariant functions depend only on the internal quotients and the
unchanged boundary references. -/
theorem regularRegionHalfEdgesOfBonds_apply_of_rightInvariant (R : Finset V)
    (f : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ)
    (hf : ∀ r : Edge Γ → G, (∀ e, IsRegionBoundaryEdge R e → r e = 1) →
      ∀ α, f (regularRegionHalfEdgeRightMul R r α) = f α)
    (u : RegularRegionInternalEdge (Γ := Γ) R → G)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    f (regularRegionHalfEdgesOfBonds R u η) =
      f (regularRegionHalfEdgesOfBonds R u
        (regularRegionCanonicalReferences R (regularRegionReferenceBoundary R η))) := by
  rw [← regularRegionHalfEdgesOfBonds_right_normalize R u η]
  apply hf
  intro e he
  have hn : ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R) := by
    rcases he with he | he
    · exact fun hi => he.2 hi.2
    · exact fun hi => he.1 hi.1
  simp only [hn, ↓reduceDIte]

end TNLean.PEPS
