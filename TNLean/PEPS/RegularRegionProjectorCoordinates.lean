/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.PEPS.RegularRegionCoordinates
import TNLean.PEPS.RegularProjectorOpenRegion

/-!
# Canonical blocked-region coefficients in spanning-tree coordinates

The actual open-region contraction of regular averaging-projector sites has a simple
form after the reversible spanning-tree change of physical basis. Its boundary
factor is the simultaneous regular projector. Internal reference labels and normalized
vertex labels are unrestricted, while every residual cycle label is the identity.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, accessible virtual coordinates
and regular blocking, `Papers/1001.3807/paper_v3.tex`, lines 1765–1920. The coefficient
formula is derived from the original internal-bond summation; no factorization is assumed.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private abbrev Vertex (R : Finset V) := {v : V // v ∈ R}
private abbrev BlockInternal (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev Incident (R : Finset V) := {e : Edge Γ // IsRegionIncidentEdge R e}
private abbrev BlockBoundary (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_of_incident_not_internal (R : Finset V) (e : Incident (Γ := Γ) R)
    (hi : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R)) : IsRegionBoundaryEdge R e.1 := by
  rcases e.2 with ht | hh
  · exact Or.inl ⟨ht, fun h => hi ⟨ht, h⟩⟩
  · exact Or.inr ⟨fun h => hi ⟨h, hh⟩, hh⟩

private def referenceConfig (R : Finset V)
    (y : BlockBoundary (Γ := Γ) R → G) (a : BlockInternal (Γ := Γ) R → G) :
    Incident (Γ := Γ) R → G := fun e =>
  if hi : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R then a ⟨e.1, hi⟩
  else y ⟨e.1, boundary_of_incident_not_internal R e hi⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem referenceConfig_internal (R : Finset V)
    (y : BlockBoundary (Γ := Γ) R → G) (a : BlockInternal (Γ := Γ) R → G)
    (e : BlockInternal (Γ := Γ) R) :
    referenceConfig R y a ⟨e.1, Or.inl e.2.1⟩ = a e := by
  simp only [referenceConfig, dite_eq_left e.2]

omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem referenceConfig_boundary (R : Finset V)
    (y : BlockBoundary (Γ := Γ) R → G) (a : BlockInternal (Γ := Γ) R → G)
    (e : BlockBoundary (Γ := Γ) R) :
    referenceConfig R y a ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩ = y e := by
  have hi : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
    rcases e.2 with h | h
    · exact fun hi => h.2 hi.2
    · exact fun hi => h.1 hi.1
  simp only [referenceConfig, dite_eq_right hi]

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] [Fintype G] in
/-- Compatibility on the chosen spanning tree fixes every vertex translation
up to its value at the root. Source: SCP10, the regular blocking construction,
lines 1840–1920. No compatibility condition on cycle or boundary edges is needed. -/
theorem regularRegionCoordinates_rootLabels_of_tree_compatibility [Finite G] (R : Finset V)
    (T : SimpleGraph ({v : V // v ∈ R}))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : {e : Edge Γ // IsRegionIncidentEdge R e} → G) (q : {v : V // v ∈ R} → G)
    (hα : ∀ e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R},
      T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩ →
        c.2.2.1.1 ⟨e.1.1.1, e.2.1⟩ * c.2.1 e =
          q ⟨e.1.1.1, e.2.1⟩ * η ⟨e.1, Or.inl e.2.1⟩ ∧
        c.2.2.1.1 ⟨e.1.1.2, e.2.2⟩ * c.2.1 e =
          q ⟨e.1.1.2, e.2.2⟩ * η ⟨e.1, Or.inl e.2.1⟩) :
    ∀ w, q w = c.2.2.1.1 w * q o := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let p : RootedGroupLabels (G := G) o :=
    ⟨fun w => q w * (q o)⁻¹, by simp⟩
  have hp : p = c.2.2.1 := by
    apply (rootedTreeGradientEquiv T htree o).injective
    funext e
    let f : BlockInternal (Γ := Γ) R :=
      ⟨⟨(e.1.1.1, e.1.2.1), e.2.1, hT e.2.2⟩, e.1.1.2, e.1.2.2⟩
    have he : T.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩ := e.2.2
    obtain ⟨ht, hh⟩ := hα f he
    change (q e.1.2 * (q o)⁻¹) * (q e.1.1 * (q o)⁻¹)⁻¹ =
      c.2.2.1.1 e.1.2 * (c.2.2.1.1 e.1.1)⁻¹
    calc
      _ = q e.1.2 * (q e.1.1)⁻¹ := by group
      _ = (q e.1.2 * η ⟨f.1, Or.inl f.2.1⟩) *
          (q e.1.1 * η ⟨f.1, Or.inl f.2.1⟩)⁻¹ := by group
      _ = (c.2.2.1.1 e.1.2 * c.2.1 f) *
          (c.2.2.1.1 e.1.1 * c.2.1 f)⁻¹ := by rw [← hh, ← ht]
      _ = _ := by group
  intro w
  have hw := congrArg (fun s : RootedGroupLabels (G := G) o => s.1 w) hp
  exact (mul_inv_eq_iff_eq_mul).mp hw

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem compatible_root_labels (R : Finset V)
    (T : SimpleGraph (Vertex R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : Incident (Γ := Γ) R → G) (q : Vertex R → G)
    (hα : ∀ w (f : IncidentEdge Γ w.1),
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
        q w * η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) :
    ∀ w, q w = c.2.2.1.1 w * q o := by
  apply regularRegionCoordinates_rootLabels_of_tree_compatibility R T hT htree o c η q
  intro e he
  have ht := hα ⟨e.1.1.1, e.2.1⟩ ⟨e.1, Or.inl rfl⟩
  have hh := hα ⟨e.1.1.2, e.2.2⟩ ⟨e.1, Or.inr rfl⟩
  rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c e] at ht
  rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c e] at hh
  simp only [dite_eq_left he, mul_one] at hh
  exact ⟨ht, hh⟩

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem reconstruction_of_cycle_one (R : Finset V)
    (T : SimpleGraph (Vertex R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (hz : c.2.2.2 = 1) (w : Vertex R) (f : IncidentEdge Γ w.1) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
      c.2.2.1.1 w * referenceConfig R c.1 c.2.1
        ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩ := by
  rcases w with ⟨v, hv⟩
  rcases f with ⟨e, hf⟩
  rcases hf with ht | hh
  · change e.1.1 = v at ht
    subst v
    by_cases hi : e.1.2 ∈ R
    · rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c ⟨e, hv, hi⟩,
        referenceConfig_internal R c.1 c.2.1 ⟨e, hv, hi⟩]
    · rw [regularRegionCoordinatesEquiv_symm_boundary_tail R T hT htree o c e hv hi,
        referenceConfig_boundary R c.1 c.2.1 ⟨e, Or.inl ⟨hv, hi⟩⟩]
  · change e.1.2 = v at hh
    subst v
    by_cases hi : e.1.1 ∈ R
    · have he := regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c ⟨e, hi, hv⟩
      simp only [hz, Pi.one_apply, dite_eq_ite, ite_self, mul_one] at he
      rw [he, referenceConfig_internal R c.1 c.2.1 ⟨e, hi, hv⟩]
    · rw [regularRegionCoordinatesEquiv_symm_boundary_head R T hT htree o c e hi hv,
        referenceConfig_boundary R c.1 c.2.1 ⟨e, Or.inr ⟨hi, hv⟩⟩]

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem compatible_cycle_one (R : Finset V)
    (T : SimpleGraph (Vertex R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : Incident (Γ := Γ) R → G) (q : Vertex R → G)
    (hα : ∀ w (f : IncidentEdge Γ w.1),
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
        q w * η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) :
    c.2.2.2 = 1 := by
  have hr := compatible_root_labels R T hT htree o c η q hα
  funext e
  change c.2.2.2 e = 1
  have ht := hα ⟨e.1.1.1.1, e.1.2.1⟩ ⟨e.1.1, Or.inl rfl⟩
  have hh := hα ⟨e.1.1.1.2, e.1.2.2⟩ ⟨e.1.1, Or.inr rfl⟩
  rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c e.1] at ht
  rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c e.1] at hh
  simp only [dite_eq_right e.2] at hh
  rw [hr] at ht hh
  simp only [mul_assoc] at ht hh
  have hz : c.2.2.2 e * c.2.1 e.1 = c.2.1 e.1 :=
    (mul_left_cancel hh).trans (mul_left_cancel ht).symm
  exact mul_right_cancel (hz.trans (one_mul _).symm)

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem compatible_reference_eq (R : Finset V)
    (T : SimpleGraph (Vertex R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : Vertex R)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : Incident (Γ := Γ) R → G) (q : Vertex R → G)
    (hα : ∀ w (f : IncidentEdge Γ w.1),
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
        q w * η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) :
    η = fun e => (q o)⁻¹ * referenceConfig R c.1 c.2.1 e := by
  have hr := compatible_root_labels R T hT htree o c η q hα
  have hz := compatible_cycle_one R T hT htree o c η q hα
  funext e
  rcases e.2 with ht | hh
  · have h := hα ⟨e.1.1.1, ht⟩ ⟨e.1, Or.inl rfl⟩
    rw [reconstruction_of_cycle_one R T hT htree o c hz, hr, mul_assoc] at h
    exact eq_inv_mul_iff_mul_eq.mpr (mul_left_cancel h).symm
  · have h := hα ⟨e.1.1.2, hh⟩ ⟨e.1, Or.inr rfl⟩
    rw [reconstruction_of_cycle_one R T hT htree o c hz, hr, mul_assoc] at h
    exact eq_inv_mul_iff_mul_eq.mpr (mul_left_cancel h).symm

private theorem projector_matrix_apply_pointwise (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) (θ : BlockBoundary (Γ := Γ) R → G) :
    regularProjectorOpenRegionMatrix R α θ = (Fintype.card G : ℂ)⁻¹ ^ R.card *
      ∑ p : (Incident (Γ := Γ) R → G) × (Vertex R → G),
        if (fun e : BlockBoundary (Γ := Γ) R =>
              p.1 ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ ∧
            (∀ w (e : IncidentEdge Γ w.1),
              α w e = p.2 w * p.1 ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)
        then 1 else 0 := by
  classical
  rw [regularProjectorOpenRegionMatrix_apply, Fintype.sum_prod_type]
  apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ R.card * ·)
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro q _
  have hlocal : (∀ w : Vertex R,
      α w = q w • (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩)) ↔
      ∀ w (e : IncidentEdge Γ w.1),
        α w e = q w * η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩ := by
    simp only [funext_iff, Pi.smul_apply, smul_eq_mul]
  simp only [hlocal]

/-- The actual canonical blocked tensor factors in spanning-tree physical coordinates.
The boundary factor is the regular projector, all reference and normalized vertex
labels are unrestricted, and all residual cycle labels must be the identity.
Source: SCP10, accessible virtual coordinates and blocking, lines 1765–1920. -/
theorem regularProjectorOpenRegionMatrix_coordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ) * (Fintype.card G : ℂ)⁻¹ ^ R.card *
        regularLegProjector {e : Edge Γ // IsRegionBoundaryEdge R e} c.1 θ *
        (if c.2.2.2 = 1 then 1 else 0) := by
  classical
  let P (p : (Incident (Γ := Γ) R → G) × (Vertex R → G)) : Prop :=
    (fun e : BlockBoundary (Γ := Γ) R =>
        p.1 ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ ∧
      ∀ w (f : IncidentEdge Γ w.1),
        (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
          p.2 w * p.1 ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩
  let f : G → (Incident (Γ := Γ) R → G) × (Vertex R → G) := fun x =>
    (fun e => x⁻¹ * referenceConfig R c.1 c.2.1 e, fun w => c.2.2.1.1 w * x)
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun p => p.2 o) hxy
    change c.2.2.1.1 o * x = c.2.2.1.1 o * y at h
    exact mul_left_cancel h
  have hPx (x : G) : P (f x) ↔ c.2.2.2 = 1 ∧ c.1 = x • θ := by
    constructor
    · intro h
      refine ⟨compatible_cycle_one R T hT htree o c (f x).1 (f x).2 h.2, ?_⟩
      funext e
      have he := congrFun h.1 e
      change x⁻¹ * referenceConfig R c.1 c.2.1
        ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩ = θ e at he
      rw [referenceConfig_boundary R c.1 c.2.1 e] at he
      exact inv_mul_eq_iff_eq_mul.mp he
    · rintro ⟨hz, hy⟩
      constructor
      · funext e
        change x⁻¹ * referenceConfig R c.1 c.2.1
          ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩ = θ e
        rw [referenceConfig_boundary R c.1 c.2.1 e]
        have he := congrFun hy e
        change c.1 e = x * θ e at he
        rw [he]
        group
      · intro w e
        rw [reconstruction_of_cycle_one R T hT htree o c hz]
        change c.2.2.1.1 w * referenceConfig R c.1 c.2.1 _ =
          (c.2.2.1.1 w * x) * (x⁻¹ * referenceConfig R c.1 c.2.1 _)
        group
  have hsum : (∑ p, if P p then (1 : ℂ) else 0) =
      ∑ x : G, if c.2.2.2 = 1 ∧ c.1 = x • θ then 1 else 0 := by
    refine (Fintype.sum_of_injective f hf _ _ ?_ ?_).symm
    · intro p hp
      by_cases h : P p
      · have hη := compatible_reference_eq R T hT htree o c p.1 p.2 h.2
        have hq := compatible_root_labels R T hT htree o c p.1 p.2 h.2
        have he : f (p.2 o) = p := Prod.ext hη.symm (funext hq).symm
        exact (hp ⟨p.2 o, he⟩).elim
      · simp only [h, ↓reduceIte]
    · intro x
      simp only [hPx x]
  have hmatrix : regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ p, if P p then (1 : ℂ) else 0 := by
    exact projector_matrix_apply_pointwise R _ θ
  rw [hmatrix, hsum]
  by_cases hz : c.2.2.2 = 1
  · simp only [hz, ↓reduceIte, true_and, mul_one]
    rw [regularLegProjector_apply, ← mul_assoc]
    have hκ : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [mul_right_comm (Fintype.card G : ℂ), mul_inv_cancel₀ hκ, one_mul]
  · simp only [hz, ↓reduceIte, false_and, Finset.sum_const_zero, mul_zero]

/-- In spanning-tree physical coordinates, the actual canonical matrix is a positive
multiple of the boundary projector tensored with one normalized ancillary vector.
Source: SCP10, regular blocking and its ancillary factors, lines 1840–1920. -/
theorem regularProjectorOpenRegionMatrix_exists_normalized_ancilla (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R}) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ φ :
      (({e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G) ×
        RootedGroupLabels (G := G) o ×
        ({e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
          ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G)) → ℂ,
      ∑ a, ∑ r, ∑ z, star (φ (a, r, z)) * φ (a, r, z) = 1 ∧
        ∀ (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
        (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        regularProjectorOpenRegionMatrix R
            ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
          (γ : ℂ) * regularLegProjector {e : Edge Γ // IsRegionBoundaryEdge R e} c.1 θ *
            φ c.2 := by
  classical
  let A := (BlockInternal (Γ := Γ) R → G) × RootedGroupLabels (G := G) o
  let _ : Nonempty (RootedGroupLabels (G := G) o) := ⟨⟨1, rfl⟩⟩
  have hN : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let b := Real.sqrt (Fintype.card A : ℝ)
  have hb : 0 < b := Real.sqrt_pos.mpr hN
  let β : ℂ := (b : ℂ)⁻¹
  let φ := fun s : (BlockInternal (Γ := Γ) R → G) ×
      RootedGroupLabels (G := G) o ×
      ({e : BlockInternal (Γ := Γ) R //
        ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G) =>
    β * (if s.2.2 = 1 then 1 else 0)
  have hβ : star β = β := by simp [β]
  have hββ : β * β = (Fintype.card A : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_natCast] using
      Complex.ofReal_sqrt_inv_mul_self (Fintype.card A : ℝ) hN.le
  have hnorm : ∑ a, ∑ r, ∑ z, star (φ (a, r, z)) * φ (a, r, z) = 1 := by
    simp only [φ]
    simp only [star_mul, hβ, apply_ite, star_one, star_zero]
    simp only [ite_mul, mul_one, mul_zero, zero_mul]
    simp only [Fintype.sum_ite_eq', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod]
    simp only [↓reduceIte, one_mul, hββ]
    exact mul_inv_cancel₀
      (show (Fintype.card A : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let γ : ℝ := (Fintype.card G : ℝ) * (Fintype.card G : ℝ)⁻¹ ^ R.card * b
  have hκ : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨γ, mul_pos (mul_pos hκ (pow_pos (inv_pos.mpr hκ) _)) hb, φ, hnorm, ?_⟩
  intro c θ
  rw [regularProjectorOpenRegionMatrix_coordinates R T hT htree o c θ]
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hbβ : (b : ℂ) * β = 1 := mul_inv_cancel₀ hb0
  dsimp only [γ]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_natCast, φ]
  by_cases hz : c.2.2.2 = 1
  · simp only [hz, ↓reduceIte, mul_one]
    calc
      _ = ((Fintype.card G : ℂ) * (Fintype.card G : ℂ)⁻¹ ^ R.card) *
          regularLegProjector {e : Edge Γ // IsRegionBoundaryEdge R e} c.1 θ *
          ((b : ℂ) * β) := by rw [hbβ, mul_one]
      _ = _ := by ring
  · simp only [hz, ↓reduceIte, mul_zero]

end TNLean.PEPS
