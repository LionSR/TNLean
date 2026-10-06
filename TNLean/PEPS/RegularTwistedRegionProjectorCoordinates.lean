/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionProjectorCoordinates
import TNLean.PEPS.RegularRegionTreeGauge
import TNLean.PEPS.RegularProjectorTwistedRegion

/-!
# Actual twisted block coefficients in spanning-tree coordinates

The tree gauge determines the translations in the original canonical contraction.
The residual operators constrain the cycle coordinates by simultaneous conjugation;
operators on crossing bonds transport the boundary labels. The formula below retains
the original half-edge physical coordinates and the original internal-bond sum.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, lines 1765–1920 and 1935–1990.
No flatness, boundary invariance, or factorization is assumed.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RE (R : Finset V) := {e : Edge Γ // IsRegionIncidentEdge R e}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem root_translations (R : Finset V)
    (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (u : Edge Γ → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : RE (Γ := Γ) R → G) (q : RV R → G)
    (hα : ∀ w (f : IncidentEdge Γ w.1),
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
        q w * regularTwistedLabels u w.1
          (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) f) :
    ∀ w, q w = c.2.2.1.1 w * q o *
      ((regularRegionTreeGauge R T hT htree o u).1 w)⁻¹ := by
  let k := (regularRegionTreeGauge R T hT htree o u).1
  have hr := regularRegionCoordinates_rootLabels_of_tree_compatibility
    R T hT htree o c
    (fun e => if ht : e.1.1.1 ∈ R then (k ⟨e.1.1.1, ht⟩)⁻¹ * η e else η e)
    (fun w => q w * k w) (by
      intro e he
      have ht := hα ⟨e.1.1.1, e.2.1⟩ ⟨e.1, Or.inl rfl⟩
      have hh := hα ⟨e.1.1.2, e.2.2⟩ ⟨e.1, Or.inr rfl⟩
      rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c e] at ht
      rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c e] at hh
      have hne : e.1.1.1 ≠ e.1.1.2 := ne_of_lt e.1.2.1
      simp only [regularTwistedLabels, ite_eq_right hne] at ht
      simp only [regularTwistedLabels, dite_eq_left he, mul_one] at hh
      simp only [dite_eq_left e.2.1]
      have hk : k ⟨e.1.1.2, e.2.2⟩ * (k ⟨e.1.1.1, e.2.1⟩)⁻¹ = u e.1 :=
        regularRegionTreeGauge_gradient R T hT htree o u e he
      constructor
      · calc
          _ = q ⟨e.1.1.1, e.2.1⟩ * η ⟨e.1, Or.inl e.2.1⟩ := ht
          _ = _ := by group
      · calc
          _ = q ⟨e.1.1.2, e.2.2⟩ * (u e.1 * η ⟨e.1, Or.inl e.2.1⟩) := hh
          _ = _ := by rw [← hk]; group)
  intro w
  have h := hr w
  have hkroot : k o = 1 := regularRegionTreeGauge_root R T hT htree o u
  rw [hkroot, mul_one] at h
  exact eq_mul_inv_iff_mul_eq.mpr h

private def reference (R : Finset V) (u : Edge Γ → G) (k : RV R → G)
    (y : RB (Γ := Γ) R → G) (a : RI (Γ := Γ) R → G) (x : G) :
    RE (Γ := Γ) R → G := fun e =>
  if ht : e.1.1.1 ∈ R then
    k ⟨e.1.1.1, ht⟩ * x⁻¹ *
      (if hh : e.1.1.2 ∈ R then a ⟨e.1, ht, hh⟩ else y ⟨e.1, Or.inl ⟨ht, hh⟩⟩)
  else
    (u e.1)⁻¹ * k ⟨e.1.1.2, e.2.resolve_left ht⟩ * x⁻¹ *
      y ⟨e.1, Or.inr ⟨ht, e.2.resolve_left ht⟩⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem reference_internal (R : Finset V) (u : Edge Γ → G) (k : RV R → G)
    (y : RB (Γ := Γ) R → G) (a : RI (Γ := Γ) R → G) (x : G)
    (e : RI (Γ := Γ) R) :
    reference R u k y a x ⟨e.1, Or.inl e.2.1⟩ =
      k ⟨e.1.1.1, e.2.1⟩ * x⁻¹ * a e := by
  simp only [reference, dite_eq_left e.2.1, dite_eq_left e.2.2]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem reference_boundary_tail (R : Finset V) (u : Edge Γ → G) (k : RV R → G)
    (y : RB (Γ := Γ) R → G) (a : RI (Γ := Γ) R → G) (x : G)
    (e : Edge Γ) (ht : e.1.1 ∈ R) (hh : e.1.2 ∉ R) :
    reference R u k y a x ⟨e, Or.inl ht⟩ = k ⟨e.1.1, ht⟩ * x⁻¹ * y ⟨e, Or.inl ⟨ht, hh⟩⟩ := by
  simp only [reference, dite_eq_left ht, dite_eq_right hh]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem reference_boundary_head (R : Finset V) (u : Edge Γ → G) (k : RV R → G)
    (y : RB (Γ := Γ) R → G) (a : RI (Γ := Γ) R → G) (x : G)
    (e : Edge Γ) (ht : e.1.1 ∉ R) (hh : e.1.2 ∈ R) :
    reference R u k y a x ⟨e, Or.inr hh⟩ =
      (u e)⁻¹ * k ⟨e.1.2, hh⟩ * x⁻¹ * y ⟨e, Or.inr ⟨ht, hh⟩⟩ := by
  simp only [reference, dite_eq_right ht]

omit [Fintype G] [DecidableEq G] in
private theorem solve_translation (r x k a η : G)
    (h : r * a = (r * x * k⁻¹) * η) : η = k * x⁻¹ * a := by
  calc
    η = (r * x * k⁻¹)⁻¹ * (r * a) := eq_inv_mul_iff_mul_eq.mpr h.symm
    _ = _ := by group

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem compatible_reference (R : Finset V)
    (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (u : Edge Γ → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : RE (Γ := Γ) R → G) (q : RV R → G)
    (hα : ∀ w (f : IncidentEdge Γ w.1),
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
        q w * regularTwistedLabels u w.1
          (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) f) :
    η = reference R u (regularRegionTreeGauge R T hT htree o u).1 c.1 c.2.1 (q o) := by
  let k := (regularRegionTreeGauge R T hT htree o u).1
  have hr := root_translations R T hT htree o u c η q hα
  funext e
  by_cases ht : e.1.1.1 ∈ R
  · have h := hα ⟨e.1.1.1, ht⟩ ⟨e.1, Or.inl rfl⟩
    have hne : e.1.1.1 ≠ e.1.1.2 := ne_of_lt e.1.2.1
    simp only [regularTwistedLabels, ite_eq_right hne] at h
    rw [hr] at h
    by_cases hh : e.1.1.2 ∈ R
    · rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c ⟨e.1, ht, hh⟩]
        at h
      rw [reference_internal R u k c.1 c.2.1 (q o) ⟨e.1, ht, hh⟩]
      exact solve_translation _ _ _ _ _ h
    · rw [regularRegionCoordinatesEquiv_symm_boundary_tail R T hT htree o c e.1 ht hh] at h
      rw [reference_boundary_tail R u k c.1 c.2.1 (q o) e.1 ht hh]
      exact solve_translation _ _ _ _ _ h
  · have hh : e.1.1.2 ∈ R := e.2.resolve_left ht
    have h := hα ⟨e.1.1.2, hh⟩ ⟨e.1, Or.inr rfl⟩
    simp only [regularTwistedLabels, ↓reduceIte] at h
    rw [hr, regularRegionCoordinatesEquiv_symm_boundary_head R T hT htree o c e.1 ht hh]
      at h
    rw [reference_boundary_head R u k c.1 c.2.1 (q o) e.1 ht hh]
    have hs := solve_translation _ _ _ _ _ h
    calc
      _ = (u e.1)⁻¹ * (u e.1 * η e) := by group
      _ = _ := by rw [hs]; dsimp only [k]; group

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem compatible_cycles (R : Finset V)
    (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (u : Edge Γ → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (η : RE (Γ := Γ) R → G) (q : RV R → G)
    (hα : ∀ w (f : IncidentEdge Γ w.1),
      (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
        q w * regularTwistedLabels u w.1
          (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) f) :
    c.2.2.2 = fun e => q o * regularRegionTreeCycleResidual R T hT htree o u e * (q o)⁻¹ := by
  have hr := root_translations R T hT htree o u c η q hα
  have hη := compatible_reference R T hT htree o u c η q hα
  funext e
  have h := hα ⟨e.1.1.1.2, e.1.2.2⟩ ⟨e.1.1, Or.inr rfl⟩
  rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c e.1] at h
  simp only [dite_eq_right e.2, regularTwistedLabels, ↓reduceIte] at h
  rw [hr, hη, reference_internal] at h
  have hright :
      (c.2.2.1.1 ⟨e.1.1.1.2, e.1.2.2⟩ * q o *
        ((regularRegionTreeGauge R T hT htree o u).1 ⟨e.1.1.1.2, e.1.2.2⟩)⁻¹) *
          (u e.1.1 * ((regularRegionTreeGauge R T hT htree o u).1
            ⟨e.1.1.1.1, e.1.2.1⟩ * (q o)⁻¹ * c.2.1 e.1)) =
      c.2.2.1.1 ⟨e.1.1.1.2, e.1.2.2⟩ *
        ((q o * regularRegionTreeCycleResidual R T hT htree o u e * (q o)⁻¹) * c.2.1 e.1) := by
    simp only [regularRegionTreeCycleResidual, regularRegionGaugeResidual]
    group
  rw [hright] at h
  exact mul_right_cancel (mul_left_cancel (by simpa only [mul_assoc] using h))

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem reference_boundary_iff (R : Finset V) (u : Edge Γ → G) (k : RV R → G)
    (y θ : RB (Γ := Γ) R → G) (a : RI (Γ := Γ) R → G) (x : G) :
    (fun e : RB (Γ := Γ) R => reference R u k y a x
      ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ ↔
        y = x • regularRegionBoundaryTransport R k u θ := by
  constructor
  · intro h
    funext e
    rcases e with ⟨e, he⟩
    rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · have he := congrFun h ⟨e, Or.inl ⟨ht, hh⟩⟩
      rw [reference_boundary_tail R u k y a x e ht hh] at he
      change y ⟨e, Or.inl ⟨ht, hh⟩⟩ = x * regularRegionBoundaryTransport R k u θ _
      rw [regularRegionBoundaryTransport_tail R k u θ e ht hh]
      calc
        _ = x * (k ⟨e.1.1, ht⟩)⁻¹ *
            (k ⟨e.1.1, ht⟩ * x⁻¹ * y ⟨e, Or.inl ⟨ht, hh⟩⟩) := by group
        _ = _ := by rw [he]; group
    · have he := congrFun h ⟨e, Or.inr ⟨ht, hh⟩⟩
      rw [reference_boundary_head R u k y a x e ht hh] at he
      change y ⟨e, Or.inr ⟨ht, hh⟩⟩ = x * regularRegionBoundaryTransport R k u θ _
      rw [regularRegionBoundaryTransport_head R k u θ e ht hh]
      calc
        _ = x * (k ⟨e.1.2, hh⟩)⁻¹ * u e *
            ((u e)⁻¹ * k ⟨e.1.2, hh⟩ * x⁻¹ * y ⟨e, Or.inr ⟨ht, hh⟩⟩) := by group
        _ = _ := by rw [he]; group
  · intro h
    funext e
    rcases e with ⟨e, he⟩
    rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · have he := congrFun h ⟨e, Or.inl ⟨ht, hh⟩⟩
      change y _ = x * regularRegionBoundaryTransport R k u θ _ at he
      rw [reference_boundary_tail R u k y a x e ht hh, he,
        regularRegionBoundaryTransport_tail R k u θ e ht hh]
      group
    · have he := congrFun h ⟨e, Or.inr ⟨ht, hh⟩⟩
      change y _ = x * regularRegionBoundaryTransport R k u θ _ at he
      rw [reference_boundary_head R u k y a x e ht hh, he,
        regularRegionBoundaryTransport_head R k u θ e ht hh]
      group

omit [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] in
private theorem reconstruct_compatible (R : Finset V)
    (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (u : Edge Γ → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) (x : G)
    (hz : c.2.2.2 = fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹)
    (w : RV R) (f : IncidentEdge Γ w.1) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm c w f =
      (c.2.2.1.1 w * x * ((regularRegionTreeGauge R T hT htree o u).1 w)⁻¹) *
        regularTwistedLabels u w.1
          (fun e => reference R u (regularRegionTreeGauge R T hT htree o u).1 c.1 c.2.1 x
            ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) f := by
  let k := (regularRegionTreeGauge R T hT htree o u).1
  rcases w with ⟨v, hv⟩
  rcases f with ⟨e, ht | hh⟩
  · change e.1.1 = v at ht
    subst v
    have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2.1
    simp only [regularTwistedLabels, ite_eq_right hne]
    by_cases hi : e.1.2 ∈ R
    · rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c ⟨e, hv, hi⟩,
        reference_internal R u k c.1 c.2.1 x ⟨e, hv, hi⟩]
      dsimp only [k]
      group
    · rw [regularRegionCoordinatesEquiv_symm_boundary_tail R T hT htree o c e hv hi,
        reference_boundary_tail R u k c.1 c.2.1 x e hv hi]
      dsimp only [k]
      group
  · change e.1.2 = v at hh
    subst v
    simp only [regularTwistedLabels, ↓reduceIte]
    by_cases hi : e.1.1 ∈ R
    · let f : RI (Γ := Γ) R := ⟨e, hi, hv⟩
      rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c f,
        reference_internal R u k c.1 c.2.1 x f]
      dsimp only [f]
      by_cases he : T.Adj ⟨e.1.1, hi⟩ ⟨e.1.2, hv⟩
      · simp only [dite_eq_left he, mul_one]
        have hk : k ⟨e.1.2, hv⟩ * (k ⟨e.1.1, hi⟩)⁻¹ = u e :=
          regularRegionTreeGauge_gradient R T hT htree o u f he
        rw [← hk]
        dsimp only [k]
        group
      · simp only [dite_eq_right he]
        rw [congrFun hz ⟨f, he⟩]
        simp only [regularRegionTreeCycleResidual, regularRegionGaugeResidual]
        dsimp only [f, k]
        group
    · rw [regularRegionCoordinatesEquiv_symm_boundary_head R T hT htree o c e hi hv,
        reference_boundary_head R u k c.1 c.2.1 x e hi hv]
      dsimp only [k]
      group

private theorem matrix_apply_pointwise (R : Finset V) (u : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) (θ : RB (Γ := Γ) R → G) :
    regularProjectorTwistedRegionMatrix R u α θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        ∑ p : (RE (Γ := Γ) R → G) × (RV R → G),
          if (fun e : RB (Γ := Γ) R => p.1 ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ ∧
            (∀ w (f : IncidentEdge Γ w.1), α w f = p.2 w *
              regularTwistedLabels u w.1
                (fun e => p.1 ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) f)
          then 1 else 0 := by
  classical
  rw [regularProjectorTwistedRegionMatrix_apply, Fintype.sum_prod_type]
  apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ R.card * ·)
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro q _
  simp only [funext_iff, Pi.smul_apply, smul_eq_mul]

/-- The actual twisted canonical block, in the original spanning-tree physical
coordinates, is a sum over one common translation. Crossing operators transport
its boundary labels, and its cycle labels are simultaneous conjugates of the
residual operators. Source: SCP10, lines 1765–1920 and 1935–1990. -/
theorem regularProjectorTwistedRegionMatrix_coordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (u : Edge Γ → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R u
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
        if c.1 = x • regularRegionBoundaryTransport R
            (regularRegionTreeGauge R T hT htree o u).1 u θ ∧
          c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹)
        then 1 else 0 := by
  classical
  let k := (regularRegionTreeGauge R T hT htree o u).1
  let P (p : (RE (Γ := Γ) R → G) × (RV R → G)) : Prop :=
    (fun e : RB (Γ := Γ) R => p.1 ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) = θ ∧
      ∀ w (f : IncidentEdge Γ w.1),
        (regularRegionCoordinatesEquiv R T hT htree o).symm c w f = p.2 w *
          regularTwistedLabels u w.1
            (fun e => p.1 ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) f
  let f : G → (RE (Γ := Γ) R → G) × (RV R → G) := fun x =>
    (reference R u k c.1 c.2.1 x, fun w => c.2.2.1.1 w * x * (k w)⁻¹)
  have hroot (x : G) : (f x).2 o = x := by
    simp only [f, k, c.2.2.1.2, regularRegionTreeGauge_root, one_mul, inv_one, mul_one]
  have hf : Function.Injective f := by
    intro x y h
    simpa only [hroot] using congrArg (fun p => p.2 o) h
  have hPx (x : G) : P (f x) ↔
      c.1 = x • regularRegionBoundaryTransport R k u θ ∧
        c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹) := by
    constructor
    · intro h
      refine ⟨(reference_boundary_iff R u k c.1 θ c.2.1 x).mp h.1, ?_⟩
      simpa only [hroot] using compatible_cycles R T hT htree o u c (f x).1 (f x).2 h.2
    · rintro ⟨hy, hz⟩
      exact ⟨(reference_boundary_iff R u k c.1 θ c.2.1 x).mpr hy,
        reconstruct_compatible R T hT htree o u c x hz⟩
  have hsum : (∑ p, if P p then (1 : ℂ) else 0) = ∑ x : G,
      if c.1 = x • regularRegionBoundaryTransport R k u θ ∧
        c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹)
      then 1 else 0 := by
    refine (Fintype.sum_of_injective f hf _ _ ?_ ?_).symm
    · intro p hp
      by_cases h : P p
      · have hη := compatible_reference R T hT htree o u c p.1 p.2 h.2
        have hq := root_translations R T hT htree o u c p.1 p.2 h.2
        have he : f (p.2 o) = p := Prod.ext hη.symm (funext hq).symm
        exact (hp ⟨p.2 o, he⟩).elim
      · simp only [h, ↓reduceIte]
    · intro x
      simp only [hPx x]
  have hmatrix : regularProjectorTwistedRegionMatrix R u
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
        (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ p, if P p then (1 : ℂ) else 0 :=
    matrix_apply_pointwise R u _ θ
  rw [hmatrix, hsum]

end TNLean.PEPS
