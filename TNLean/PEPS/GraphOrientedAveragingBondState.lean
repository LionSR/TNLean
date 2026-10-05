/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphCanonicalBondCoordinates

/-!
# Open averaging contractions with arbitrary native edge orientations

An independent Boolean flag reverses each edge relative to the auxiliary vertex
order. One representation acts uniformly on all native directed edges. Physical
bond coordinates remain ordered head-tail pairs; reversing a native edge reverses
both its relative group element and the order of its physical matrix indices.
Every open virtual boundary label is retained, and finite physical numbering
identifies the derived column span with the actual regional PEPS range.

Source: SCP10, arXiv:1001.3807, regional contraction algebra, lines 1765–1920
and 1935–1957, and Section 7, lines 2977–3019. This orientation extension does
not introduce link-dependent representations or require a symmetric weight.

**Local fix (group-average normalization):** Each site average is divided by
|G|, as documented in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- The native tail is the ordered first endpoint unless the orientation flag
reverses the edge. Source: SCP10, Section 7, lines 2977–3019. -/
def graphNativeTail (o : Edge Γ → Bool) (v : V) (f : IncidentEdge Γ v) : Prop :=
  if o f.1 then f.1.1.2 = v else f.1.1.1 = v

instance (o : Edge Γ → Bool) (v : V) (f : IncidentEdge Γ v) :
    Decidable (graphNativeTail o v f) := by unfold graphNativeTail; infer_instance

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- The ordered first endpoint is the native tail exactly when its edge is
not reversed. Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem graphNativeTail_edgeLeftIncident (o : Edge Γ → Bool) (e : Edge Γ) :
    graphNativeTail o e.1.1 (edgeLeftIncident e) ↔ o e = false := by
  cases ho : o e <;>
    simp [graphNativeTail, edgeLeftIncident, ho, ne_of_gt e.2.1]

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- The ordered second endpoint is the native tail exactly when its edge is
reversed. Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem graphNativeTail_edgeRightIncident (o : Edge Γ → Bool) (e : Edge Γ) :
    graphNativeTail o e.1.2 (edgeRightIncident e) ↔ o e = true := by
  cases ho : o e <;>
    simp [graphNativeTail, edgeRightIncident, ho, ne_of_lt e.2.1]

variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]

/-- The normalized group average uses WU(g⁻¹) at each native tail and U(g)W
at each native head. Source: SCP10, Section 7, lines 2977–3019. -/
def graphOrientedAveragingSite (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) (η σ : IncidentEdge Γ v → X) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ∏ f : IncidentEdge Γ v,
    if graphNativeTail o v f then (W * U g⁻¹) (η f) (σ f)
    else (U g * W) (σ f) (η f)

/-- With no reversed edges this is exactly the existing virtual dressing,
without any transposition assumption on W. Source: SCP10, Section 7. -/
@[simp] theorem graphOrientedAveragingSite_false (U : G →* Matrix X X ℂ)
    (W : Matrix X X ℂ) :
    graphOrientedAveragingSite (Γ := Γ) U W (fun _ => false) =
      graphDressedAveragingSite U W := by
  funext v η σ
  simp only [graphOrientedAveragingSite, graphNativeTail, Bool.false_eq_true, ↓reduceIte,
    graphDressedAveragingSite, graphDress_averagingSite]

/-- The retained endpoint on a crossing bond, with its fixed virtual boundary
index and its native orientation. Source: SCP10, Section 7, lines 2977–3019. -/
def graphOrientedOpenBoundaryFactor (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (o : Edge Γ → Bool) (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R)
    (θ x : X) : ℂ :=
  if h : e.1.1.1 ∈ R then
    if o e.1 then (U (q ⟨e.1.1.1, h⟩) * W) x θ
    else (W * U (q ⟨e.1.1.1, h⟩)⁻¹) θ x
  else
    if o e.1 then
      (W * U (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩)⁻¹) θ x
    else (U (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩) * W) x θ

/-- An internal native edge in the existing ordered (head, tail) physical
coordinates. A reversed edge swaps both indices and the relative group element.
Source: SCP10, Section 7, lines 2977–3019. -/
def graphOrientedOpenInternalFactor (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (o : Edge Γ → Bool) (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R)
    (x : X × X) : ℂ :=
  if o e.1 then
    (W ^ 2 * U (q ⟨e.1.1.1, e.2.1⟩ * (q ⟨e.1.1.2, e.2.2⟩)⁻¹)) x.2 x.1
  else (W ^ 2 * U (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹)) x.1 x.2

/-- The open contraction in crossing-endpoint and ordered internal-pair
coordinates. Source: SCP10, Section 7, lines 2977–3019. -/
def graphOrientedOpenBondCoordinates (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (o : Edge Γ → Bool) (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    ((RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) → ℂ :=
  fun β => ∑ q : RV R → G, (Fintype.card G : ℂ)⁻¹ ^ R.card *
    ((∏ e : RI (Γ := Γ) R, graphOrientedOpenInternalFactor U W o R q e (β.2 e)) *
      ∏ e : RB (Γ := Γ) R, graphOrientedOpenBoundaryFactor U W o R q e (θ e) (β.1 e))

/-- Separate boundary and internal factors of every coherent group assignment.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphOrientedOpenBondCoordinates_eq_sum_prod
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (o : Edge Γ → Bool)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    graphOrientedOpenBondCoordinates U W o R θ = fun β => ∑ q : RV R → G,
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        (∏ e : RB (Γ := Γ) R, graphOrientedOpenBoundaryFactor U W o R q e (θ e) (β.1 e)) *
        ∏ e : RI (Γ := Γ) R, graphOrientedOpenInternalFactor U W o R q e (β.2 e) := by
  funext β
  unfold graphOrientedOpenBondCoordinates
  apply Finset.sum_congr rfl
  intro q _
  exact (mul_assoc _ _ _).symm.trans (mul_right_comm _ _ _)

/-- Expanding the actual open contraction gives the native oriented edge
factors with arbitrary virtual boundary data. Source: SCP10, regional
contractions and Section 7, lines 2977–3019. -/
theorem graphOpenRegionNetwork_orientedAveragingSite_coherent
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (R : Finset V) (θ : RB (Γ := Γ) R → X)
    (α : RegionHalfEdgeConfig (Γ := Γ) X R) :
    graphOpenRegionNetwork (graphOrientedAveragingSite U W o) R θ α =
      graphOrientedOpenBondCoordinates U W o R θ
        ((regionHalfEdgeLabelEquiv R α).1,
          fun e => ((regionHalfEdgeLabelEquiv R α).2.2 e,
            (regionHalfEdgeLabelEquiv R α).2.1 e)) := by
  classical
  unfold graphOrientedOpenBondCoordinates
  rw [graphOpenRegionNetwork_eq_sum_internal]
  simp only [graphOrientedAveragingSite, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.mul_sum]
  congr 1
  have hi (ξ : RI (Γ := Γ) R → X) (e : RI (Γ := Γ) R) :
      (graphRegionIncidentConfigEquiv R).symm (ξ, θ) ⟨e.1, Or.inl e.2.1⟩ = ξ e := by
    rw [← graphRegionIncidentConfigEquiv_apply_internal R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, θ)) e, Equiv.apply_symm_apply]
  have hb (ξ : RI (Γ := Γ) R → X) (e : RB (Γ := Γ) R) :
      (graphRegionIncidentConfigEquiv R).symm (ξ, θ)
        ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩ = θ e := by
    rw [← graphRegionIncidentConfigEquiv_apply_boundary R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, θ)) e, Equiv.apply_symm_apply]
  let F : RI (Γ := Γ) R → X → ℂ := fun e j =>
    if o e.1 then
      (U (q ⟨e.1.1.1, e.2.1⟩) * W) ((regionHalfEdgeLabelEquiv R α).2.1 e) j *
      (W * U (q ⟨e.1.1.2, e.2.2⟩)⁻¹) j ((regionHalfEdgeLabelEquiv R α).2.2 e)
    else
      (W * U (q ⟨e.1.1.1, e.2.1⟩)⁻¹) j ((regionHalfEdgeLabelEquiv R α).2.1 e) *
      (U (q ⟨e.1.1.2, e.2.2⟩) * W) ((regionHalfEdgeLabelEquiv R α).2.2 e) j
  have hp (ξ : RI (Γ := Γ) R → X) :
      (∏ v : RV R, ∏ f : IncidentEdge Γ v.1,
        if graphNativeTail o v.1 f then
          (W * U (q v)⁻¹) ((graphRegionIncidentConfigEquiv R).symm (ξ, θ)
            ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) (α v f)
        else (U (q v) * W) (α v f)
          ((graphRegionIncidentConfigEquiv R).symm (ξ, θ)
            ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩)) =
      (∏ e : RI (Γ := Γ) R, F e (ξ e)) *
      (∏ e : RB (Γ := Γ) R,
        graphOrientedOpenBoundaryFactor U W o R q e (θ e)
          ((regionHalfEdgeLabelEquiv R α).1 e)) := by
    rw [prod_region_incident_eq_internal_boundary]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e _
      have hn : ¬ e.1.1.1 = e.1.1.2 := ne_of_lt e.1.2.1
      have hn' : ¬ e.1.1.2 = e.1.1.1 := fun h => hn h.symm
      cases ho : o e.1 <;>
        simp only [graphNativeTail, edgeLeftIncident, edgeRightIncident, ho,
          Bool.false_eq_true, ↓reduceIte, hn, hn', hi, F,
          regionHalfEdgeLabelEquiv_apply_internal_tail,
          regionHalfEdgeLabelEquiv_apply_internal_head]
    · apply Finset.prod_congr rfl
      intro e _
      have hn : ¬ e.1.1.1 = e.1.1.2 := ne_of_lt e.1.2.1
      have hn' : ¬ e.1.1.2 = e.1.1.1 := fun h => hn h.symm
      by_cases ht : e.1.1.1 ∈ R
      · cases ho : o e.1 <;>
          simp only [dite_eq_left ht, graphOrientedOpenBoundaryFactor, graphNativeTail,
            edgeLeftIncident, ho, Bool.false_eq_true, hn', ↓reduceIte, hb,
            regionHalfEdgeLabelEquiv_apply_boundary_tail R α e ht]
      · have hh : e.1.1.2 ∈ R := (e.2.resolve_left (fun h' => ht h'.1)).2
        cases ho : o e.1 <;>
          simp only [dite_eq_right ht, graphOrientedOpenBoundaryFactor, graphNativeTail,
            edgeRightIncident, ho, Bool.false_eq_true, hn, ↓reduceIte, hb,
            regionHalfEdgeLabelEquiv_apply_boundary_head R α e hh]
  simp_rw [hp]
  rw [← Finset.sum_mul]
  congr 1
  change (∑ ξ : RI (Γ := Γ) R → X, ∏ e, F e (ξ e)) = _
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro e _
  cases ho : o e.1
  · simp only [F, graphOrientedOpenInternalFactor, ho, Bool.false_eq_true, ↓reduceIte]
    rw [← U.mul_weight_mul_weight_mul W hc]
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [F, graphOrientedOpenInternalFactor, ho, ↓reduceIte]
    rw [← U.mul_weight_mul_weight_mul W hc]
    rfl

/-- Regrouping the actual physical incidences preserves the existing ordered
bond coordinates. Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphOpenBondRegrouping_orientedAveragingSite
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (R : Finset V) (θ : RB (Γ := Γ) R → X)
    (β : (RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) :
    graphOpenRegionNetwork (graphOrientedAveragingSite U W o) R θ
      ((regionHalfEdgeLabelEquiv R).symm
        (β.1, (fun e => (β.2 e).2), fun e => (β.2 e).1)) =
      graphOrientedOpenBondCoordinates U W o R θ β := by
  simpa only [Equiv.apply_symm_apply] using
    graphOpenRegionNetwork_orientedAveragingSite_coherent U W hc o R θ
      ((regionHalfEdgeLabelEquiv R).symm
        (β.1, (fun e => (β.2 e).2), fun e => (β.2 e).1))

/-- Numbering the physical alphabet gives the actual oriented graph tensor.
Source: SCP10, Section 7, lines 2977–3019. -/
def numberedGraphOrientedAveragingTensor {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (o : Edge Γ → Bool)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) : Tensor Γ p :=
  groupBondTensor (fun v η s => graphOrientedAveragingSite U W o v η ((e v).symm s))

/-- The literal numbered open-region coefficient has the derived oriented
bond expression. Source: SCP10, Section 7, lines 2977–3019. -/
theorem openRegionWeight_numberedGraphOrientedAveragingTensor {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) (σ : RegionPhysicalConfig (d := p) R) :
    openRegionWeight (numberedGraphOrientedAveragingTensor U W o e) R
      (fun f => Fintype.equivFin X (θ f)) σ =
      graphOrientedOpenBondCoordinates U W o R θ (regionBondConfigEquiv e R σ) := by
  unfold numberedGraphOrientedAveragingTensor
  rw [openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork]
  exact graphOpenRegionNetwork_orientedAveragingSite_coherent U W hc o R θ
    (fun v => (e v.1).symm (σ v))

/-- All boundary columns span the oriented open-region range in the unchanged
ordered physical coordinates. Source: SCP10, Theorem 5.7 and Section 7. -/
def graphOrientedOpenBondSpace (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (o : Edge Γ → Bool) (R : Finset V) :
    Submodule ℂ (((RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) → ℂ) :=
  Submodule.span ℂ (Set.range (graphOrientedOpenBondCoordinates U W o R))

/-- Regrouping each literal boundary column gives its oriented bond
coordinates. Source: SCP10, Theorem 5.7 and Section 7. -/
theorem regionBondPhysicalEquiv_openRegionWeight_oriented {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    regionBondPhysicalEquiv e R
      (openRegionWeight (numberedGraphOrientedAveragingTensor U W o e) R
        (fun f => Fintype.equivFin X (θ f))) = graphOrientedOpenBondCoordinates U W o R θ := by
  funext β
  change openRegionWeight (numberedGraphOrientedAveragingTensor U W o e) R
    (fun f => Fintype.equivFin X (θ f)) ((regionBondConfigEquiv e R).symm β) = _
  rw [openRegionWeight_numberedGraphOrientedAveragingTensor U W hc,
    Equiv.apply_symm_apply]

/-- The oriented column span is exactly the genuine numbered regional PEPS
range, including every virtual boundary condition. Source: SCP10, Theorem 5.7
and Section 7, lines 2977–3019. -/
theorem map_regionGroundSpace_eq_graphOrientedOpenBondSpace {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) :
    (regionGroundSpace (numberedGraphOrientedAveragingTensor U W o e) R).map
      (regionBondPhysicalEquiv e R).toLinearMap = graphOrientedOpenBondSpace U W o R := by
  rw [regionGroundSpace_eq_span, Submodule.map_span]
  unfold graphOrientedOpenBondSpace
  congr 1
  ext φ
  constructor
  · rintro ⟨_, ⟨μ, rfl⟩, rfl⟩
    let θ : RB (Γ := Γ) R → X := fun f => (Fintype.equivFin X).symm (μ f)
    refine ⟨θ, ?_⟩
    have hμ : (fun f => Fintype.equivFin X (θ f)) = μ := by
      funext f
      exact Equiv.apply_symm_apply _ _
    simpa only [hμ, LinearEquiv.coe_coe] using
      (regionBondPhysicalEquiv_openRegionWeight_oriented U W hc o e R θ).symm
  · rintro ⟨θ, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, regionBondPhysicalEquiv_openRegionWeight_oriented U W hc o e R θ⟩

/-- Membership in the genuine regional range is characterized by its
oriented bond-coordinate vector. Source: SCP10, Theorem 5.7 and Section 7. -/
theorem regionBondPhysicalEquiv_mem_graphOrientedOpenBondSpace_iff {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (o : Edge Γ → Bool) (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (ψ : RegionPhysicalConfig (d := p) R → ℂ) :
    regionBondPhysicalEquiv e R ψ ∈ graphOrientedOpenBondSpace U W o R ↔
      ψ ∈ regionGroundSpace (numberedGraphOrientedAveragingTensor U W o e) R := by
  rw [← map_regionGroundSpace_eq_graphOrientedOpenBondSpace U W hc o e R]
  constructor
  · rintro ⟨φ, hφ, hEq⟩
    exact (regionBondPhysicalEquiv e R).injective hEq ▸ hφ
  · intro hψ
    exact ⟨ψ, hψ, rfl⟩

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Keeping the ordered orientation recovers the previous boundary factor.
Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem graphOrientedOpenBoundaryFactor_false
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (R : Finset V)
    (q : RV R → G) (e : RB (Γ := Γ) R) (θ x : X) :
    graphOrientedOpenBoundaryFactor U W (fun _ => false) R q e θ x =
      graphOpenBoundaryFactor U W R q e θ x := by
  simp only [graphOrientedOpenBoundaryFactor, graphOpenBoundaryFactor,
    Bool.false_eq_true, ↓reduceIte]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Keeping the ordered orientation recovers the previous internal factor.
Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem graphOrientedOpenInternalFactor_false
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (R : Finset V)
    (q : RV R → G) (e : RI (Γ := Γ) R) (x : X × X) :
    graphOrientedOpenInternalFactor U W (fun _ => false) R q e x =
      graphOpenInternalFactor U W R q e x := rfl

/-- With every native edge ordered, the bond-coordinate expression is the
previous open contraction. Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem graphOrientedOpenBondCoordinates_false
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    graphOrientedOpenBondCoordinates U W (fun _ => false) R θ =
      graphOpenBondCoordinates U W R θ := by
  rw [graphOrientedOpenBondCoordinates_eq_sum_prod, graphOpenBondCoordinates_eq_sum_prod]
  simp only [graphOrientedOpenBoundaryFactor_false, graphOrientedOpenInternalFactor_false]

/-- The numbered orientation extension recovers the existing tensor when no
edge is reversed. Source: SCP10, Section 7, lines 2977–3019. -/
@[simp] theorem numberedGraphOrientedAveragingTensor_false {p : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) :
    numberedGraphOrientedAveragingTensor U W (fun _ => false) e =
      numberedGraphDressedAveragingTensor U W e := by
  simp only [numberedGraphOrientedAveragingTensor, numberedGraphDressedAveragingTensor,
    graphOrientedAveragingSite_false]

/-- The ordered special case has exactly the previous regional bond range.
Source: SCP10, Theorem 5.7 and Section 7, lines 2977–3019. -/
@[simp] theorem graphOrientedOpenBondSpace_false
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (R : Finset V) :
    graphOrientedOpenBondSpace (Γ := Γ) U W (fun _ => false) R =
      graphOpenBondSpace U W R := by
  exact congrArg (fun f => Submodule.span ℂ (Set.range f))
    (funext fun θ => graphOrientedOpenBondCoordinates_false U W R θ)

end TNLean.PEPS
