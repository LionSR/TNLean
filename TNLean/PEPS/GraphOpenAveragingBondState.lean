/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MonoidHomCommutingWeight
import TNLean.PEPS.GraphOpenRegionContraction
import TNLean.PEPS.GraphAveragingBondState
import TNLean.PEPS.RegularRegionCoordinates
import TNLean.PEPS.RegularProjectorOpenRegion
import TNLean.PEPS.RegionBlock.GaugeInjectivity

/-!
# Actual weighted averaging coefficients of an open graph region

Physical incidences in a region regroup into internal tail-head pairs and one
retained endpoint for each crossing bond. Expanding the local group averages
and summing the actual internal virtual labels gives W²U(q_head q_tail⁻¹)
on internal bonds. A crossing bond instead retains WU(q_tail⁻¹), or U(q_head)W,
with the prescribed virtual boundary label. The boundary labels are arbitrary.
The numbered coefficient theorem identifies the same expression with the
existing open-region contraction after finite physical enumerations.

Source: SCP10, arXiv:1001.3807, regional contraction algebra, lines 1765–1920
and 1935–1957, and Section 7, lines 2977–3019. These are coefficient identities
on finite simple graphs. They do not assert that every regular open-boundary
state has a corresponding minimal-representation open-boundary state.

**Local fix (group-average normalization):** Site averages are divided by |G|,
so the expression has |G|⁻|R|. This convention is documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- The incidence product contains two factors on internal bonds and one on crossing bonds.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem prod_region_incident_eq_internal_boundary (R : Finset V)
    (F : (v : RV R) → IncidentEdge Γ v.1 → ℂ) :
    (∏ v : RV R, ∏ e : IncidentEdge Γ v.1, F v e) =
    (∏ e : RI (Γ := Γ) R,
      F ⟨e.1.1.1, e.2.1⟩ (edgeLeftIncident e.1) *
      F ⟨e.1.1.2, e.2.2⟩ (edgeRightIncident e.1)) *
    (∏ e : RB (Γ := Γ) R,
      if h : e.1.1.1 ∈ R then F ⟨e.1.1.1, h⟩ (edgeLeftIncident e.1)
      else F ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩ (edgeRightIncident e.1)) := by
  classical
  let f : (v : V) → IncidentEdge Γ v → ℂ := fun v e =>
    if h : v ∈ R then F ⟨v, h⟩ e else 1
  have he : (∏ v : RV R, ∏ e : IncidentEdge Γ v.1, F v e) =
      ∏ v : RV R, ∏ e : IncidentEdge Γ v.1, f v.1 e := by
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_congr rfl
    intro e _
    simp only [f, dite_eq_left v.2]
  rw [he, prod_region_incident_eq_prod_edge R f]
  let i : Edge Γ → ℂ := fun e => if h : e.1.1 ∈ R ∧ e.1.2 ∈ R then
    F ⟨e.1.1, h.1⟩ (edgeLeftIncident e) * F ⟨e.1.2, h.2⟩ (edgeRightIncident e) else 1
  let b : Edge Γ → ℂ := fun e => if h : IsRegionBoundaryEdge R e then
    if ht : e.1.1 ∈ R then F ⟨e.1.1, ht⟩ (edgeLeftIncident e)
    else F ⟨e.1.2, (h.resolve_left (fun h' => ht h'.1)).2⟩ (edgeRightIncident e) else 1
  have hk (e : Edge Γ) :
      (if e.1.1 ∈ R then f e.1.1 (edgeLeftIncident e) else 1) *
      (if e.1.2 ∈ R then f e.1.2 (edgeRightIncident e) else 1) = i e * b e := by
    by_cases ht : e.1.1 ∈ R <;> by_cases hh : e.1.2 ∈ R <;>
      simp [i, b, f, IsRegionBoundaryEdge, ht, hh]
  simp_rw [hk]
  rw [Finset.prod_mul_distrib]
  dsimp only [i, b]
  rw [Fintype.prod_dite]
  simp only [Finset.prod_const_one, mul_one]
  rw [Fintype.prod_dite]
  simp only [Finset.prod_const_one, mul_one]

variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]

/-- The coherent bond-coordinate expression, retaining every boundary endpoint factor.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
def graphOpenAveragingBondState (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (θ : RB (Γ := Γ) R → X)
    (β : (RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X) × (RI (Γ := Γ) R → X)) : ℂ :=
      ∑ q : RV R → G, (Fintype.card G : ℂ)⁻¹ ^ R.card *
        ((∏ e : RI (Γ := Γ) R,
          (W ^ 2 * U (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹))
            (β.2.2 e) (β.2.1 e)) *
        (∏ e : RB (Γ := Γ) R, if h : e.1.1.1 ∈ R then
          (W * U ((q ⟨e.1.1.1, h⟩)⁻¹)) (θ e) (β.1 e)
        else (U (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩) * W)
          (β.1 e) (θ e)))

/-- The actual weighted open contraction equals its derived coherent bond expression.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem graphOpenRegionNetwork_dressedAveragingSite_coherent
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (R : Finset V) (θ : RB (Γ := Γ) R → X)
    (α : RegionHalfEdgeConfig (Γ := Γ) X R) :
    graphOpenRegionNetwork (graphDressedAveragingSite U W) R θ α =
      graphOpenAveragingBondState U W R θ (regionHalfEdgeLabelEquiv R α) := by
  classical
  unfold graphOpenAveragingBondState
  rw [graphOpenRegionNetwork_eq_sum_internal]
  simp only [graphDressedAveragingSite, graphDress_averagingSite,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
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
  have hp (ξ : RI (Γ := Γ) R → X) :
      (∏ v : RV R, ∏ f : IncidentEdge Γ v.1,
        if f.1.1.1 = v.1 then
          (W * U (q v)⁻¹) ((graphRegionIncidentConfigEquiv R).symm (ξ, θ)
            ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩) (α v f)
        else (U (q v) * W) (α v f)
          ((graphRegionIncidentConfigEquiv R).symm (ξ, θ)
            ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩)) =
      (∏ e : RI (Γ := Γ) R,
        (W * U (q ⟨e.1.1.1, e.2.1⟩)⁻¹) (ξ e) ((regionHalfEdgeLabelEquiv R α).2.1 e) *
        (U (q ⟨e.1.1.2, e.2.2⟩) * W) ((regionHalfEdgeLabelEquiv R α).2.2 e) (ξ e)) *
      (∏ e : RB (Γ := Γ) R, if h : e.1.1.1 ∈ R then
        (W * U (q ⟨e.1.1.1, h⟩)⁻¹) (θ e) ((regionHalfEdgeLabelEquiv R α).1 e)
      else (U (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩) * W)
        ((regionHalfEdgeLabelEquiv R α).1 e) (θ e)) := by
    rw [prod_region_incident_eq_internal_boundary]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e _
      have hn : ¬ e.1.1.1 = e.1.1.2 := ne_of_lt e.1.2.1
      simp only [edgeLeftIncident, edgeRightIncident, hn, ↓reduceIte]
      simp only [hi, regionHalfEdgeLabelEquiv_apply_internal_tail,
        regionHalfEdgeLabelEquiv_apply_internal_head]
      rfl
    · apply Finset.prod_congr rfl
      intro e _
      by_cases ht : e.1.1.1 ∈ R
      · simp only [dite_eq_left ht, edgeLeftIncident, ↓reduceIte, hb,
          regionHalfEdgeLabelEquiv_apply_boundary_tail R α e ht]
      · have hn : ¬ e.1.1.1 = e.1.1.2 := ne_of_lt e.1.2.1
        have hh : e.1.1.2 ∈ R := (e.2.resolve_left (fun h' => ht h'.1)).2
        simp only [dite_eq_right ht, edgeRightIncident, hn, ↓reduceIte, hb,
          regionHalfEdgeLabelEquiv_apply_boundary_head R α e hh]
  simp_rw [hp]
  rw [← Finset.sum_mul]
  congr 1
  let F : RI (Γ := Γ) R → X → ℂ := fun e j =>
    (W * U (q ⟨e.1.1.1, e.2.1⟩)⁻¹) j ((regionHalfEdgeLabelEquiv R α).2.1 e) *
    (U (q ⟨e.1.1.2, e.2.2⟩) * W) ((regionHalfEdgeLabelEquiv R α).2.2 e) j
  change (∑ ξ : RI (Γ := Γ) R → X, ∏ e, F e (ξ e)) = _
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro e _
  dsimp only [F]
  rw [← U.mul_weight_mul_weight_mul W hc]
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Regrouping the actual physical incidence coordinates gives the bond expression.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem graphOpenBondRegrouping_dressedAveragingSite
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (R : Finset V) (θ : RB (Γ := Γ) R → X)
    (β : (RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X) × (RI (Γ := Γ) R → X)) :
    graphOpenRegionNetwork (graphDressedAveragingSite U W) R θ
      ((regionHalfEdgeLabelEquiv R).symm β) = graphOpenAveragingBondState U W R θ β := by
  simpa only [Equiv.apply_symm_apply] using
    graphOpenRegionNetwork_dressedAveragingSite_coherent U W hc R θ
      ((regionHalfEdgeLabelEquiv R).symm β)

/-- The identity-weight specialization is the actual open averaging-site contraction.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem graphOpenRegionNetwork_averagingSite_coherent (U : G →* Matrix X X ℂ)
    (R : Finset V) (θ : RB (Γ := Γ) R → X)
    (α : RegionHalfEdgeConfig (Γ := Γ) X R) :
    graphOpenRegionNetwork (graphAveragingSite U) R θ α =
      graphOpenAveragingBondState U 1 R θ (regionHalfEdgeLabelEquiv R α) := by
  have hs : graphDressedAveragingSite (Γ := Γ) U 1 = graphAveragingSite U := by
    funext v η σ
    exact graphDress_one v (fun ξ => graphAveragingSite U v ξ σ) η
  simpa only [hs] using graphOpenRegionNetwork_dressedAveragingSite_coherent
    U 1 (fun _ => Commute.one_left _) R θ α

/-- Finite physical enumerations give the literal numbered open-region coefficient.
Source: SCP10, lines 1765–1920 and 1935–1957, and Section 7, lines 2977–3019. -/
theorem openRegionWeight_groupBondTensor_dressedAveragingSite {d : ℕ}
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin d)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) (σ : RegionPhysicalConfig (d := d) R) :
    openRegionWeight (groupBondTensor (fun v η s =>
      graphDressedAveragingSite U W v η ((e v).symm s))) R
        (fun f => Fintype.equivFin X (θ f)) σ =
      graphOpenAveragingBondState U W R θ
        (regionHalfEdgeLabelEquiv R (fun v => (e v.1).symm (σ v))) := by
  rw [openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork]
  exact graphOpenRegionNetwork_dressedAveragingSite_coherent U W hc R θ
    (fun v => (e v.1).symm (σ v))
end TNLean.PEPS
