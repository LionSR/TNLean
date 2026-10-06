/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteIndicatorSum
import TNLean.PEPS.RegularProjectorOpenRegion
import TNLean.PEPS.RegularTwistedRegion

/-!
# Canonical projector coordinates for actual twisted regular regions

An oriented regular-bond operator multiplies the label at the larger endpoint.
The canonical physical row remains the original family's incident half-edge
coordinates. The same local physical maps expose these coordinates and recover
the original contracted tensor for every choice of bond operators, including
operators on crossing bonds. No connectedness or region Gram identity is used.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`eq:2d:peps-with-ug-uh` and Observation `obs:iso:accessible-virt`,
`Papers/1001.3807/paper_v3.tex`, lines 1515–1525 and 1765–1820.

**Local fix (normalization):** The normalized adjoint is divided by the positive
site factor allowed by `IsGIsometric`, as documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The canonical region matrix after insertion of arbitrary oriented regular
bond operators. Its physical rows are the original incident half-edge labels.
Source: SCP10, lines 1515–1525 and 1765–1820. -/
noncomputable def regularProjectorTwistedRegionMatrix (R : Finset V) (u : Edge Γ → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      ({f : Edge Γ // IsRegionBoundaryEdge R f} → G) ℂ :=
  fun α θ => ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
    if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ then
      ∏ w : {w : V // w ∈ R},
        regularLegProjector (IncidentEdge Γ w.1) (α w)
          (regularTwistedLabels u w.1
            (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩))
    else 0

/-- Identity operators recover the original canonical open-region matrix. -/
theorem regularProjectorTwistedRegionMatrix_one (R : Finset V) :
    regularProjectorTwistedRegionMatrix (Γ := Γ) (G := G) R (fun _ => 1) =
      regularProjectorOpenRegionMatrix R := by
  have hlabels (v : V) (η : IncidentEdge Γ v → G) :
      regularTwistedLabels (fun _ => 1) v η = η := by
    funext f
    simp only [regularTwistedLabels, one_mul, ite_self]
  funext α θ
  simp only [regularProjectorTwistedRegionMatrix, regularProjectorOpenRegionMatrix, hlabels]

/-- The actual twisted canonical coefficients have the original local-average
normalization and one translation label per vertex. Source: SCP10,
`obs:iso:accessible-virt`, lines 1765–1820. -/
theorem regularProjectorTwistedRegionMatrix_apply (R : Finset V) (u : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorTwistedRegionMatrix R u α θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card *
        ∑ η : {f : Edge Γ // IsRegionIncidentEdge R f} → G,
          ∑ q : {w : V // w ∈ R} → G,
            if (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
                  η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ ∧
                (∀ w : {w : V // w ∈ R}, α w = q w •
                  regularTwistedLabels u w.1
                    (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩))
            then 1 else 0 := by
  classical
  unfold regularProjectorTwistedRegionMatrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hb : (fun f : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ
  · simp only [hb, ↓reduceIte, true_and]
    simp only [regularLegProjector_apply, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    congr 1
    exact Fintype.prod_sum_boole _
  · simp only [hb, ↓reduceIte, false_and, Finset.sum_const_zero, mul_zero]

variable {d : ℕ}

/-- The original local physical inverse exposes canonical projector coordinates
for every twist assignment, without any condition on crossing bonds.
Source: SCP10, lines 1515–1525 and 1765–1820. -/
theorem regionPhysicalMap_eq_regularProjectorTwistedRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (u : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regionPhysicalMap R F (openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
      (fun f => Fintype.equivFin G (θ f))) α =
      regularProjectorTwistedRegionMatrix R u α θ := by
  classical
  rw [regionPhysicalMap_openRegionWeight,
    ← Equiv.sum_comp (regularRegionIncidentConfigEquiv (regularTwistedSite a u) R)]
  unfold regularProjectorTwistedRegionMatrix
  apply Finset.sum_congr rfl
  intro η _
  simp only [regionIncidentBoundaryLabel_regularGroup_iff]
  split_ifs
  · apply Finset.prod_congr rfl
    intro w _
    simpa only [groupBondTensor, regularRegionIncidentConfigEquiv,
      Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply, regularTwistedSite] using
      hF w.1 (α w) (regularTwistedLabels u w.1
        (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩))
  · rfl

/-- Recovering the original physical coefficients reverses the canonical
coordinate map for every twist. Source: SCP10, lines 1515–1525 and 1765–1820.
Only the original site's G-injectivity is used. -/
theorem regionPhysicalMap_regularProjectorTwistedRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (u : Edge Γ → G)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s))
      (fun α => regularProjectorTwistedRegionMatrix R u α θ) =
      openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
        (fun f => Fintype.equivFin G (θ f)) := by
  classical
  choose F hF using fun v => (ha v).exists_regularProjectorCoefficients
  let A (v : V) : Matrix (Fin d) (IncidentEdge Γ v → G) ℂ :=
    Matrix.of (fun s α => a v α s)
  have hFA (v : V) : F v * A v = regularLegProjector (IncidentEdge Γ v) := by
    ext α η
    exact hF v α η
  have hAP (v : V) : A v * regularLegProjector (IncidentEdge Γ v) = A v := by
    ext s η
    exact (ha v).regularSiteMap_projector_coefficients s η
  have hAFA (v : V) : (A v * F v) * A v = A v := by
    rw [Matrix.mul_assoc, hFA, hAP]
  have hforward : regionPhysicalMap R F
      (openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
        (fun f => Fintype.equivFin G (θ f))) =
      fun α => regularProjectorTwistedRegionMatrix R u α θ := by
    funext α
    exact regionPhysicalMap_eq_regularProjectorTwistedRegionMatrix a F hF R u α θ
  rw [← hforward]
  change (regionPhysicalMap R A ∘ₗ regionPhysicalMap R F) _ = _
  rw [regionPhysicalMap_comp]
  funext σ
  rw [regionPhysicalMap_openRegionWeight]
  unfold openRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · unfold regionIncidentWeight
    apply Finset.prod_congr rfl
    intro w _
    change ((A w.1 * F w.1) * A w.1) (σ w)
      (regularTwistedLabels u w.1 (fun f => (Fintype.equivFin G).symm
        (η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩))) = _
    rw [hAFA]
    rfl
  · rfl

/-- A regular G-injective family has one collection of local physical inverse
matrices that exposes every twisted canonical region. This is an algebraic
extension of SCP10's accessibility argument, without a unitary assertion. -/
theorem exists_regularProjectorTwistedRegionMatrix_of_isGInjective
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) :
    ∃ F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ,
      ∀ (R : Finset V) (u : Edge Γ → G)
        (α : RegionHalfEdgeConfig (Γ := Γ) G R)
        (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G),
      regionPhysicalMap R F
        (openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
          (fun f => Fintype.equivFin G (θ f))) α =
        regularProjectorTwistedRegionMatrix R u α θ := by
  classical
  choose F hF using fun v => (ha v).exists_regularProjectorCoefficients
  exact ⟨F, fun R u α θ =>
    regionPhysicalMap_eq_regularProjectorTwistedRegionMatrix a F hF R u α θ⟩

/-- All twists share the same normalized local-adjoint physical maps.
Source: SCP10, `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem exists_regularProjectorTwistedRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) :
    ∃ c : V → ℝ, (∀ v, 0 < c v) ∧ ∀ (R : Finset V) (u : Edge Γ → G)
      (α : RegionHalfEdgeConfig (Γ := Γ) G R)
      (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G),
      regionPhysicalMap R (fun v α s => (c v : ℂ)⁻¹ * star (a v α s))
        (openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
          (fun f => Fintype.equivFin G (θ f))) α =
        regularProjectorTwistedRegionMatrix R u α θ := by
  classical
  choose c hc h using fun v => (ha v).exists_regularProjectorCoefficients
  refine ⟨c, hc, fun R u α θ => ?_⟩
  exact regionPhysicalMap_eq_regularProjectorTwistedRegionMatrix a _ h R u α θ

end TNLean.PEPS
