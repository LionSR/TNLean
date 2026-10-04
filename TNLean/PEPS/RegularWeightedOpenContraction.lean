/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates
/-!
# Actual character-weighted open contractions in original physical coordinates

Scalar bond weights are retained in the original incident-label sum. Applying
one original physical site map at every vertex recovers this weighted sum from
its canonical projector coordinates. Source: SCP10, arXiv:1001.3807,
lines 1765–1820, 2449–2486 and 2569–2581. These are auxiliary contraction
identities; no decomposition of a diagonal weight into group insertions is used.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {d : ℕ}
private abbrev RE (R : Finset V) := {e : Edge Γ // IsRegionIncidentEdge R e}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
/-- The literal weighted open contraction of the original site tensors.
Source: SCP10, lines 2449–2486 and 2569–2581. -/
def regularWeightedOpenRegionWeight
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (u : Edge Γ → G) (F : (RE (Γ := Γ) R → G) → ℂ)
    (θ : RB (Γ := Γ) R → G) (σ : {v : V // v ∈ R} → Fin d) : ℂ :=
  ∑ η : RE (Γ := Γ) R → G,
    if (fun f : RB (Γ := Γ) R =>
      η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ then
      F η * ∏ w : {v : V // v ∈ R}, a w.1
        (regularTwistedLabels u w.1
          (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)) (σ w)
    else 0
/-- The constant unit weight is exactly the existing numbered open contraction.
Source: SCP10, regional contraction, lines 1935–1957. -/
theorem regularWeightedOpenRegionWeight_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (u : Edge Γ → G) (θ : RB (Γ := Γ) R → G) :
    regularWeightedOpenRegionWeight a R u (fun _ => 1) θ =
      openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
        (fun f => Fintype.equivFin G (θ f)) := by
  classical
  funext σ
  unfold openRegionWeight
  rw [← Equiv.sum_comp (regularRegionIncidentConfigEquiv (regularTwistedSite a u) R)]
  unfold regularWeightedOpenRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  simp only [one_mul, regionIncidentBoundaryLabel_regularGroup_iff]
  split_ifs
  · simp only [regionIncidentWeight, groupBondTensor, regularRegionIncidentConfigEquiv,
      Equiv.piCongrRight_apply, Pi.map_apply, Equiv.symm_apply_apply, regularTwistedSite]
  · rfl

/-- The original physical site maps recover every literal weighted contraction.
Source: SCP10, accessible coordinates, lines 1765–1820, and 2569–2581. -/
theorem regionPhysicalMap_regularProjectorWeightedTwistedRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (u : Edge Γ → G) (F : (RE (Γ := Γ) R → G) → ℂ)
    (θ : RB (Γ := Γ) R → G) :
    regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s))
      (fun α => regularProjectorWeightedTwistedRegionMatrix R u F α θ) =
      regularWeightedOpenRegionWeight a R u F θ := by
  classical
  funext σ
  rw [regionPhysicalMap_apply]
  simp only [regularProjectorWeightedTwistedRegionMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold regularWeightedOpenRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  by_cases hb : (fun f : RB (Γ := Γ) R =>
      η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ
  · simp only [hb, ↓reduceIte, Matrix.of_apply]
    simp_rw [mul_left_comm _ (F η)]
    rw [← Finset.mul_sum]
    congr 1
    simp only [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (w : {v : V // v ∈ R}) (β : IncidentEdge Γ w.1 → G) =>
      a w.1 β (σ w) * regularLegProjector (IncidentEdge Γ w.1) β
        (regularTwistedLabels u w.1
          (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩)))]
    apply Finset.prod_congr rfl
    intro w _
    exact (ha w.1).regularSiteMap_projector_coefficients _ _
  · simp only [hb, ↓reduceIte, mul_zero, Finset.sum_const_zero]
end TNLean.PEPS
