/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Regular.RegularTwistedRegionProjectorCoordinates
import TNLean.PEPS.Injectivity.Charge.RegularEdgeChargeContraction

/-!
# Actual character-weighted open contractions in original physical coordinates

Scalar bond weights are retained in the original incident-label sum. Applying
one original physical site map at every vertex recovers this weighted sum from
its canonical projector coordinates. Source: SCP10, arXiv:1001.3807,
lines 1765–1820, 2449–2486 and 2569–2581. These are auxiliary contraction
identities; no decomposition of a diagonal weight into group insertions is used.

## A literal weighted contraction is the actual charge-inserted tensor network

Source: SCP10, arXiv:1001.3807, diagonal charge insertion, lines 2432–2453,
and `eq:anyons:chargeon-move-setting`, lines 2489–2507.
-/

section

open ManyBody (Edge)
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {d : ℕ}
private abbrev RE (R : Finset V) := {e : Edge Γ // ManyBody.IsRegionIncidentEdge R e}
private abbrev RB (R : Finset V) := {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e}
/-- The literal weighted open contraction of the original site tensors.
Source: SCP10, lines 2449–2486 and 2569–2581. -/
def regularWeightedOpenRegionWeight
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (u : Edge Γ → G) (F : (RE (Γ := Γ) R → G) → ℂ)
    (θ : RB (Γ := Γ) R → G) (σ : {v : V // v ∈ R} → Fin d) : ℂ :=
  ∑ η : RE (Γ := Γ) R → G,
    if (fun f : RB (Γ := Γ) R =>
      η ⟨f.1, ManyBody.isRegionBoundaryEdge_touches R f.2⟩) = θ then
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
      η ⟨f.1, ManyBody.isRegionBoundaryEdge_touches R f.2⟩) = θ
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
end

end

section

open ManyBody (Edge)
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- A weight on one actual internal bond equals the original open contraction
with the literal diagonal insertion on its ordered tail site.
Source: SCP10, `eq:anyons:chargeon-def`, lines 2432–2453. -/
theorem regularWeightedOpenRegionWeight_eq_openRegionWeight_regularEdgeCharacterSite
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
    (χ : G → ℂ) (p : G) (θ : {b : Edge Γ // ManyBody.IsRegionBoundaryEdge R b} → G) :
    regularWeightedOpenRegionWeight a R (fun _ => 1)
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩)) θ =
      openRegionWeight (groupBondTensor (regularEdgeCharacterSite a e.1 χ p)) R
        (fun b => Fintype.equivFin G (θ b)) := by
  classical
  have hsite (v : V) (α : IncidentEdge Γ v → G) :
      regularTwistedLabels (fun _ => (1 : G)) v α = α := by
    funext i
    simp only [regularTwistedLabels, one_mul, ite_self]
  have hone : regularTwistedSite (regularEdgeCharacterSite a e.1 χ p)
      (fun _ => 1) = regularEdgeCharacterSite a e.1 χ p := by
    funext v α s
    simp only [regularTwistedSite, hsite]
  rw [← hone, ← regularWeightedOpenRegionWeight_one]
  funext σ
  unfold regularWeightedOpenRegionWeight
  apply Finset.sum_congr rfl
  intro η _
  split_ifs
  · simp only [one_mul, hsite]
    have he (w : {v : V // v ∈ R}) :
        regularEdgeCharacterSite a e.1 χ p w.1
            (fun i => η ⟨i.1, isRegionIncidentEdge_of_regionVertex R w i⟩) (σ w) =
          (if w = ⟨e.1.1.1,e.2.1⟩ then χ (p * η ⟨e.1,Or.inl e.2.1⟩) else 1) *
            a w.1 (fun i => η ⟨i.1, isRegionIncidentEdge_of_regionVertex R w i⟩) (σ w) := by
      by_cases hw : w.1 = e.1.1.1
      · have hsub : w = ⟨e.1.1.1,e.2.1⟩ := Subtype.ext hw
        subst w
        simp only [regularEdgeCharacterSite, dite_true, ite_true]
      · have hsub : w ≠ ⟨e.1.1.1,e.2.1⟩ := fun h => hw (congrArg Subtype.val h)
        simp only [regularEdgeCharacterSite, dite_eq_right hw, ite_eq_right hsub, one_mul]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp only [Fintype.prod_ite_eq']
  · rfl
end TNLean.PEPS
end

end
