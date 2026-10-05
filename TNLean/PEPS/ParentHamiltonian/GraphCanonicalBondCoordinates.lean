/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenBondFactors
import TNLean.PEPS.GraphBondRegionBlocks

/-!
# Genuine canonical regional ranges in bond coordinates

Finite coordinate regrouping identifies the actual numbered regional PEPS
range with the span of all its explicitly contracted bond-coordinate columns.
Every virtual boundary condition is retained.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2977–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G] {p q : ℕ}

/-- The actual dressed graph tensor with finite numbered physical coordinates. -/
def numberedGraphDressedAveragingTensor (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) : Tensor Γ p :=
  groupBondTensor (fun v η s => graphDressedAveragingSite U W v η ((e v).symm s))

/-- Reorder numbered regional physical vectors into crossing endpoints and
internal bond pairs. This changes coordinates, not the contraction space. -/
def regionBondPhysicalEquiv
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (R : Finset V) :
    (RegionPhysicalConfig (d := p) R → ℂ) ≃ₗ[ℂ]
      (((RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (regionBondConfigEquiv e R).symm

/-- The open-region range, written in bond coordinates with all virtual
boundary labels allowed. Its equality with the numbered PEPS range is proved below. -/
def graphOpenBondSpace (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (R : Finset V) :
    Submodule ℂ (((RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) → ℂ) :=
  Submodule.span ℂ (Set.range (graphOpenBondCoordinates U W R))

/-- Coordinate regrouping sends every literal open-region tensor to its
already derived bond-coordinate contraction, with identical boundary data. -/
theorem regionBondPhysicalEquiv_openRegionWeight
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    regionBondPhysicalEquiv e R
      (openRegionWeight (numberedGraphDressedAveragingTensor U W e) R
        (fun f => Fintype.equivFin X (θ f))) = graphOpenBondCoordinates U W R θ := by
  funext β
  change openRegionWeight (numberedGraphDressedAveragingTensor U W e) R
    (fun f => Fintype.equivFin X (θ f)) ((regionBondConfigEquiv e R).symm β) = _
  rw [regionBondConfigEquiv_symm_apply]
  have h := openRegionWeight_groupBondTensor_dressedAveragingSite U W hc e R θ
    (fun v => e v.1 ((regionHalfEdgeLabelEquiv R).symm
      (β.1, (fun f => (β.2 f).2), fun f => (β.2 f).1) v))
  simpa only [numberedGraphDressedAveragingTensor, graphOpenBondCoordinates,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h

/-- The bond-coordinate space is exactly the genuine regional PEPS range,
with no extra boundary support premise. -/
theorem map_regionGroundSpace_eq_graphOpenBondSpace
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (R : Finset V) :
    (regionGroundSpace (numberedGraphDressedAveragingTensor U W e) R).map
      (regionBondPhysicalEquiv e R).toLinearMap = graphOpenBondSpace U W R := by
  rw [regionGroundSpace_eq_span, Submodule.map_span]
  unfold graphOpenBondSpace
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
      (regionBondPhysicalEquiv_openRegionWeight U W hc e R θ).symm
  · rintro ⟨θ, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, regionBondPhysicalEquiv_openRegionWeight U W hc e R θ⟩

/-- Membership in the actual regional range is precisely membership after
regrouping into the explicitly contracted bond-coordinate space. -/
theorem regionBondPhysicalEquiv_mem_graphOpenBondSpace_iff
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (R : Finset V)
    (ψ : RegionPhysicalConfig (d := p) R → ℂ) :
    regionBondPhysicalEquiv e R ψ ∈ graphOpenBondSpace U W R ↔
      ψ ∈ regionGroundSpace (numberedGraphDressedAveragingTensor U W e) R := by
  rw [← map_regionGroundSpace_eq_graphOpenBondSpace U W hc e R]
  constructor
  · rintro ⟨φ, hφ, hEq⟩
    exact (regionBondPhysicalEquiv e R).injective hEq ▸ hφ
  · intro hψ
    exact ⟨ψ, hψ, rfl⟩

end TNLean.PEPS
