/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargePairRegionalReadout
import TNLean.PEPS.TorusPhysicalChargePairCreation
import TNLean.PEPS.VerticalTwoPlaquetteGeometry
import TNLean.PEPS.RegularTorusEntropy

/-!
# Two-spin charge readout of the actual prepared six-spin pair

The translated two-column, three-row region supplies its five-edge tree and
its two horizontal chords. The charge insertion is the single correlated
weight χ(p η₁⁻¹ η₀) on these two internal bond labels. The same physical
unitary acts for every remaining crossing configuration.

Source: SCP10, arXiv:1001.3807, charge-pair creation, lines 2505–2558.
**Scope restriction (finite torus and regular action):** The horizontal period
is at least three and the vertical period at least four. Native bond sorting is retained,
including translated blocks crossing a seam. Coordinates increase along the
native upward axis; reversing the drawing's vertical axis identifies the
lower and middle chords with its top and middle internal references.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance chargeReadoutWidthTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance chargeReadoutWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance chargeReadoutHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

private abbrev R (v : X) := verticalTwoPlaquetteRegion v
private abbrev e₀ (v : X) := (verticalTwoPlaquetteCycleBond v 0).1
private abbrev e₁ (v : X) := (verticalTwoPlaquetteCycleBond v 1).1
private abbrev A (a : G → G → G → G → Fin d → ℂ) :=
  torusIncidentSite (width := width) (height := height) a


open scoped Classical in
/-- Two complete measurements, each supported on the two spins of its chosen
horizontal bond, read out the actual six-spin prepared correlated charge pair.
The measurements precede every charge and internal parameter. The preparation
unitary may depend on them, and acts uniformly on every crossing column.
Source: SCP10, charge-pair creation and its conjugate outcomes, lines 2505–2558. -/
theorem IsGIsometric.exists_torusPhysicalChargePairReadout
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ Q : Bool → Option (regularChargeLabels (G := G)) →
        Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      (∀ n r, (Q n r).IsHermitian ∧ (Q n r).PosSemidef) ∧
      (∀ n r s, Q n r * Q n s = if r = s then Q n r else 0) ∧
      (∀ n, ∑ r, Q n r = 1) ∧
      ∀ (χ : regularChargeLabels (G := G)) p,
        ∃ W : Matrix ({w : X // w ∈ R v} → Fin d)
            ({w : X // w ∈ R v} → Fin d) ℂ,
          W ∈ Matrix.unitaryGroup _ ℂ ∧
          ∀ θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R v) e} → G,
            W *ᵥ openRegionWeight (groupBondTensor (A a)) (R v)
                (fun f => Fintype.equivFin G (θ f)) =
              (fun s => regularChargePairOpenRegionMatrix (A a) (R v)
                (e₀ v) (e₁ v) χ.val p s θ) ∧
            ∀ n r,
              regularChargePairEndpointAction (R v) (if n then e₁ v else e₀ v) (Q n r)
                  (W *ᵥ openRegionWeight (groupBondTensor (A a)) (R v)
                    (fun f => Fintype.equivFin G (θ f))) =
                if r = some (if n then regularDualChargeLabel χ else χ) then
                  W *ᵥ openRegionWeight (groupBondTensor (A a)) (R v)
                    (fun f => Fintype.equivFin G (θ f)) else 0 := by
  have hne : (verticalTwoPlaquetteCycleBond v 0).1 ≠
      (verticalTwoPlaquetteCycleBond v 1).1 := by
    intro h
    have h' := verticalTwoPlaquetteCycleBond_injective v (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) h'
  obtain ⟨Q,hH,hO,hI,hact⟩ := exists_regularChargePairEndpointMeasurements
    (torusIncidentSite (width := width) (height := height) a)
    (fun w => ha.isGIsometric_torusIncidentSite w) (verticalTwoPlaquetteRegion v)
    (verticalTwoPlaquetteCycleBond v 0).1 (verticalTwoPlaquetteCycleBond v 1).1 hne
  refine ⟨Q,hH,hO,hI,?_⟩
  intro χ p
  obtain ⟨W,hW,hcreate⟩ := ha.exists_unitary_torusPhysicalChargePairCreation
    v χ.val χ.property p
  refine ⟨W,hW,fun θ => ⟨hcreate θ,?_⟩⟩
  intro n r
  rw [hcreate]
  exact hact n χ r p θ
end TNLean.PEPS
