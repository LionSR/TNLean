/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularPhysicalChargePairInterference
import TNLean.PEPS.TorusPhysicalChargePairCreation

/-!
# The return measurement on six original torus spins

The actual translated two-column, three-row patch supplies the reference bonds,
spanning tree and root. A complete binary measurement on its six original spins
has the accepted amplitude of SCP10's charge–flux interference calculation.
Every actual boundary label is retained.

Source: SCP10, arXiv:1001.3807, lines 2582–2615.
**Scope restriction (six-site return operation):** The horizontal period is at
least three and the vertical period at least four, including both seams.
This proves the return measurement on the literal correlated bond sum, not
that a prescribed complete geometric braid produces that sum. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance chargeReturnHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance chargeReturnWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance chargeReturnHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private abbrev R (v : X) := verticalTwoPlaquetteRegion v
private abbrev e₀ (v : X) := (verticalTwoPlaquetteCycleBond v 0).1
private abbrev e₁ (v : X) := (verticalTwoPlaquetteCycleBond v 1).1

/-- A complete original-spin measurement is chosen before the flux and every
native crossing label. The six sites, tree and two distinct reference bonds are
derived from the actual torus. Source: SCP10, return measurement, lines 2582–2615. -/
theorem IsGIsometric.exists_torusPhysicalChargePairReturnMeasurement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (σ : Representation ℂ G H) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : X) (p : G) :
    ∃ Q : Bool → Matrix ({w : X // w ∈ R v} → Fin d)
        ({w : X // w ∈ R v} → Fin d) ℂ,
      (∀ b, (Q b).IsHermitian ∧ (Q b).PosSemidef) ∧
      (∀ b r, Q b * Q r = if b = r then Q b else 0) ∧ (∑ b, Q b) = 1 ∧
      ∀ (k : G) (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R v) e} → G),
        let ψ := regularWeightedOpenRegionWeight (torusIncidentSite a) (R v)
          (fun _ => 1) (fun η => σ.character
            (p * (η ⟨(e₁ v).1,Or.inl (e₁ v).2.1⟩)⁻¹ * k⁻¹ *
              η ⟨(e₀ v).1,Or.inl (e₀ v).2.1⟩)) θ
        let φ := (σ.character k⁻¹ / Module.finrank ℂ H) •
          (fun s => regularChargePairOpenRegionMatrix (torusIncidentSite a)
            (R v) (e₀ v) (e₁ v) σ.character p s θ)
        Q true *ᵥ ψ = φ ∧ Q false *ᵥ ψ = ψ - φ := by
  have hne : (verticalTwoPlaquetteCycleBond v 0).1 ≠
      (verticalTwoPlaquetteCycleBond v 1).1 := by
    intro h
    have h' := verticalTwoPlaquetteCycleBond_injective v (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) h'
  exact exists_regularPhysicalChargePairReturnMeasurement σ hσ
    (torusIncidentSite (width := width) (height := height) a)
    (fun w => ha.isGIsometric_torusIncidentSite w) (verticalTwoPlaquetteRegion v)
    (verticalTwoPlaquetteTree v) (verticalTwoPlaquetteTree_le v)
    (verticalTwoPlaquetteTree_isTree v) (verticalTwoPlaquetteIso v 0)
    (verticalTwoPlaquetteCycleBond v 0).1 (verticalTwoPlaquetteCycleBond v 1).1 hne p

end TNLean.PEPS
