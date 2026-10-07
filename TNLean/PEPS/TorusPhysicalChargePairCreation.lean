/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularPhysicalChargePairCreation
import TNLean.PEPS.VerticalTwoPlaquetteGeometry
import TNLean.PEPS.RegularTorusEntropy

/-!
# Charge-pair preparation on the actual six original torus spins

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
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance chargePairWidthTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance chargePairWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance chargePairHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

private abbrev R (v : X) := verticalTwoPlaquetteRegion v
private abbrev e₀ (v : X) := (verticalTwoPlaquetteCycleBond v 0).1
private abbrev e₁ (v : X) := (verticalTwoPlaquetteCycleBond v 1).1
private abbrev A (a : G → G → G → G → Fin d → ℂ) :=
  torusIncidentSite (width := width) (height := height) a

/-- One unitary on the actual six original spins prepares the literal correlated
charge-pair insertion, uniformly in all crossing labels. The tree, root, local
Gram matrix and charge witnesses are derived internally.
Source: SCP10, charge-pair creation, lines 2505–2558. -/
theorem IsGIsometric.exists_unitary_torusPhysicalChargePairCreation
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X)
    (χ : G → ℂ) (hχ : χ ∈ regularChargeLabels (G := G)) (p : G) :
    ∃ W : Matrix ({w : X // w ∈ R v} → Fin d)
        ({w : X // w ∈ R v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup _ ℂ ∧
      ∀ θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R v) e} → G,
        W *ᵥ openRegionWeight (groupBondTensor (A a)) (R v) (fun f => Fintype.equivFin G (θ f)) =
        fun s => regularChargePairOpenRegionMatrix (A a) (R v) (e₀ v) (e₁ v) χ p s θ := by
  have hne : (verticalTwoPlaquetteCycleBond v 0).1 ≠
      (verticalTwoPlaquetteCycleBond v 1).1 := by
    intro h
    have h' := verticalTwoPlaquetteCycleBond_injective v (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) h'
  obtain ⟨W, hW, hact⟩ := exists_unitary_regularPhysicalChargePairCreation
    (torusIncidentSite (width := width) (height := height) a)
    (fun w => ha.isGIsometric_torusIncidentSite w) (verticalTwoPlaquetteRegion v)
    (verticalTwoPlaquetteTree v) (verticalTwoPlaquetteTree_le v)
    (verticalTwoPlaquetteTree_isTree v) (verticalTwoPlaquetteIso v 0)
    (verticalTwoPlaquetteCycleBond v 0).1 (verticalTwoPlaquetteCycleBond v 1).1 hne χ hχ p
  refine ⟨W, hW, fun θ => ?_⟩
  have hinput := regularChargePairOpenRegionMatrix_one_eq_openRegionWeight
    (torusIncidentSite (width := width) (height := height) a)
    (fun w => (ha.isGIsometric_torusIncidentSite w).toIsGInjective)
    (verticalTwoPlaquetteRegion v)
    (verticalTwoPlaquetteCycleBond v 0).1 (verticalTwoPlaquetteCycleBond v 1).1 θ
  exact (congrArg (fun ψ => W *ᵥ ψ) hinput).symm.trans (hact θ)
end TNLean.PEPS
