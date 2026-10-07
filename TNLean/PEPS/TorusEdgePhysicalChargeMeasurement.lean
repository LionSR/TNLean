/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularEdgePhysicalChargeMeasurement
import TNLean.PEPS.RegularTorusEntropy
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.RegularTwoSiteChargeNonzero

/-!
# Native two-spin charge detection

The measured bond is an actual right or up edge, and its two original physical
sites and all crossing labels are retained. Ordered endpoints automatically
account for both seam orientations. Source: SCP10, arXiv:1001.3807,
Theorem `thm:anyons:detect-chargeons`, charge detection, lines 2464–2486.

**Scope restriction (finite simple tori):** both periods are at least three.
No energy, ground-space or nonvanishing assertion for arbitrary exterior
contractions is made. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance torusEdgeChargeWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance torusEdgeChargeHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- The actual horizontal or vertical bond supporting the diagonal charge.
Source: SCP10, `eq:anyons:chargeon-def`, lines 2432–2453. -/
def torusChargeMeasurementEdge (horizontal : Bool) (p : TorusVertex width height) :
    Edge (torusGraph width height) := if horizontal then torusRightEdge p else torusUpEdge p

private theorem other_leg (horizontal : Bool) (p : TorusVertex width height)
    (v : TorusVertex width height)
    (i : IncidentEdge (torusGraph width height) v)
    (hi : i.1 = torusChargeMeasurementEdge horizontal p) :
    Nonempty {f : IncidentEdge (torusGraph width height) v // f ≠ i} := by
  cases horizontal with
  | false =>
    refine ⟨⟨torusRightLeg v, ?_⟩⟩
    intro h
    have he := congrArg Subtype.val h
    exact torusRightEdge_ne_torusUpEdge v p (he.trans hi)
  | true =>
    refine ⟨⟨torusTopLeg v, ?_⟩⟩
    intro h
    have he := congrArg Subtype.val h
    exact torusRightEdge_ne_torusUpEdge p v (he.trans hi).symm
/-- Every actual irreducible charge yields a nonzero native two-spin open
column. The three other legs at each site are retained; no global nonvanishing
under an arbitrary exterior contraction is asserted. Source: SCP10,
charge detection, lines 2464–2486. -/
theorem IsGIsometric.openRegionWeight_torusEdgeCharacterSite_ne_zero
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (horizontal : Bool) (v : TorusVertex width height)
    (χ : regularChargeLabels (G := G)) (p : G)
    (θ : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge
      {(torusChargeMeasurementEdge horizontal v).1.1,
        (torusChargeMeasurementEdge horizontal v).1.2} f} → G) :
    openRegionWeight (groupBondTensor (regularEdgeCharacterSite (torusIncidentSite a)
      (torusChargeMeasurementEdge horizontal v) χ.val p))
      {(torusChargeMeasurementEdge horizontal v).1.1,
        (torusChargeMeasurementEdge horizontal v).1.2}
      (fun f => Fintype.equivFin G (θ f)) ≠ 0 := by
  classical
  let e := torusChargeMeasurementEdge horizontal v
  let _ := other_leg horizontal v e.1.1 (regularEdgeTailLeg e) rfl
  let _ := other_leg horizontal v e.1.2 (regularEdgeHeadLeg e) rfl
  have hn := regularTwoSitePhysicalChargeColumn_ne_zero_of_mem_regularChargeLabels
    (regularEdgeTailLeg e) (regularEdgeHeadLeg e)
    (torusIncidentSite a e.1.1) (torusIncidentSite a e.1.2)
    (ha.isGIsometric_torusIncidentSite e.1.1).toIsGInjective
    (ha.isGIsometric_torusIncidentSite e.1.2).toIsGInjective
    χ.val χ.property p (regularEdgeChargeBoundaryLabels e θ)
  intro hz
  apply hn
  funext s
  have hs := congrFun hz ((regularEdgePhysicalPairEquiv (d := d) e).symm s)
  rw [openRegionWeight_regularEdgeCharacterSite] at hs
  simpa only [e, Equiv.apply_symm_apply, Pi.zero_apply] using hs
/-- A fixed complete measurement on the two adjacent original torus spins
selects the charge on every actual open column and cut, including both seams.
It is chosen before the charge, its internal parameter, and all common exterior
site tensors. Source: SCP10, `thm:anyons:detect-chargeons`, lines 2464–2486. -/
theorem IsGIsometric.exists_torusEdgePhysicalAllChargeMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (horizontal : Bool) (v : TorusVertex width height) :
    let e := torusChargeMeasurementEdge horizontal v
    let R : Finset (TorusVertex width height) := {e.1.1,e.1.2}
    ∃ Q : Option (regularChargeLabels (G := G)) →
        Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      (∀ r, (Q r).IsHermitian ∧ (Q r).PosSemidef) ∧
      (∀ r s, Q r * Q s = if r = s then Q r else 0) ∧
      (∑ r, Q r = 1) ∧
      ∀ (b : (w : TorusVertex width height) →
          (IncidentEdge (torusGraph width height) w → G) → Fin d → ℂ)
        (_ : ∀ w ∈ R, b w = torusIncidentSite a w)
        (χ : regularChargeLabels (G := G)) r p,
        (∀ θ : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} → G,
          Q r *ᵥ openRegionWeight (groupBondTensor (regularEdgeCharacterSite b e χ.val p))
              R (fun f => Fintype.equivFin G (θ f)) =
            if r = some χ then
              openRegionWeight (groupBondTensor (regularEdgeCharacterSite b e χ.val p))
                R (fun f => Fintype.equivFin G (θ f)) else 0) ∧
        Q r * regularPhysicalCutMatrix (regularEdgeCharacterSite b e χ.val p) R =
          if r = some χ then
            regularPhysicalCutMatrix (regularEdgeCharacterSite b e χ.val p) R else 0 := by
  classical
  dsimp only
  let e := torusChargeMeasurementEdge horizontal v
  obtain ⟨Q,hQh,hQQ,hQs,hQa⟩ := exists_regularEdgePhysicalAllChargeMeasurement
    (torusIncidentSite a) e (ha.isGIsometric_torusIncidentSite e.1.1)
      (ha.isGIsometric_torusIncidentSite e.1.2)
  refine ⟨Q,hQh,hQQ,hQs,?_⟩
  intro b hb χ r p
  have hc := hQa b hb χ r p
  exact ⟨hc, mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
    (regularEdgeCharacterSite b e χ.val p) {e.1.1,e.1.2} (Q r) (r = some χ) hc⟩
end TNLean.PEPS
