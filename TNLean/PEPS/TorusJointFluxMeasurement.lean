/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusJointFluxGeometry
import TNLean.PEPS.RegularPhysicalCutColumnAction
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
import TNLean.PEPS.RegularCycleFluxMeasurement

import TNLean.PEPS.RegularInsertedWalkHolonomy

/-!
# A physical measurement of the joint flux of two adjacent plaquettes

The outer walk of a translated six-site block encloses two plaquettes. The
routed bond assignment has their holonomies `a` and `b` and outer holonomy
`a * b`. A single complete projective measurement on the original six spins
detects the conjugacy class of this product, for every outgoing configuration
and every common exterior and crossing assignment. The same measurement acts
on the actual globally contracted physical cut matrix.

Source: SCP10, arXiv:1001.3807, the joint flux measurement in the braiding
argument, lines 2380–2415, using Theorem 6.15, lines 2217–2267.

**Scope restriction (regular six-site joint measurement):** The torus has
horizontal period at least four and vertical period at least three. The block
may cross either seam. This proves the joint measurement step for regular
G-isometric tensors, without asserting braiding, energies, or membership in a
parent-Hamiltonian ground space. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance jointMeasurementWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance jointMeasurementWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance jointMeasurementHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- One complete six-spin measurement detects the product of the two routed
plaquette fluxes on every boundary column and on the actual global cut.
Source: SCP10, joint flux measurement, lines 2380–2415. -/
theorem IsGIsometric.exists_torusJointFlux_physicalMeasurement
    {tensor : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap tensor)) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (translatedTwoPlaquetteRegion v))
          (RegionPhysicalConfig (d := d) (translatedTwoPlaquetteRegion v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      (∀ (a b : G) (u : Edge (Γₜ) → G)
        (θ : {f : Edge (Γₜ) // IsRegionBoundaryEdge (translatedTwoPlaquetteRegion v) f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight
            (groupBondTensor (regularTwistedSite (torusIncidentSite tensor)
              (regularRegionBondExtension (translatedTwoPlaquetteRegion v)
                (torusJointFluxAssignment v a b) u)))
            (translatedTwoPlaquetteRegion v) (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk (a * b)) then openRegionWeight
            (groupBondTensor (regularTwistedSite (torusIncidentSite tensor)
              (regularRegionBondExtension (translatedTwoPlaquetteRegion v)
                (torusJointFluxAssignment v a b) u)))
            (translatedTwoPlaquetteRegion v) (fun f => Fintype.equivFin G (θ f)) else 0) ∧
      ∀ (a b : G) (u : Edge (Γₜ) → G) (C : Option (ConjClasses G)),
        Q C * regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite tensor)
              (regularRegionBondExtension (translatedTwoPlaquetteRegion v)
                (torusJointFluxAssignment v a b) u)) (translatedTwoPlaquetteRegion v) =
          if C = some (ConjClasses.mk (a * b)) then regularPhysicalCutMatrix
            (regularTwistedSite (torusIncidentSite tensor)
              (regularRegionBondExtension (translatedTwoPlaquetteRegion v)
                (torusJointFluxAssignment v a b) u)) (translatedTwoPlaquetteRegion v) else 0 := by
  classical
  let R := translatedTwoPlaquetteRegion v
  have hs : ∀ x ∈ (torusTwoPlaquetteOuterWalk v).support, x ∈ (R : Set X) := by
    intro x hx
    change x ∈ translatedTwoPlaquetteRegion v
    rw [← torusTwoPlaquetteOuterWalk_support v]
    exact List.mem_toFinset.mpr hx
  let o : {x : X // x ∈ R} := ⟨v, hs _ (torusTwoPlaquetteOuterWalk v).start_mem_support⟩
  let p : ((Γₜ).induce (R : Set X)).Walk o o :=
    (torusTwoPlaquetteOuterWalk v).induce (R : Set X) hs
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ :=
    exists_regularClosedWalkClass_physicalMeasurement (torusIncidentSite tensor)
      (fun w => ha.isGIsometric_torusIncidentSite w) R
      (translatedTwoPlaquetteRegion_connected v) o p
  have hhol (a b : G) (u : Edge (Γₜ) → G) :
      regularWalkHolonomy (regularRegionInternalOperators R
        (regularRegionBondExtension R (torusJointFluxAssignment v a b) u)) p = a * b := by
    rw [regularWalkHolonomy_induced_bondExtension, SimpleGraph.Walk.map_induce]
    exact (regularWalkHolonomy_torusJointFluxAssignment v a b).2.2
  have hcols (a b : G) (u : Edge (Γₜ) → G)
      (θ : {f : Edge (Γₜ) // IsRegionBoundaryEdge R f} → G) (C : Option (ConjClasses G)) :=
    hQact (regularRegionBondExtension R (torusJointFluxAssignment v a b) u) θ C
  simp only [hhol] at hcols
  refine ⟨Q, hQh, hQm, hQsum, hcols, ?_⟩
  intro a b u C
  apply mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
  exact fun θ => hcols a b u θ C

end TNLean.PEPS
