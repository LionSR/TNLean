/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptRouteBondAssignments
import TNLean.PEPS.TorusJointFluxGeometry
import TNLean.PEPS.RegularCycleFluxMeasurement
import TNLean.PEPS.RegularPhysicalCutColumnAction
import TNLean.PEPS.RegularInsertedWalkHolonomy
/-!
# Actual commutator-class measurement after the literal endpoint route

The actual partner-first reunion loop is supported in the native six-site
block around the final two neighbouring plaquettes. A complete original-spin
projective measurement, chosen before all flux and exterior labels, detects
its derived commutator class on every boundary column and the actual cut.
Physical implementation of the preceding twelve moves remains separate.
Source: SCP10, arXiv:1001.3807, Section 6.6, joint-flux alignment and detection,
local lines 2387–2415. No parent-Hamiltonian assertion is made.
**Scope restriction (finite torus and regular action):** The width is at least
eight and the height at least seven. Every position and both periodic seams
are allowed. The results concern the displayed endpoint route and its original
physical contractions. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance routeMeasurementWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeMeasurementHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance routeMeasurementWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance routeMeasurementHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
/-- The actual six-site block supporting the final two neighbouring B loops.
Source: SCP10, joint-flux measurement after reunion, lines 2387–2415. -/
def torusSweptRouteReunionRegion (v : X) := translatedTwoPlaquetteRegion (v.1,v.2-2)
private abbrev R (v : X) := torusSweptRouteReunionRegion v
private theorem reunion_support (v : X) :
    ∀ x ∈ (torusSweptPhysicalRouteBReunionLoop v).support, x ∈ (R v : Set X) := by
  intro x hx
  change x ∈ translatedTwoPlaquetteRegion (v.1,v.2-2)
  rw [← torusTwoPlaquetteOuterWalk_support (v.1,v.2-2), List.mem_toFinset]
  simp only [torusSweptPhysicalRouteBReunionLoop,
    SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hx
  simp only [torusSweptPhysicalRouteReunionConnector, torusPlaquetteWalk,
    SimpleGraph.Walk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [torusTwoPlaquetteOuterWalk, SimpleGraph.Walk.support,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
omit [Fintype G] [DecidableEq G] in
/-- The derived joint measurement has identity conjugacy class precisely when
its two initial flux labels commute. Source: SCP10, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptRoute_jointClass_trivial_iff
    (v : X) (g h : G) :
    ConjClasses.mk (regularWalkHolonomy (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteBReunionLoop v)) = 1 ↔ Commute g h := by
  rw [regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop_conjClass,
    ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj,
    isConj_one_left, ← commutatorElement_def, commutatorElement_eq_one_iff_commute]
/-- One complete measurement on the actual six original spins detects the
commutator class derived from the literal final route assignment, uniformly
in both flux labels, all crossing/exterior operators and all boundary columns.
Source: SCP10, joint flux and alignment, lines 2387–2415.
Physical implementation of the preceding route remains separate. -/
theorem IsGIsometric.exists_torusSweptRouteReunion_physicalMeasurement
    (a : (v : X) → (IncidentEdge Γₜ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ v))
      (regularSiteMap (a v))) (v : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (R v))
          (RegionPhysicalConfig (d := d) (R v)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      (∀ (g h : G) (u : Edge Γₜ → G)
          (θ : {f : Edge Γₜ // IsRegionBoundaryEdge (R v) f} → G)
          (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension (R v) (torusSweptPhysicalRouteOperators v g h 12) u)))
          (R v) (fun f => Fintype.equivFin G (θ f)) =
        if C = some (ConjClasses.mk (g*h*g⁻¹*h⁻¹)) then
          openRegionWeight (groupBondTensor (regularTwistedSite a
            (regularRegionBondExtension (R v) (torusSweptPhysicalRouteOperators v g h 12) u)))
            (R v) (fun f => Fintype.equivFin G (θ f)) else 0) ∧
      ∀ (g h : G) (u : Edge Γₜ → G) (C : Option (ConjClasses G)),
        Q C * regularPhysicalCutMatrix (regularTwistedSite a
          (regularRegionBondExtension (R v) (torusSweptPhysicalRouteOperators v g h 12) u))
          (R v) =
        if C = some (ConjClasses.mk (g*h*g⁻¹*h⁻¹)) then
          regularPhysicalCutMatrix (regularTwistedSite a
            (regularRegionBondExtension (R v) (torusSweptPhysicalRouteOperators v g h 12) u))
            (R v) else 0 := by
  classical
  let hs := reunion_support v
  let o : {x : X // x ∈ R v} :=
    ⟨(v.1,v.2-2), hs _ (torusSweptPhysicalRouteBReunionLoop v).start_mem_support⟩
  let p : ((Γₜ).induce (R v : Set X)).Walk o o :=
    (torusSweptPhysicalRouteBReunionLoop v).induce (R v : Set X) hs
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ :=
    exists_regularClosedWalkClass_physicalMeasurement a ha (R v)
      (translatedTwoPlaquetteRegion_connected (v.1,v.2-2)) o p
  have hclass (g h : G) (u : Edge Γₜ → G) :
      ConjClasses.mk (regularWalkHolonomy (regularRegionInternalOperators (R v)
        (regularRegionBondExtension (R v) (torusSweptPhysicalRouteOperators v g h 12) u)) p) =
        ConjClasses.mk (g*h*g⁻¹*h⁻¹) := by
    rw [regularWalkHolonomy_induced_bondExtension, SimpleGraph.Walk.map_induce]
    exact regularWalkHolonomy_torusSweptPhysicalRoute_BReunionLoop_conjClass v g h
  have hcols (g h : G) (u : Edge Γₜ → G)
      (θ : {f : Edge Γₜ // IsRegionBoundaryEdge (R v) f} → G)
      (C : Option (ConjClasses G)) :=
    hQact (regularRegionBondExtension (R v) (torusSweptPhysicalRouteOperators v g h 12) u) θ C
  simp only [hclass] at hcols
  refine ⟨Q,hQh,hQm,hQsum,hcols,?_⟩
  intro g h u C
  apply mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
  exact fun θ => hcols g h u θ C
end TNLean.PEPS
