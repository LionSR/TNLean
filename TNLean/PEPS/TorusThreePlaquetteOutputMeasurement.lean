/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusThreePlaquetteDoubleExchange
import TNLean.PEPS.RegularCycleFluxMeasurement
import TNLean.PEPS.RegularPhysicalCutColumnAction

import TNLean.PEPS.RegularInsertedWalkHolonomy

/-!
# Joint-flux measurement after the literal three-plaquette double exchange

One complete projective measurement on the eight original spins detects the
conjugacy class of the actual outer holonomy surrounding the middle and right
plaquettes. The family is chosen before all input transports, crossing labels
and common exterior assignments. Its actions on the output boundary columns
and actual global cut are derived from the induced native closed walk.

Source: SCP10, arXiv:1001.3807, Theorem 6.15, lines 2217–2267, and the
joint-measurement braiding passage, lines 2380–2415.

**Scope restriction (constructed double-exchange output):** The horizontal
period is at least five and the vertical period at least three, and the virtual
action is regular. All positions and both seams are included. No prescribed
physical string crossing, braid, energy, or parent-Hamiltonian membership is
asserted. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (2 < height)]
local instance threeOutputWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeOutputWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeOutputWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeOutputHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- One complete original eight-spin measurement detects the actual surrounding
output flux for all input transports, boundary configurations and exterior data.
Auxiliary joint measurement for SCP10, lines 2217–2267 and 2380–2415. -/
theorem IsGIsometric.exists_torusThreePlaquetteOutput_physicalMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let R := translatedThreePlaquetteRegion v
    let A := torusIncidentSite (width := width) (height := height) a
    let flux := fun t : Fin 3 → G =>
      ((t 0)⁻¹ * t 1) * ((t 1)⁻¹ * t 2) * ((t 0)⁻¹ * t 1)⁻¹ * (t 2)⁻¹
    let output := fun t : Fin 3 → G =>
      torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t)
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      (∀ (t : Fin 3 → G) (u : Edge Γₜ → G)
        (θ : {f : Edge Γₜ // IsRegionBoundaryEdge R f} → G) (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight
            (groupBondTensor (regularTwistedSite A (regularRegionBondExtension R (output t) u)))
            R (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk (flux t)) then openRegionWeight
            (groupBondTensor (regularTwistedSite A (regularRegionBondExtension R (output t) u)))
            R (fun f => Fintype.equivFin G (θ f)) else 0) ∧
      ∀ (t : Fin 3 → G) (u : Edge Γₜ → G) (C : Option (ConjClasses G)),
        Q C * regularPhysicalCutMatrix
            (regularTwistedSite A (regularRegionBondExtension R (output t) u)) R =
          if C = some (ConjClasses.mk (flux t)) then regularPhysicalCutMatrix
            (regularTwistedSite A (regularRegionBondExtension R (output t) u)) R else 0 := by
  classical
  let R := translatedThreePlaquetteRegion v
  let A := torusIncidentSite (width := width) (height := height) a
  let flux := fun t : Fin 3 → G =>
    ((t 0)⁻¹ * t 1) * ((t 1)⁻¹ * t 2) * ((t 0)⁻¹ * t 1)⁻¹ * (t 2)⁻¹
  let output := fun t : Fin 3 → G =>
    torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t)
  have hs := torusThreePlaquette_rightPairWalk_mem_region v
  let o : {x : X // x ∈ R} :=
    ⟨(v.1 + 1, v.2), hs _ (torusTwoPlaquetteOuterWalk (v.1 + 1, v.2)).start_mem_support⟩
  let p : ((Γₜ).induce (R : Set X)).Walk o o :=
    (torusTwoPlaquetteOuterWalk (v.1 + 1, v.2)).induce (R : Set X) hs
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ :=
    exists_regularClosedWalkClass_physicalMeasurement A
      (fun x => ha.isGIsometric_torusIncidentSite x) R
      (translatedThreePlaquetteRegion_connected v) o p
  have hhol (t : Fin 3 → G) (u : Edge Γₜ → G) :
      regularWalkHolonomy (regularRegionInternalOperators R
        (regularRegionBondExtension R (output t) u)) p = flux t := by
    rw [regularWalkHolonomy_induced_bondExtension, SimpleGraph.Walk.map_induce]
    exact (regularWalkHolonomy_torusThreePlaquetteDoubleExchange v t).2.2.2
  have hcols (t : Fin 3 → G) (u : Edge Γₜ → G)
      (θ : {f : Edge Γₜ // IsRegionBoundaryEdge R f} → G) (C : Option (ConjClasses G)) :=
    hQact (regularRegionBondExtension R (output t) u) θ C
  simp only [hhol] at hcols
  refine ⟨Q, hQh, hQm, hQsum, hcols, ?_⟩
  intro t u C
  apply mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen
  exact fun θ => hcols t u θ C

/-- The output measurement can be chosen together with the same literal
original-spin double-exchange unitary. Both witnesses precede all transports,
boundary configurations and common exterior operators. Auxiliary to SCP10,
Theorem 6.15 and braiding passage, lines 2217–2267 and 2380–2415. -/
theorem IsGIsometric.exists_torusThreePlaquetteMeasuredDoubleExchange
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let R := translatedThreePlaquetteRegion v
    let A := torusIncidentSite (width := width) (height := height) a
    let flux := fun t : Fin 3 → G =>
      ((t 0)⁻¹ * t 1) * ((t 1)⁻¹ * t 2) * ((t 0)⁻¹ * t 1)⁻¹ * (t 2)⁻¹
    let input := fun t : Fin 3 → G => torusThreePlaquetteFluxAssignment v t
    let output := fun t : Fin 3 → G =>
      torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t)
    ∃ (W : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
      (Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ),
      W ∈ Matrix.unitaryGroup (RegionPhysicalConfig (d := d) R) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      (∀ (t : Fin 3 → G) (θ : {f : Edge Γₜ // IsRegionBoundaryEdge R f} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite A (input t))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite A (output t))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      (∀ (t : Fin 3 → G) (u : Edge Γₜ → G),
        regionLocalTerm R W *ᵥ stateCoeff
          (groupBondTensor (regularTwistedSite A (regularRegionBondExtension R (input t) u))) =
        stateCoeff
          (groupBondTensor (regularTwistedSite A (regularRegionBondExtension R (output t) u)))) ∧
      (∀ (t : Fin 3 → G) (θ : {f : Edge Γₜ // IsRegionBoundaryEdge R f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ (W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite A (input t))) R
            (fun f => Fintype.equivFin G (θ f))) =
          if C = some (ConjClasses.mk (flux t)) then
            W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite A (input t))) R
              (fun f => Fintype.equivFin G (θ f)) else 0) ∧
      ∀ (t : Fin 3 → G) (u : Edge Γₜ → G) (C : Option (ConjClasses G)),
        Q C * (W * regularPhysicalCutMatrix
            (regularTwistedSite A (regularRegionBondExtension R (input t) u)) R) =
          if C = some (ConjClasses.mk (flux t)) then W * regularPhysicalCutMatrix
            (regularTwistedSite A (regularRegionBondExtension R (input t) u)) R else 0 := by
  classical
  let R := translatedThreePlaquetteRegion v
  let A := torusIncidentSite (width := width) (height := height) a
  let input := fun t : Fin 3 → G => torusThreePlaquetteFluxAssignment v t
  let output := fun t : Fin 3 → G =>
    torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t)
  obtain ⟨W, hW, hWU, hlocal, hglobal⟩ := ha.exists_unitary_torusThreePlaquetteDoubleExchange v
  obtain ⟨Q, hQh, hQm, hQsum, hQcol, hQcut⟩ :=
    ha.exists_torusThreePlaquetteOutput_physicalMeasurement v
  have hcut (t : Fin 3 → G) (u : Edge Γₜ → G) :
      W * regularPhysicalCutMatrix
          (regularTwistedSite A (regularRegionBondExtension R (input t) u)) R =
        regularPhysicalCutMatrix
          (regularTwistedSite A (regularRegionBondExtension R (output t) u)) R := by
    ext σ τ
    have h := congrFun (hglobal t u) (assembleRegionσ R σ τ)
    rw [regionLocalTerm_mulVec_assemble] at h
    exact h
  refine ⟨W, Q, hW, hWU, hQh, hQm, hQsum, hlocal, hglobal, ?_, ?_⟩
  · intro t θ C
    rw [hlocal t θ]
    have hself : regularRegionBondExtension R (output t) (output t) = output t := by
      funext e
      simp only [regularRegionBondExtension, ite_self]
    have h := hQcol t (output t) θ C
    rw [hself] at h
    exact h
  · intro t u C
    rw [hcut t u]
    exact hQcut t u C

end TNLean.PEPS
