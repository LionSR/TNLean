/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSweptPhysicalRouteComposition
import TNLean.PEPS.TorusSweptRouteJointFluxMeasurement
/-!
# Original-spin endpoint route followed by the actual reunion measurement

The twelve fixed elementary operations and the six-spin reunion projectors
are selected before both flux labels. Their actual contraction identities
show that the final measurement selects the commutator conjugacy class.
Source: SCP10, arXiv:1001.3807, Section 6.6, lines 2340–2423.
The finite-torus route and class measurement do not assert an unrestricted
braid, a prescribed partner-annihilation operation or an energy statement.
**Scope restriction (finite torus and regular action):** The width is at least
eight and the height at least seven. All translations and both seams are
included. The result concerns the specified physical route and its class
measurement. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (7 < width)] [Fact (6 < height)]
local instance measuredRouteWidthFour : Fact (4 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance measuredRouteHeightThree : Fact (3 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local instance measuredRouteWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 7 < width); omega⟩
local instance measuredRouteHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 6 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
omit [Group G] [DecidableEq G] in
private theorem global_eigen_of_cut
    (a : (x : X) → (IncidentEdge Γₜ x → G) → Fin d → ℂ) (R : Finset X)
    (Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (P : Prop) [Decidable P]
    (hQ : Q * regularPhysicalCutMatrix a R = if P then regularPhysicalCutMatrix a R else 0) :
    regionLocalTerm R Q *ᵥ stateCoeff (groupBondTensor a) =
      if P then stateCoeff (groupBondTensor a) else 0 := by
  funext ξ
  obtain ⟨⟨σ,τ⟩,rfl⟩ := (regionConfigEquiv (d := d) R).symm.surjective ξ
  change (regionLocalTerm R Q *ᵥ stateCoeff (groupBondTensor a))
    (assembleRegionσ R σ τ) =
      (if P then stateCoeff (groupBondTensor a) else 0) (assembleRegionσ R σ τ)
  rw [regionLocalTerm_mulVec_assemble]
  have H := congrArg (fun N => N σ τ) hQ
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, regularPhysicalCutMatrix,
    Matrix.ite_apply,
    Matrix.zero_apply, ite_apply, Pi.zero_apply] using H
/-- One fixed twelve-step original-spin product followed by one fixed six-spin
measurement detects the derived commutator class on the actual whole state and
its actual cut. Source: SCP10, Section 6.6, lines 2340–2423. The elementary
support witnesses are retained; no state, Gram or holonomy identity is supplied. -/
theorem IsGIsometric.exists_torusSweptPhysicalRoute_commutatorMeasurement
    (a : (x : X) → (IncidentEdge Γₜ x → G) → Fin d → ℂ)
    (ha : ∀ x, IsGIsometric (regularLegRepresentation (IncidentEdge Γₜ x))
      (regularSiteMap (a x))) (v : X) :
    let R := torusSweptRouteReunionRegion v
    ∃ M : Fin 12 → Matrix (X → Fin d) (X → Fin d) ℂ,
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      (∀ i, M i ∈ Matrix.unitaryGroup (X → Fin d) ℂ) ∧
      (∀ i, ∃ W : Matrix
          ({x : X // x ∈ torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
            (torusSweptPhysicalBRouteVertex v i.castSucc)} → Fin d)
          ({x : X // x ∈ torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
            (torusSweptPhysicalBRouteVertex v i.castSucc)} → Fin d) ℂ,
        W ∈ Matrix.unitaryGroup _ ℂ ∧
          (M i = regionLocalTerm (torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
              (torusSweptPhysicalBRouteVertex v i.castSucc)) W ∨
            M i = (regionLocalTerm (torusVacantPlaquetteMoveRegion (sweptPhysicalBRouteDirection i)
              (torusSweptPhysicalBRouteVertex v i.castSucc)) W).conjTranspose)) ∧
      torusSweptPhysicalRouteProduct M 12 ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ g h : G,
        let U := torusSweptPhysicalRouteProduct M 12
        let ψ₀ := stateCoeff (groupBondTensor
          (regularTwistedSite a (torusSweptStringInitialOperators v g h)))
        let ψ₁₂ := stateCoeff (groupBondTensor
          (regularTwistedSite a (torusSweptPhysicalRouteOperators v g h 12)))
        U *ᵥ ψ₀ = ψ₁₂ ∧
        ∀ C : Option (ConjClasses G),
          (regionLocalTerm R (Q C) *ᵥ (U *ᵥ ψ₀) =
            if C = some (ConjClasses.mk (g*h*g⁻¹*h⁻¹)) then U *ᵥ ψ₀ else 0) ∧
          Q C * (Matrix.of (fun σ τ => (U *ᵥ ψ₀) (assembleRegionσ R σ τ)) :
            Matrix (RegionPhysicalConfig (d := d) R)
              (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ) =
            if C = some (ConjClasses.mk (g*h*g⁻¹*h⁻¹)) then
              Matrix.of (fun σ τ => (U *ᵥ ψ₀) (assembleRegionσ R σ τ)) else 0 := by
  classical
  dsimp only
  obtain ⟨M,hM,hlocal,_,hprefix⟩ :=
    IsGIsometric.exists_unitary_torusSweptPhysicalRoute a ha v
  obtain ⟨Q,hQh,hQm,hQsum,_,hcut⟩ :=
    IsGIsometric.exists_torusSweptRouteReunion_physicalMeasurement a ha v
  refine ⟨M,Q,hM,hlocal,(hprefix 12 (by omega)).1,hQh,hQm,hQsum,?_⟩
  intro g h
  have HP := (hprefix 12 (by omega)).2 g h
  refine ⟨HP,fun C => ?_⟩
  have hid : regularRegionBondExtension (torusSweptRouteReunionRegion v)
      (torusSweptPhysicalRouteOperators v g h 12)
      (torusSweptPhysicalRouteOperators v g h 12) =
        torusSweptPhysicalRouteOperators v g h 12 := by
    funext e
    simp only [regularRegionBondExtension, ite_self]
  have HC := hcut g h (torusSweptPhysicalRouteOperators v g h 12) C
  rw [hid] at HC
  constructor
  · rw [HP]
    exact global_eigen_of_cut _ _ _ _ HC
  · rw [HP]
    exact HC
end TNLean.PEPS
