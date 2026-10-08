/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusParentGroundStateObservables

/-!
# Arbitrary parent ground-state observable regressions

The inputs below are arbitrary physical vectors annihilated by the genuine
positive native plaquette parent Hamiltonian. No closure coefficients, closure
span membership, cut nonvanishing, or boundary rank are supplied. The
non-isometric test assumes only G-injectivity. The zero vector is allowed in
the coefficient-extraction regression.
-/

namespace TNLeanTest.ParentGroundStateObservables

open TNLean.PEPS
open scoped BigOperators Matrix ComplexOrder

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

variable {a : G → G → G → G → Fin d → ℂ}

noncomputable local instance : DecidablePred (fun p : G × G => Commute p.1 p.2) :=
  fun _ => Classical.propDecidable _

/-- Regression from the actual parent equation. -/
theorem arbitraryKernelExpansion
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (ψ : (X → Fin d) → ℂ)
    (hzero : regionParentHamiltonian torusPlaquetteRegion P *ᵥ ψ = 0) :
    ∃ μ : {p : G × G // Commute p.1 p.2} → ℂ,
      ∑ p, μ p • torusGClosure (leftRegularMatrix G) a p.1.1 p.1.2 = ψ :=
  ha.exists_torusGClosure_sum_of_mem_parentKernel P hP ψ hzero

/-- Regression from the actual parent equation. -/
theorem zeroKernelExpansion
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ μ : {p : G × G // Commute p.1 p.2} → ℂ,
      ∑ p, μ p • torusGClosure (width := width) (height := height)
        (leftRegularMatrix G) a p.1.1 p.1.2 = 0 :=
  ha.exists_torusGClosure_sum_of_mem_parentKernel P hP 0 (Submodule.zero_mem _)

/-- Regression from the actual parent equation. -/
theorem arbitraryKernelCommonDensity
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (ψ φ : (X → Fin d) → ℂ)
    (hψ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ ψ = 0)
    (hφ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ φ = 0)
    (hneψ : ψ ≠ 0) (hneφ : φ ≠ 0) :
    let A : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => ψ (assembleRegionσ R σ τ)
    let B : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => φ (assembleRegionσ R σ τ)
    (A * A.conjTranspose).trace⁻¹ • (A * A.conjTranspose) =
      (B * B.conjTranspose).trace⁻¹ • (B * B.conjTranspose) := by
  obtain ⟨ρ, hρ⟩ := ha.exists_torusParentKernel_common_density_of_isSimplyConnected P hP R hR hSC
  exact (hρ ψ hψ hneψ).2.1.trans (hρ φ hφ hneφ).2.1.symm

/-- Regression from the actual parent equation. -/
theorem arbitraryKernelLocalExpectations
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (ψ φ : (X → Fin d) → ℂ)
    (hψ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ ψ = 0)
    (hφ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ φ = 0)
    (hneψ : ψ ≠ 0) (hneφ : φ ≠ 0)
    (O : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    let A : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => ψ (assembleRegionσ R σ τ)
    let B : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => φ (assembleRegionσ R σ τ)
    (O * (normalizedPureCutMatrix B * (normalizedPureCutMatrix B).conjTranspose)).trace =
      (O * (normalizedPureCutMatrix A * (normalizedPureCutMatrix A).conjTranspose)).trace :=
  (ha.torusParentKernel_local_equivalence_of_isSimplyConnected
    P hP R hR hSC ψ φ hψ hφ hneψ hneφ).1 O

/-- Regression from the actual parent equation. -/
theorem arbitraryKernelStripeUnitary
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (ψ φ : (X → Fin d) → ℂ)
    (hψ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ ψ = 0)
    (hφ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ φ = 0)
    (hneψ : ψ ≠ 0) (hneφ : φ ≠ 0) :
    let R := torusContiguousRectangle (width := width) (height := height)
      1 1 (width - 1) (height - 1)
    let A : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => ψ (assembleRegionσ R σ τ)
    let B : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => φ (assembleRegionσ R σ τ)
    ∃ U : Matrix.unitaryGroup (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ,
      normalizedPureCutMatrix B = normalizedPureCutMatrix A *
        (U : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
          (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ).transpose :=
  ha.torusParentKernel_stripe_local_equivalence P hP ψ φ hψ hφ hneψ hneφ

/-- Regression from the actual parent equation. -/
theorem arbitraryKernelZeroEntropy
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (ψ : (X → Fin d) → ℂ)
    (hψ : regionParentHamiltonian torusPlaquetteRegion P *ᵥ ψ = 0) (hne : ψ ≠ 0) :
    let _ := Classical.decEq (Fin d)
    let b := Fintype.card {f : Edge Γₜ // IsRegionBoundaryEdge R f}
    let M := physicalCutMatrix (fun v => v ∈ R) ψ
    let ρ := (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose)
    ρ.rank = Fintype.card G ^ (b - 1) ∧
      ∃ hρ : ρ.IsHermitian,
        renyiEntropy ρ hρ 0 = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) := by
  have h := ha.torusParentKernel_rank_zeroEntropy_of_isSimplyConnected P hP R hR hSC ψ hψ hne
  exact ⟨h.2.2.2.1, h.2.2.2.2.2⟩

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.IsGInjective.exists_torusGClosure_sum_of_mem_parentKernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGInjective.exists_torusGClosure_sum_of_mem_parentKernel

/--
info: 'TNLean.PEPS.IsGIsometric.exists_torusParentKernel_common_density_of_isSimplyConnected'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.exists_torusParentKernel_common_density_of_isSimplyConnected

/--
info: 'TNLean.PEPS.IsGIsometric.torusParentKernel_local_equivalence_of_isSimplyConnected'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.torusParentKernel_local_equivalence_of_isSimplyConnected

/--
info: 'TNLean.PEPS.IsGIsometric.torusParentKernel_stripe_local_equivalence'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.torusParentKernel_stripe_local_equivalence

/--
info: 'TNLean.PEPS.IsGInjective.torusParentKernel_rank_zeroEntropy_of_isSimplyConnected'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGInjective.torusParentKernel_rank_zeroEntropy_of_isSimplyConnected

/--
info: 'TNLeanTest.ParentGroundStateObservables.arbitraryKernelExpansion'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms arbitraryKernelExpansion

/--
info: 'TNLeanTest.ParentGroundStateObservables.zeroKernelExpansion'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms zeroKernelExpansion

/--
info: 'TNLeanTest.ParentGroundStateObservables.arbitraryKernelCommonDensity'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms arbitraryKernelCommonDensity

/--
info: 'TNLeanTest.ParentGroundStateObservables.arbitraryKernelLocalExpectations'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms arbitraryKernelLocalExpectations

/--
info: 'TNLeanTest.ParentGroundStateObservables.arbitraryKernelStripeUnitary'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms arbitraryKernelStripeUnitary

/--
info: 'TNLeanTest.ParentGroundStateObservables.arbitraryKernelZeroEntropy'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms arbitraryKernelZeroEntropy

end TNLeanTest.ParentGroundStateObservables
