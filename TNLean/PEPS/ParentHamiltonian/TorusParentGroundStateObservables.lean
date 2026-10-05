/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusRegularParentGroundSpace
import TNLean.PEPS.TorusStripeLocalEquivalence
import TNLean.PEPS.RegularGInjectiveSimplyConnectedEntropy

/-!
# Local observables and entropy of every regular torus parent ground state

Membership in the kernel of the actual positive plaquette parent Hamiltonian
supplies a finite commuting-closure expansion. The physical cut of a nonzero
vector is nonzero because restricting and reassembling its configurations
recovers the vector. Consequently the closure-state density, local equivalence,
stripe-unitary, and entropy results apply to every actual parent ground state.
Neither a closure expansion nor a cut-nonvanishing hypothesis is an input.

**Scope restriction (regular native torus):** Both torus periods are at least
three. One regular tensor is repeated at every site. A region has connected occupied
nearest-neighbour graph and simply connected actual closed-cell realization.
The stripe statement uses the two coordinate-zero stripes. The parent terms
are the existing positive interactions whose kernels equal the actual
plaquette ranges. The isometric conclusions use local G-isometry; the rank
and zero-order Rényi entropy conclusion only uses local G-injectivity.
No smaller-period or arbitrary semi-regular extension is claimed. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807v3, Theorem 5.7,
Theorem 6.7, Corollary 6.8, Theorem 6.9, and Corollary 6.10;
local source lines 1995–2090 for the observable and entropy conclusions.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

noncomputable local instance : DecidablePred (fun p : G × G => Commute p.1 p.2) :=
  fun _ => Classical.propDecidable _

/-- Every actual regular parent ground vector has commuting-closure coefficients.
The vector may be zero. Source: SCP10, Theorem 5.7. -/
theorem IsGInjective.exists_torusGClosure_sum_of_mem_parentKernel
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ψ : (X → Fin d) → ℂ)
    (hψ : ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker) :
    ∃ μ : {p : G × G // Commute p.1 p.2} → ℂ,
      ∑ p, μ p • torusGClosure (leftRegularMatrix G) a p.1.1 p.1.2 = ψ := by
  classical
  rw [ha.torusParentKernel_eq_commutingClosureSpan P hP] at hψ
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hψ

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem torusClosureSuperpositionCut_ne_zero_of_sum_ne_zero
    (a : G → G → G → G → Fin d → ℂ)
    {I : Type*} [Fintype I] (pairs : I → G × G) (μ : I → ℂ)
    (R : Finset X)
    (hne : (∑ i, μ i • torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) a (pairs i).1 (pairs i).2) ≠ 0) :
    torusClosureSuperpositionCut a pairs μ R ≠ 0 := by
  intro hzero
  apply hne
  funext σ
  have h := congrFun hzero ((fun v => σ v.1), (fun v => σ v.1))
  have hglue : assembleRegionσ R (fun v => σ v.1) (fun v => σ v.1) = σ := by
    funext v
    simp only [assembleRegionσ]
    split_ifs <;> rfl
  simpa only [torusClosureSuperpositionCut, hglue, Pi.zero_apply] using h

/-- All nonzero vectors in the actual parent kernel have one common normalized
reduced density on a contiguous simply connected region. Its rank is
\(|G|^{b-1}\), its nonzero spectrum is flat, and its von Neumann and every
finite nonnegative-order Rényi entropy equal \((b-1)\log |G|\), where \(b\)
is the actual number of crossing bonds. Source: SCP10, Theorem 6.9. -/
theorem IsGIsometric.exists_torusParentKernel_common_density_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R)) :
    let b := Fintype.card {f : Edge Γₜ // IsRegionBoundaryEdge R f}
    ∃ ρ : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      ∀ ψ : (X → Fin d) → ℂ,
        ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker →
        ψ ≠ 0 →
        let M : Matrix (RegionPhysicalConfig (d := d) R)
            (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
          fun σ τ => ψ (assembleRegionσ R σ τ)
        0 < (M * M.conjTranspose).trace ∧
          (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ ∧
          ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ.rank = Fintype.card G ^ (b - 1) ∧
          ρ * ρ = ((Fintype.card G : ℂ) ^ (b - 1))⁻¹ • ρ ∧
          ∃ hρ : ρ.IsHermitian,
            vonNeumannEntropy ρ hρ = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) ∧
              ∀ α : ℝ, 0 ≤ α →
                renyiEntropy ρ hρ α = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) := by
  classical
  obtain ⟨ρ, hρ⟩ := ha.exists_torusPhysicalCut_common_density_of_isSimplyConnected R hR hSC
  refine ⟨ρ, ?_⟩
  intro ψ hψ hne
  obtain ⟨μ, rfl⟩ := ha.toIsGInjective.exists_torusGClosure_sum_of_mem_parentKernel P hP ψ hψ
  exact hρ Subtype.val (fun p => p.property) μ
    (torusClosureSuperpositionCut_ne_zero_of_sum_ne_zero a Subtype.val μ R hne)

/-- Any two nonzero actual parent ground vectors have identical normalized
local expectations on a contiguous simply connected region, and a unitary
on its physical complement relates their normalized coefficient matrices.
Source: SCP10, Theorem 6.7 and Corollary 6.8. -/
theorem IsGIsometric.torusParentKernel_local_equivalence_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (ψ φ : (X → Fin d) → ℂ)
    (hψ : ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker)
    (hφ : φ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker)
    (hneψ : ψ ≠ 0) (hneφ : φ ≠ 0) :
    let A : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => ψ (assembleRegionσ R σ τ)
    let B : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => φ (assembleRegionσ R σ τ)
    (∀ O : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) R) ℂ,
      (O * (normalizedPureCutMatrix B * (normalizedPureCutMatrix B).conjTranspose)).trace =
        (O * (normalizedPureCutMatrix A * (normalizedPureCutMatrix A).conjTranspose)).trace) ∧
      ∃ U : Matrix.unitaryGroup (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ,
        normalizedPureCutMatrix B = normalizedPureCutMatrix A *
          (U : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
            (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ).transpose := by
  classical
  obtain ⟨μ, rfl⟩ := ha.toIsGInjective.exists_torusGClosure_sum_of_mem_parentKernel P hP ψ hψ
  obtain ⟨ν, rfl⟩ := ha.toIsGInjective.exists_torusGClosure_sum_of_mem_parentKernel P hP φ hφ
  exact ha.torusPhysicalCut_local_equivalence_of_isSimplyConnected R hR hSC
    Subtype.val Subtype.val (fun p => p.property) (fun p => p.property) μ ν
    (torusClosureSuperpositionCut_ne_zero_of_sum_ne_zero a Subtype.val μ R hneψ)
    (torusClosureSuperpositionCut_ne_zero_of_sum_ne_zero a Subtype.val ν R hneφ)

/-- A unitary on the two coordinate-zero width-one stripes relates the
normalized cuts of any two nonzero actual parent ground vectors.
Source: SCP10, Theorem 6.7. -/
theorem IsGIsometric.torusParentKernel_stripe_local_equivalence
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (ψ φ : (X → Fin d) → ℂ)
    (hψ : ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker)
    (hφ : φ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker)
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
          (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ).transpose := by
  classical
  obtain ⟨μ, rfl⟩ := ha.toIsGInjective.exists_torusGClosure_sum_of_mem_parentKernel P hP ψ hψ
  obtain ⟨ν, rfl⟩ := ha.toIsGInjective.exists_torusGClosure_sum_of_mem_parentKernel P hP φ hφ
  exact ha.torusClosureSuperpositionCut_stripe_local_equivalence
    Subtype.val Subtype.val (fun p => p.property) (fun p => p.property) μ ν
    (torusClosureSuperpositionCut_ne_zero_of_sum_ne_zero a Subtype.val μ _ hneψ)
    (torusClosureSuperpositionCut_ne_zero_of_sum_ne_zero a Subtype.val ν _ hneφ)

/-- Every nonzero actual regular G-injective parent ground vector has reduced
rank \(|G|^{b-1}\) and zero-order Rényi entropy \((b-1)\log |G|\) on a
contiguous simply connected region. Local isometry is not assumed.
Source: SCP10, Corollary 6.10. -/
theorem IsGInjective.torusParentKernel_rank_zeroEntropy_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (ψ : (X → Fin d) → ℂ)
    (hψ : ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker)
    (hne : ψ ≠ 0) :
    let _ := Classical.decEq (Fin d)
    let b := Fintype.card {f : Edge Γₜ // IsRegionBoundaryEdge R f}
    let M := physicalCutMatrix (fun v => v ∈ R) ψ
    let ρ := (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose)
    0 < (M * M.conjTranspose).trace ∧ ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ρ.rank = Fintype.card G ^ (b - 1) ∧
      Real.log (ρ.rank : ℝ) = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) ∧
      ∃ hρ : ρ.IsHermitian,
        renyiEntropy ρ hρ 0 = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) := by
  classical
  obtain ⟨μ, hμ⟩ := ha.exists_torusGClosure_sum_of_mem_parentKernel P hP ψ hψ
  simpa only [hμ] using
    ha.torusPhysicalCut_rank_zeroEntropy_of_isSimplyConnected R hR hSC
      Subtype.val (fun p => p.property) μ (by rwa [hμ])

end TNLean.PEPS
