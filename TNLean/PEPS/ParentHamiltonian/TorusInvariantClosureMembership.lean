/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusInsertedGraphNetwork
import TNLean.PEPS.GraphInsertedRegionSupport
import TNLean.PEPS.TorusClosureSeams
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian

/-!
# Commuting closures satisfy the actual torus plaquette parents

Move the two commuting seams beyond the selected plaquette. Their matrices
are then the identity on every internal bond, while arbitrary crossing-bond
matrices are absorbed by the virtual boundary condition. Only the native
four-leg virtual invariance is used, with arbitrary finite virtual alphabet.
Source: SCP10, Theorem 5.7 and the seam deformation `eq:2d:move-strings`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "TG" => torusGraph width height

private theorem zmod_add_two_ne {n : ℕ} [NeZero n] [Fact (2 < n)] (x : ZMod n) :
    x + 2 ≠ x ∧ x + 2 ≠ x + 1 := by
  have hn : 2 < n := Fact.out
  have htwo : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 n).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hone : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 1 n).mp (by simp at h)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  constructor
  · simpa using htwo
  · intro h
    have hh : (2 : ZMod n) = 1 := add_left_cancel h
    apply hone
    linear_combination hh

private theorem torusPlaquetteRegion_fst (v p : TV) (hp : p ∈ torusPlaquetteRegion v) :
    p.1 = v.1 ∨ p.1 = v.1 + 1 := by
  simp only [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem torusPlaquetteRegion_snd (v p : TV) (hp : p ∈ torusPlaquetteRegion v) :
    p.2 = v.2 ∨ p.2 = v.2 + 1 := by
  simp only [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

variable {G X : Type*} [Group G] [Fintype X] [DecidableEq X]

/-- The shifted commuting seams can avoid every internal edge of any selected
plaquette, including when a torus period is three.
Source: SCP10, the local seam deformation in Theorem 5.7. -/
theorem torusGraphBondMatrix_closureAt_eq_one_on_plaquette_internal
    (U : G →* Matrix X X ℂ) (g h : G) (v : TV) (e : Edge TG)
    (ht : e.1.1 ∈ torusPlaquetteRegion v) (hh : e.1.2 ∈ torusPlaquetteRegion v) :
    torusGraphBondMatrix (torusHorizontalClosureAt U h (v.1 + 2))
      (torusVerticalClosureAt U g (v.2 + 2)) e = 1 := by
  obtain ⟨p, rfl⟩ := torusEdgeEquiv.surjective e
  rcases p with p | p
  · change (torusRightEdge p).1.1 ∈ torusPlaquetteRegion v at ht
    change (torusRightEdge p).1.2 ∈ torusPlaquetteRegion v at hh
    have hp : (p.1 + 1, p.2) ∈ torusPlaquetteRegion v := by
      rcases Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ht' | hh'
      · simpa only [torusRightEdge, ht'.2] using hh
      · simpa only [torusRightEdge, hh'.1] using ht
    have hne : p.1 + 1 ≠ v.1 + 2 := by
      intro he
      rcases torusPlaquetteRegion_fst v _ hp with hx | hx
      · exact (zmod_add_two_ne v.1).1 (he.symm.trans hx)
      · exact (zmod_add_two_ne v.1).2 (he.symm.trans hx)
    change torusGraphBondMatrix _ _ (torusRightEdge p) = _
    simp [torusHorizontalClosureAt, hne]
  · change (torusUpEdge p).1.1 ∈ torusPlaquetteRegion v at ht
    change (torusUpEdge p).1.2 ∈ torusPlaquetteRegion v at hh
    have hp : (p.1, p.2 + 1) ∈ torusPlaquetteRegion v := by
      rcases Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ht' | hh'
      · simpa only [torusUpEdge, ht'.2] using hh
      · simpa only [torusUpEdge, hh'.1] using ht
    have hne : p.2 + 1 ≠ v.2 + 2 := by
      intro he
      rcases torusPlaquetteRegion_snd v _ hp with hy | hy
      · exact (zmod_add_two_ne v.2).1 (he.symm.trans hy)
      · exact (zmod_add_two_ne v.2).2 (he.symm.trans hy)
    change torusGraphBondMatrix _ _ (torusUpEdge p) = _
    simp [torusVerticalClosureAt, hne]


variable {d : ℕ}

/-- Every local slice of a commuting closure lies in the original plaquette
range. Only native virtual invariance is required.
Source: SCP10, the local sufficiency argument in Theorem 5.7. -/
theorem torusGClosure_slice_mem_plaquetteGroundSpace_of_invariant
    (U : G →* Matrix X X ℂ) (a : X → X → X → X → Fin d → ℂ)
    (ha : ∀ k, siteMap a ∘ₗ torusLegRep U k = siteMap a)
    (g h : G) (hgh : Commute g h) (v : TV)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ torusPlaquetteRegion v)) :
    (fun σ => torusGClosure U a g h (assembleRegionσ (torusPlaquetteRegion v) σ τ)) ∈
      regionGroundSpace (groupBondTensor (torusNativeIncidentSite a)) (torusPlaquetteRegion v) := by
  classical
  have heq : torusGClosure (width := width) (height := height) U a g h =
      graphInsertedBondNetwork
        (torusGraphBondMatrix (torusHorizontalClosureAt U h (v.1 + 2))
          (torusVerticalClosureAt U g (v.2 + 2))) (torusNativeIncidentSite a) := by
    funext σ
    rw [← torusBondNetwork_closureAt_eq_torusGClosure U a ha g h hgh (v.1 + 2) (v.2 + 2),
      torusBondNetwork_eq_graphInsertedBondNetwork]
  rw [heq]
  exact graphInsertedBondNetwork_slice_mem_regionGroundSpace_of_internal_eq_one _ _ _
    (torusGraphBondMatrix_closureAt_eq_one_on_plaquette_internal U g h v) τ

/-- A commuting closure satisfies all the actual plaquette boundary conditions.
Source: SCP10, the inclusion in Theorem 5.7, without semi-regularity. -/
theorem torusGClosure_mem_torusParentGroundSpace_of_invariant
    (U : G →* Matrix X X ℂ) (a : X → X → X → X → Fin d → ℂ)
    (ha : ∀ k, siteMap a ∘ₗ torusLegRep U k = siteMap a)
    (g h : G) (hgh : Commute g h) :
    torusGClosure (width := width) (height := height) U a g h ∈
      regionParentGroundSpace (groupBondTensor (torusNativeIncidentSite a))
        torusPlaquetteRegion := by
  simp only [regionParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap]
  intro v τ
  exact torusGClosure_slice_mem_plaquetteGroundSpace_of_invariant U a ha g h hgh v τ

/-- Every actual plaquette parent annihilates a commuting native closure.
Source: SCP10, the inclusion in Theorem 5.7. -/
theorem torusParent_annihilates_torusGClosure_of_invariant
    (U : G →* Matrix X X ℂ) (a : X → X → X → X → Fin d → ℂ)
    (ha : ∀ k, siteMap a ∘ₗ torusLegRep U k = siteMap a)
    (g h : G) (hgh : Commute g h) (v : TV)
    (P : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) P) :
    regionLocalTerm (torusPlaquetteRegion v) P *ᵥ torusGClosure U a g h = 0 := by
  apply (regionLocalTerm_mulVec_eq_zero_iff _ _ hP _).mpr
  exact torusGClosure_slice_mem_plaquetteGroundSpace_of_invariant U a ha g h hgh v

/-- Commuting native closures belong to the kernel of every genuine positive
plaquette parent Hamiltonian. Source: SCP10, the inclusion in Theorem 5.7. -/
theorem torusParentHamiltonian_annihilates_torusGClosure_of_invariant
    (U : G →* Matrix X X ℂ) (a : X → X → X → X → Fin d → ℂ)
    (ha : ∀ k, siteMap a ∘ₗ torusLegRep U k = siteMap a)
    (P : (v : TV) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) (P v))
    (g h : G) (hgh : Commute g h) :
    regionParentHamiltonian torusPlaquetteRegion P *ᵥ torusGClosure U a g h = 0 := by
  apply (regionParentHamiltonian_mulVec_eq_zero_iff _ _ (fun v => (hP v).1) _).mpr
  intro v
  exact torusParent_annihilates_torusGClosure_of_invariant U a ha g h hgh v (P v) (hP v)

/-- The span of commuting closures is contained in the actual native plaquette
parent kernel for any invariant site and any finite virtual representation.
Source: SCP10, the inclusion in Theorem 5.7. -/
theorem span_torusGClosure_commuting_le_torusParentKernel_of_invariant
    (U : G →* Matrix X X ℂ) (a : X → X → X → X → Fin d → ℂ)
    (ha : ∀ k, siteMap a ∘ₗ torusLegRep U k = siteMap a)
    (P : (v : TV) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
      torusGClosure (width := width) (height := height) U a p.1.1 p.1.2)) ≤
      (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker := by
  apply Submodule.span_le.mpr
  rintro ψ ⟨p, rfl⟩
  exact torusParentHamiltonian_annihilates_torusGClosure_of_invariant
    U a ha P hP p.1.1 p.1.2 p.2

end TNLean.PEPS
