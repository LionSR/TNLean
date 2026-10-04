/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveVirtualComparison
import TNLean.PEPS.RegularOpenRegion
import TNLean.PEPS.RegularSiteGram
import TNLean.PEPS.TorusPhysicalMap
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalDeformation

/-!
# G-injectivity under physical maps

A physical linear map preserves virtual invariance. For a G-injective tensor
and a finite group, it preserves G-injectivity precisely when it is injective
on the original physical range. Isometries preserve the invariant-space inner
products, so they also preserve G-isometry.

Source: SCP10, arXiv:1001.3807, Definition 5.1, lines 1278–1296, and the
physical changes of coordinates in Observation `obs:iso:accessible-virt`,
lines 1765–1820. These are local consequences and assert no classification
of virtual bond representations.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

section LinearMaps

variable {G W P Q : Type*} [Group G]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
variable [AddCommGroup Q] [Module ℂ Q]
variable {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P}

/-- Every physical linear map preserves the virtual invariance of a tensor.
Source: SCP10, Definition 5.1(i), lines 1278–1287. -/
theorem comp_invariant_of_invariant (F : P →ₗ[ℂ] Q)
    (hT : ∀ g, T ∘ₗ ρ g = T) : ∀ g, (F ∘ₗ T) ∘ₗ ρ g = F ∘ₗ T := by
  intro g
  rw [LinearMap.comp_assoc, hT g]

/-- A physical map injective on the physical range preserves G-injectivity.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_of_injOn_range (hT : IsGInjective ρ T)
    (F : P →ₗ[ℂ] Q) (hF : Set.InjOn F T.range) : IsGInjective ρ (F ∘ₗ T) := by
  refine ⟨comp_invariant_of_invariant F hT.invariant, ?_⟩
  intro x hx hzero
  apply hT.injOn_invariants x hx
  exact hF (T.mem_range_self x) T.range.zero_mem (hzero.trans (map_zero F).symm)

/-- Injective physical maps preserve G-injectivity.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_of_injective (hT : IsGInjective ρ T)
    (F : P →ₗ[ℂ] Q) (hF : Function.Injective F) : IsGInjective ρ (F ∘ₗ T) :=
  hT.comp_of_injOn_range F hF.injOn

/-- An invertible physical change of coordinates preserves G-injectivity.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_equiv (hT : IsGInjective ρ T) (F : P ≃ₗ[ℂ] Q) :
    IsGInjective ρ (F.toLinearMap ∘ₗ T) :=
  hT.comp_of_injective F.toLinearMap F.injective

/-- An invertible physical change of coordinates preserves G-injectivity in
both directions. Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem isGInjective_comp_equiv_iff (F : P ≃ₗ[ℂ] Q) :
    IsGInjective ρ (F.toLinearMap ∘ₗ T) ↔ IsGInjective ρ T := by
  constructor
  · intro h
    have h' := h.comp_equiv F.symm
    simpa only [← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp] using h'
  · intro h
    exact h.comp_equiv F

/-- For a finite group, G-injectivity after a physical map is equivalent to
injectivity of that map on the original physical range.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_iff_injOn_range [Finite G] (hT : IsGInjective ρ T)
    (F : P →ₗ[ℂ] Q) : IsGInjective ρ (F ∘ₗ T) ↔ Set.InjOn F T.range := by
  constructor
  · intro hFT
    rw [← LinearMap.disjoint_ker_iff_injOn, LinearMap.disjoint_ker]
    intro y hy hFy
    obtain ⟨x, hx⟩ := hT.bijective_invariants_rangeRestrict.surjective ⟨y, hy⟩
    have hTx : T x = y := congrArg Subtype.val hx
    have hzero : (F ∘ₗ T) x = 0 := by
      change F (T x) = 0
      rw [hTx, hFy]
    have hxzero := hFT.injOn_invariants x x.2 hzero
    rw [← hTx, hxzero, map_zero]
  · exact hT.comp_of_injOn_range F

/-- Equivalently, the physical map must have no kernel inside the tensor's range.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_iff_range_inf_ker_eq_bot [Finite G] (hT : IsGInjective ρ T)
    (F : P →ₗ[ℂ] Q) : IsGInjective ρ (F ∘ₗ T) ↔ T.range ⊓ F.ker = ⊥ := by
  rw [hT.comp_iff_injOn_range, ← LinearMap.disjoint_ker_iff_injOn, disjoint_iff]

/-- The same criterion expressed as injectivity of the restriction to the range.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_iff_injective_rangeSubtype [Finite G] (hT : IsGInjective ρ T)
    (F : P →ₗ[ℂ] Q) :
    IsGInjective ρ (F ∘ₗ T) ↔ Function.Injective (F ∘ₗ T.range.subtype) := by
  rw [hT.comp_iff_injOn_range]
  constructor
  · intro hF x y hxy
    apply Subtype.ext
    exact hF x.2 y.2 hxy
  · intro hF x hx y hy hxy
    exact congrArg Subtype.val (hF (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

end LinearMaps

section VirtualComparison

variable {G H W Z P Q : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
variable [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
variable {ρ : Representation ℂ G W} {σ : Representation ℂ H Z}
variable {T : W →ₗ[ℂ] P} {S : Z →ₗ[ℂ] P}

/-- Applying the same injective physical map to two tensors leaves their
virtual comparison unchanged. Source: local consequence of SCP10,
Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.virtualEquiv_comp_of_injective
    (hT : IsGInjective ρ T) (hS : IsGInjective σ S) (hRange : T.range = S.range)
    (F : P →ₗ[ℂ] Q) (hF : Function.Injective F) :
    (hT.comp_of_injective F hF).virtualEquiv (hS.comp_of_injective F hF)
      (by rw [LinearMap.range_comp, LinearMap.range_comp, hRange]) =
        hT.virtualEquiv hS hRange := by
  apply LinearEquiv.toLinearMap_injective
  apply hT.virtualEquiv_unique hS hRange
  intro x
  apply hF
  exact (hT.comp_of_injective F hF).virtualEquiv_apply (hS.comp_of_injective F hF) _ x

end VirtualComparison

section Isometries

variable {G ι κ ν : Type*} [Group G] [Fintype ι] [Fintype κ] [Fintype ν]
variable {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}

/-- Physical maps preserving inner products preserve G-isometry with the same
positive normalization factor. Source: SCP10, Definition `def:iso:isopeps`,
lines 1692–1697, and Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem IsGIsometric.comp_of_inner_eq (hT : IsGIsometric ρ T)
    (F : (κ → ℂ) →ₗ[ℂ] (ν → ℂ))
    (hF : ∀ x y, star (F x) ⬝ᵥ F y = star x ⬝ᵥ y) :
    IsGIsometric ρ (F ∘ₗ T) := by
  have hFinj : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    intro x hx
    apply dotProduct_star_self_eq_zero.mp
    simpa only [hx, star_zero, zero_dotProduct] using (hF x x).symm
  refine ⟨hT.toIsGInjective.comp_of_injective F hFinj, ?_⟩
  obtain ⟨c, hc, hinner⟩ := hT.exists_inner_eq
  refine ⟨c, hc, fun x hx y hy => ?_⟩
  exact (hF (T x) (T y)).trans (hinner x hx y hy)

/-- Rectangular physical isometries preserve G-isometry.
Source: SCP10, Definition `def:iso:isopeps`, lines 1692–1697, and
Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem IsGIsometric.comp_isometry (hT : IsGIsometric ρ T)
    (F : Matrix ν κ ℂ) [DecidableEq κ] (hF : F.IsIsometry) :
    IsGIsometric ρ (Matrix.mulVecLin F ∘ₗ T) := by
  classical
  apply hT.comp_of_inner_eq
  intro x y
  change star (F *ᵥ x) ⬝ᵥ F *ᵥ y = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hF, Matrix.vecMul_one]

/-- An invertible physical isometry preserves G-isometry in both directions.
Source: SCP10, Definition `def:iso:isopeps`, lines 1692–1697. -/
theorem isGIsometric_comp_equiv_iff (F : (κ → ℂ) ≃ₗ[ℂ] (ν → ℂ))
    (hF : ∀ x y, star (F x) ⬝ᵥ F y = star x ⬝ᵥ y) :
    IsGIsometric ρ (F.toLinearMap ∘ₗ T) ↔ IsGIsometric ρ T := by
  constructor
  · intro h
    have hInv : ∀ x y, star (F.symm x) ⬝ᵥ F.symm y = star x ⬝ᵥ y := by
      intro x y
      simpa only [LinearEquiv.apply_symm_apply] using (hF (F.symm x) (F.symm y)).symm
    have h' := h.comp_of_inner_eq F.symm.toLinearMap hInv
    simpa only [← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp] using h'
  · intro h
    exact h.comp_of_inner_eq F.toLinearMap hF

end Isometries

section FourLegSites

variable {G Bond Phys Out : Type*} [Group G] [Fintype Bond] [Fintype Phys]
variable {ρ : Representation ℂ G ((Bond × Bond × Bond × Bond) → ℂ)}
variable {a : Bond → Bond → Bond → Bond → Phys → ℂ}

/-- Injective physical maps preserve G-injectivity of the four-leg site tensor.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.physicalMapSite (ha : IsGInjective ρ (siteMap a))
    (F : Matrix Out Phys ℂ) (hF : Function.Injective (Matrix.mulVecLin F)) :
    IsGInjective ρ (siteMap (physicalMapSite F a)) := by
  rw [siteMap_physicalMapSite]
  exact ha.comp_of_injective _ hF

/-- Physical isometries preserve G-isometry of the four-leg site tensor.
Source: SCP10, Definition `def:iso:isopeps`, lines 1692–1697. -/
theorem IsGIsometric.physicalMapSite [Fintype Out]
    (ha : IsGIsometric ρ (siteMap a)) (F : Matrix Out Phys ℂ)
    [DecidableEq Phys] (hF : F.IsIsometry) :
    IsGIsometric ρ (siteMap (physicalMapSite F a)) := by
  rw [siteMap_physicalMapSite]
  exact ha.comp_isometry F hF

end FourLegSites

/-- Apply a physical matrix to a site with an arbitrary incident-leg set.
Source: SCP10, physical changes of coordinates in Observation
`obs:iso:accessible-virt`, lines 1765–1820. -/
noncomputable def regularPhysicalMapSite {G ι κ ν : Type*} [Fintype κ]
    (F : Matrix ν κ ℂ) (a : (ι → G) → κ → ℂ) (η : ι → G) (t : ν) : ℂ :=
  ∑ s, F t s * a η s

section RegularSites

variable {G ι κ ν : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ν]

omit [Group G] [DecidableEq G] [Fintype ν] in
/-- The physical change of coefficients composes the regular site map. -/
theorem regularSiteMap_regularPhysicalMapSite (F : Matrix ν κ ℂ) (a : (ι → G) → κ → ℂ) :
    regularSiteMap (regularPhysicalMapSite F a) = Matrix.mulVecLin F ∘ₗ regularSiteMap a := by
  change Matrix.mulVecLin (F * Matrix.of (fun s η => a η s)) = _
  exact Matrix.mulVecLin_mul _ _

omit [DecidableEq G] [Fintype ν] in
/-- Injective physical maps preserve regular G-injective sites.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.regularPhysicalMapSite {a : (ι → G) → κ → ℂ}
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a))
    (F : Matrix ν κ ℂ) (hF : Function.Injective (Matrix.mulVecLin F)) :
    IsGInjective (regularLegRepresentation ι) (regularSiteMap (regularPhysicalMapSite F a)) := by
  rw [regularSiteMap_regularPhysicalMapSite]
  exact ha.comp_of_injective _ hF

omit [DecidableEq G] in
/-- Physical isometries preserve regular G-isometric sites.
Source: SCP10, Definition `def:iso:isopeps`, lines 1692–1697. -/
theorem IsGIsometric.regularPhysicalMapSite {a : (ι → G) → κ → ℂ}
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (F : Matrix ν κ ℂ) [DecidableEq κ] (hF : F.IsIsometry) :
    IsGIsometric (regularLegRepresentation ι) (regularSiteMap (regularPhysicalMapSite F a)) := by
  rw [regularSiteMap_regularPhysicalMapSite]
  exact ha.comp_isometry F hF

end RegularSites

section GraphSites

variable {V G : Type*} [Fintype V] [LinearOrder V] [Group G] [Fintype G] [DecidableEq G]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d e : ℕ}

omit [Fintype V] [Group G] [DecidableEq G] in
/-- Physical deformation in finite bond coordinates agrees with deformation of
the group-labelled local sites. Source: SCP10, physical changes of coordinates
in Observation `obs:iso:accessible-virt`, lines 1765–1820. -/
theorem physicalDeform_groupBondTensor
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : V → Matrix (Fin e) (Fin d) ℂ) :
    physicalDeform (groupBondTensor a) F =
      groupBondTensor (fun v => regularPhysicalMapSite (F v) (a v)) := rfl

omit [DecidableEq G] in
/-- An invertible physical map at each graph vertex preserves regular G-injectivity
of the complete tensor family. Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem isGInjective_regularPhysicalMapSite_family
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (F : V → (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ)) :
    ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (regularPhysicalMapSite (LinearMap.toMatrix' (F v).toLinearMap) (a v))) := by
  intro v
  apply (ha v).regularPhysicalMapSite
  change Function.Injective (Matrix.toLin' (LinearMap.toMatrix' (F v).toLinearMap))
  rw [Matrix.toLin'_toMatrix']
  exact (F v).injective

omit [DecidableEq G] in
/-- Physical isometries at every graph vertex preserve regular G-isometry of
the whole site family. Source: SCP10, Definition `def:iso:isopeps`, lines 1692–1697. -/
theorem isGIsometric_regularPhysicalMapSite_family
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v)) (regularSiteMap (a v)))
    (F : V → Matrix (Fin e) (Fin d) ℂ) (hF : ∀ v, (F v).IsIsometry) :
    ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (regularPhysicalMapSite (F v) (a v))) :=
  fun v => (ha v).regularPhysicalMapSite (F v) (hF v)

end GraphSites

end TNLean.PEPS
