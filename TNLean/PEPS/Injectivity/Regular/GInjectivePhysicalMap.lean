/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.GInjective.GInjectiveVirtualComparison
import TNLean.PEPS.Tensor.GraphState.RegularOpenRegion
import TNLean.PEPS.Injectivity.Regular.RegularSiteGram
import TNLean.PEPS.Injectivity.Closure.TorusPhysicalMap
import TNLean.PEPS.Tensor.Region.RegionPhysicalMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

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

It also contains the following results.

* `TNLean.PEPS.IsGInjective.exists_normalized_isGIsometric_physicalEquiv`: a normalized
  invariant-space form of G-injective tensors.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*

## Invertible physical comparison of G-injective tensor maps

Two G-injective maps for the same virtual representation identify the same
invariant virtual space with their physical ranges. When these ranges are
finite-dimensional, their range comparison extends to an invertible map of a
common physical space. More generally, equal finite physical dimensions allow
an invertible comparison between different physical spaces.

These are local consequences of SCP10, arXiv:1001.3807, Definition 5.1,
lines 1278–1296. The comparison acts on physical coordinates; it is not a
virtual gauge relation inferred from equality of closed states.

### References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

section GInjectivePhysicalMap

section

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

/-- A virtual change of coordinates intertwining two representations preserves
G-injectivity. Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.comp_virtualEquiv {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {ρ' : Representation ℂ G W'} (hT : IsGInjective ρ T) (E : W' ≃ₗ[ℂ] W)
    (hE : ∀ g x, E (ρ' g x) = ρ g (E x)) : IsGInjective ρ' (T ∘ₗ E.toLinearMap) := by
  refine ⟨fun g => LinearMap.ext fun x => ?_, fun x hx hzero => E.injective ?_⟩
  · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hE] using
      LinearMap.congr_fun (hT.invariant g) (E x)
  · rw [map_zero]
    exact hT.injOn_invariants (E x) (fun g => by rw [← hE, hx g]) hzero

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

end

section

namespace TNLean.PEPS

variable {G W P Q : Type*} [Group G] [Finite G]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
variable [AddCommGroup Q] [Module ℂ Q]
variable {ρ : Representation ℂ G W} {T : W →ₗ[ℂ] P}

/-- Finite-dimensional physical ranges of two G-injective maps for the same
virtual representation are related by an ambient physical automorphism.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.exists_physicalEquiv {S : W →ₗ[ℂ] P}
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S) [Module.Finite ℂ T.range] :
    ∃ F : P ≃ₗ[ℂ] P, F.toLinearMap ∘ₗ T = S := by
  let _ := Fintype.ofFinite G
  obtain ⟨F, hF⟩ := Submodule.exists_linearEquiv_restrict_eq (hT.rangeEquiv hS)
  refine ⟨F, LinearMap.ext fun x => ?_⟩
  exact (hF (T.rangeRestrict x)).symm.trans (hT.rangeEquiv_apply hS x)

/-- Equal finite physical dimensions suffice for an invertible physical
comparison even when the ambient physical spaces differ.
Source: local consequence of SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.exists_physicalEquiv_of_finrank_eq {S : W →ₗ[ℂ] Q}
    [Module.Finite ℂ P] [Module.Finite ℂ Q]
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S)
    (hDim : Module.finrank ℂ P = Module.finrank ℂ Q) :
    ∃ F : P ≃ₗ[ℂ] Q, F.toLinearMap ∘ₗ T = S := by
  let E := LinearEquiv.ofFinrankEq P Q hDim
  obtain ⟨L, hL⟩ := hT.exists_physicalEquiv (hS.comp_equiv E.symm)
  refine ⟨L.trans E, LinearMap.ext fun x => ?_⟩
  have h := congrArg E (LinearMap.congr_fun hL x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using h

end TNLean.PEPS

end

end GInjectivePhysicalMap

section GInjectivePhysicalNormalForm

/-!
## A normalized invariant-space form of G-injective tensors

An invertible physical map can turn any finite-dimensional G-injective map
into a map preserving inner products on the invariant virtual space, with
normalization factor one. The construction chooses orthonormal bases of the
invariant virtual space and of the physical range, and extends the resulting
physical range comparison to the full physical space.

Source: local physical filtering from SCP10, arXiv:1001.3807,
Definition 5.1, lines 1278–1296, and Definition `def:iso:isopeps`,
lines 1692–1697. For the regular virtual representation this produces a
normalized G-isometric tensor. It is a physical change of coordinates and
does not claim equality of the original and filtered closed PEPS states.

### References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

private theorem euclideanSubmoduleIsometry_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Submodule ℂ (EuclideanSpace ℂ ι)) (R : Submodule ℂ (EuclideanSpace ℂ κ))
    (J : I ≃ₗᵢ[ℂ] R) (x y : I) :
    inner ℂ (J x : EuclideanSpace ℂ κ) (J y : EuclideanSpace ℂ κ) =
      inner ℂ (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ ι) :=
  LinearIsometryEquiv.inner_map_map (𝕜 := ℂ) (E := I) (E' := R) J x y

variable {G ι κ : Type*} [Group G] [Finite G] [Fintype ι] [Fintype κ]
variable {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- A G-injective map can be normalized on its invariant virtual space by an
invertible physical map. For regular virtual representations this is a
normalized G-isometric tensor. Source: local consequence of SCP10,
Definition 5.1, lines 1278–1296, and Definition `def:iso:isopeps`, lines 1692–1697. -/
theorem IsGInjective.exists_normalized_isGIsometric_physicalEquiv (hT : IsGInjective ρ T) :
    ∃ F : (κ → ℂ) ≃ₗ[ℂ] (κ → ℂ),
      IsGIsometric ρ (F.toLinearMap ∘ₗ T) ∧
      ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants,
        star (F (T x)) ⬝ᵥ F (T y) = star x ⬝ᵥ y := by
  classical
  let _ := Fintype.ofFinite G
  let Eι : EuclideanSpace ℂ ι ≃ₗ[ℂ] (ι → ℂ) := WithLp.linearEquiv 2 ℂ (ι → ℂ)
  let Eκ : EuclideanSpace ℂ κ ≃ₗ[ℂ] (κ → ℂ) := WithLp.linearEquiv 2 ℂ (κ → ℂ)
  let I : Submodule ℂ (EuclideanSpace ℂ ι) := ρ.invariants.map Eι.symm.toLinearMap
  let R : Submodule ℂ (EuclideanSpace ℂ κ) := T.range.map Eκ.symm.toLinearMap
  let eI : ρ.invariants ≃ₗ[ℂ] I := Eι.symm.submoduleMap ρ.invariants
  let eR : T.range ≃ₗ[ℂ] R := Eκ.symm.submoduleMap T.range
  let L : I ≃ₗ[ℂ] R := eI.symm.trans (hT.invariantsRangeEquiv.trans eR)
  obtain ⟨J⟩ : Nonempty (I ≃ₗᵢ[ℂ] R) :=
    ⟨(stdOrthonormalBasis ℂ I).equiv (stdOrthonormalBasis ℂ R) (finCongr L.finrank_eq)⟩
  let p : (ι → ℂ) →ₗ[ℂ] ρ.invariants :=
    ρ.averageMap.codRestrict ρ.invariants ρ.averageMap_invariant
  let S : (ι → ℂ) →ₗ[ℂ] (κ → ℂ) :=
    Eκ.toLinearMap ∘ₗ R.subtype ∘ₗ J.toLinearMap ∘ₗ eI.toLinearMap ∘ₗ p
  have hp (x : ρ.invariants) : p x = x :=
    Subtype.ext (ρ.averageMap_id x x.2)
  have hS (x : ρ.invariants) : S x = Eκ (J (eI x)) := by
    change Eκ (J (eI (p x))) = _
    rw [hp]
  have hAvg : ∀ g : G, ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
    intro g
    change ρ.averageMap * ρ g = ρ.averageMap
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  have hSinv : ∀ g : G, S ∘ₗ ρ g = S := by
    intro g
    apply LinearMap.ext
    intro x
    have hp' : p (ρ g x) = p x := Subtype.ext (LinearMap.congr_fun (hAvg g) x)
    change Eκ (J (eI (p (ρ g x)))) = Eκ (J (eI (p x)))
    rw [hp']
  have hSinj : ∀ x ∈ ρ.invariants, S x = 0 → x = 0 := by
    intro x hx hzero
    let xI : ρ.invariants := ⟨x, hx⟩
    have hJ : J (eI xI) = 0 := by
      apply Subtype.ext
      apply Eκ.injective
      exact (hS xI).symm.trans (hzero.trans (map_zero Eκ).symm)
    have heI : eI xI = 0 := J.injective (hJ.trans (map_zero J).symm)
    exact congrArg Subtype.val (eI.injective (heI.trans (map_zero eI).symm))
  have hInner : ∀ x ∈ ρ.invariants, ∀ y ∈ ρ.invariants,
      star (S x) ⬝ᵥ S y = star x ⬝ᵥ y := by
    intro x hx y hy
    let xI : ρ.invariants := ⟨x, hx⟩
    let yI : ρ.invariants := ⟨y, hy⟩
    have h := euclideanSubmoduleIsometry_inner I R J (eI xI) (eI yI)
    change Eκ (J (eI yI)) ⬝ᵥ star (Eκ (J (eI xI))) = y ⬝ᵥ star x at h
    rw [hS xI, hS yI]
    simpa only [dotProduct_comm] using h
  have hSIso : IsGIsometric ρ S := by
    refine ⟨⟨hSinv, hSinj⟩, 1, zero_lt_one, ?_⟩
    simpa only [Complex.ofReal_one, one_mul] using hInner
  obtain ⟨F, hF⟩ := hT.exists_physicalEquiv hSIso.toIsGInjective
  refine ⟨F, hF ▸ hSIso, ?_⟩
  intro x hx y hy
  have hFx := LinearMap.congr_fun hF x
  have hFy := LinearMap.congr_fun hF y
  change F (T x) = S x at hFx
  change F (T y) = S y at hFy
  rw [hFx, hFy]
  exact hInner x hx y hy

end TNLean.PEPS

end GInjectivePhysicalNormalForm
