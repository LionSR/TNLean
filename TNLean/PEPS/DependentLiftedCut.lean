/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondLocalInverse

/-!
# Lifted regional contractions with dependent alphabets

A regional tensor network is lifted to all physical sites by retaining the
outside physical configuration as part of one arbitrary joint boundary.
Only tensors belonging to the region are contracted. Every physical slice
inside the region therefore lies in the range of that site's tensor.

The virtual alphabet may depend on the labelled edge, and the physical
alphabet may depend on the vertex. No injectivity or group action is needed
for the local range statement or its consequence for covering regions.

Source: SCP10, arXiv:1001.3807, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*}

/-- Physical configurations on sites outside the selected region. -/
abbrev OutsidePhysicalConfig (R : Finset Vertex) (Phys : Vertex → Type*) :=
  (v : {v // v ∉ R}) → Phys v.1

/-- Retain all outside physical coordinates as one joint configuration. -/
def outsidePhysicalRestriction {Phys : Vertex → Type*} (R : Finset Vertex)
    (σ : (v : Vertex) → Phys v) : OutsidePhysicalConfig R Phys := fun v ↦ σ v.1

variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- The literal lifted contraction, with an arbitrary joint cut and outside
physical boundary and tensor factors only at sites in the region. -/
def liftedCutCoeff
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (M : CutConfig C D × OutsidePhysicalConfig R Phys → ℂ)
    (σ : (v : Vertex) → Phys v) : ℂ :=
  ∑ β : EndpointConfig D,
    (M (cutRestriction D C β, outsidePhysicalRestriction R σ) * cutInteriorWeight D C β) *
      ∏ v ∈ R, A v (endpointSiteEquiv tail head D β v) (σ v)

/-- The linear lifted regional map, retaining arbitrary correlations between
all exposed virtual and outside physical indices. -/
def liftedCutMap
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge) :
    (CutConfig C D × OutsidePhysicalConfig R Phys → ℂ) →ₗ[ℂ]
      (((v : Vertex) → Phys v) → ℂ) where
  toFun := liftedCutCoeff tail head D A R C
  map_add' M N := by
    funext σ
    simp [liftedCutCoeff, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    funext σ
    simp [liftedCutCoeff, mul_assoc, Finset.mul_sum]

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- Evaluation of the lifted regional map is its endpoint contraction. -/
@[simp] theorem liftedCutMap_apply
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (M : CutConfig C D × OutsidePhysicalConfig R Phys → ℂ)
    (σ : (v : Vertex) → Phys v) :
    liftedCutMap tail head D A R C M σ = liftedCutCoeff tail head D A R C M σ := rfl

/-- The actual lifted regional range. -/
def liftedCutSpace
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge) :
    Submodule ℂ (((v : Vertex) → Phys v) → ℂ) :=
  LinearMap.range (liftedCutMap tail head D A R C)

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Edge]
    [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)] in
/-- Updating a physical coordinate in the region leaves its outside
configuration unchanged. -/
theorem outsidePhysicalRestriction_update (R : Finset Vertex)
    {v : Vertex} (hv : v ∈ R) (σ : (v : Vertex) → Phys v) (s : Phys v) :
    outsidePhysicalRestriction R (Function.update σ v s) = outsidePhysicalRestriction R σ := by
  funext w
  change Function.update σ v s w.1 = σ w.1
  have hn : w.1 ≠ v := by
    intro h
    apply w.2
    simpa only [h] using hv
  exact Function.update_of_ne hn _ _

omit [Fintype Vertex] in
/-- A regional lifted vector has every local slice in the tensor range at
each site belonging to the region. -/
theorem liftedCutMap_slice_mem_range
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (M : CutConfig C D × OutsidePhysicalConfig R Phys → ℂ)
    {v : Vertex} (hv : v ∈ R) (σ : (v : Vertex) → Phys v) :
    (fun s ↦ liftedCutMap tail head D A R C M (Function.update σ v s)) ∈
      LinearMap.range (localSiteMap tail head D A v) := by
  classical
  have hsum : (fun s ↦ liftedCutMap tail head D A R C M (Function.update σ v s)) =
      ∑ β : EndpointConfig D,
        ((M (cutRestriction D C β, outsidePhysicalRestriction R σ) * cutInteriorWeight D C β) *
          ∏ w ∈ R.erase v, A w (endpointSiteEquiv tail head D β w) (σ w)) •
          (fun s ↦ A v (endpointSiteEquiv tail head D β v) s) := by
    funext s
    simp only [liftedCutMap_apply, liftedCutCoeff, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, outsidePhysicalRestriction_update R hv]
    apply Finset.sum_congr rfl
    intro β _
    rw [← Finset.mul_prod_erase _ _ hv, Function.update_self]
    have hout : (∏ w ∈ R.erase v,
        A w (endpointSiteEquiv tail head D β w) (Function.update σ v s w)) =
        ∏ w ∈ R.erase v, A w (endpointSiteEquiv tail head D β w) (σ w) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    rw [hout]
    ring
  rw [hsum]
  apply Submodule.sum_mem
  intro β _
  apply Submodule.smul_mem
  refine ⟨Pi.single (endpointSiteEquiv tail head D β v) 1, ?_⟩
  ext s
  simp [localSiteMap_apply, Pi.single_apply]

omit [Fintype Vertex] in
/-- The local-slice conclusion depends only on actual lifted-range membership. -/
theorem slice_mem_range_of_mem_liftedCutSpace
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge) {ψ : ((v : Vertex) → Phys v) → ℂ}
    (hψ : ψ ∈ liftedCutSpace tail head D A R C)
    {v : Vertex} (hv : v ∈ R) (σ : (v : Vertex) → Phys v) :
    (fun s ↦ ψ (Function.update σ v s)) ∈ LinearMap.range (localSiteMap tail head D A v) := by
  obtain ⟨M, rfl⟩ := hψ
  exact liftedCutMap_slice_mem_range tail head D A R C M hv σ

/-- An intersection of actual lifted regional ranges is contained in the
product of the local tensor ranges when the regions cover every site whose
tensor is not already surjective. -/
theorem iInf_liftedCutSpace_le_range_product [∀ v, Finite (Phys v)]
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    {ι : Type*} (R : ι → Finset Vertex) (C : ι → Finset Edge)
    (hcover : ∀ v, (∃ i, v ∈ R i) ∨ LinearMap.range (localSiteMap tail head D A v) = ⊤) :
    (⨅ i, liftedCutSpace tail head D A (R i) (C i)) ≤
      LinearMap.range (dependentPhysicalProductFamilyMap
        (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) := by
  classical
  intro ψ hψ
  apply (mem_range_dependentPhysicalProductFamilyMap_iff _ ψ).mpr
  intro v σ
  change (fun s ↦ ψ (Function.update σ v s)) ∈
    LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' (localSiteMap tail head D A v)))
  rw [Matrix.toLin'_toMatrix']
  rcases hcover v with ⟨i, hv⟩ | hv
  · exact slice_mem_range_of_mem_liftedCutSpace tail head D A (R i) (C i)
      ((Submodule.mem_iInf _).mp hψ i) hv σ
  · rw [hv]
    trivial

/-- At an outside vertex every incident label can be read from the cut
boundary, provided that every outside incidence belongs to a cut edge. -/
def outsideCutLocalConfig (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (η : CutConfig C D) (v : {v // v ∉ R}) : LocalConfig tail head D v.1 :=
  fun p ↦ η (⟨p.1.1, hcut p.1 (by simpa only [p.2] using v.2)⟩, p.1.2)

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
    [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)] in
/-- Extracting an outside local configuration from a restricted endpoint
configuration recovers its original local labels. -/
@[simp] theorem outsideCutLocalConfig_restriction (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C)
    (β : EndpointConfig D) (v : {v // v ∉ R}) :
    outsideCutLocalConfig tail head D R C hcut (cutRestriction D C β) v =
      endpointSiteEquiv tail head D β v.1 := rfl

omit [DecidableEq Vertex] in
/-- Contracting the outside site tensors into the joint boundary expresses
each full cut vector as a lifted regional vector. -/
theorem cutSpace_le_liftedCutSpace
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (R : Finset Vertex) (C : Finset Edge)
    (hcut : ∀ p : Endpoint Edge, endpointVertex tail head p ∉ R → p.1 ∈ C) :
    cutSpace tail head D A C ≤ liftedCutSpace tail head D A R C := by
  classical
  rintro _ ⟨M, rfl⟩
  refine ⟨fun η ↦ M η.1 * ∏ v : {v // v ∉ R},
    A v.1 (outsideCutLocalConfig tail head D R C hcut η.1 v) (η.2 v), ?_⟩
  funext σ
  simp only [liftedCutMap_apply, liftedCutCoeff, cutMap_apply, cutCoeff,
    outsideCutLocalConfig_restriction, outsidePhysicalRestriction]
  apply Finset.sum_congr rfl
  intro β _
  have hprod := Fintype.prod_subtype_mul_prod_subtype (fun v ↦ v ∈ R)
    (fun v ↦ A v (endpointSiteEquiv tail head D β v) (σ v))
  rw [← Finset.prod_subtype R (fun _ ↦ Iff.rfl)
    (fun v ↦ A v (endpointSiteEquiv tail head D β v) (σ v))] at hprod
  rw [← hprod]
  ring

/-- All full cut vectors lie in the product of the actual local site ranges. -/
theorem cutSpace_le_range_product
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ) (C : Finset Edge) :
    cutSpace tail head D A C ≤
      LinearMap.range (dependentPhysicalProductFamilyMap
        (fun v ↦ LinearMap.toMatrix' (localSiteMap tail head D A v))) := by
  classical
  rintro _ ⟨M, rfl⟩
  refine ⟨fun η ↦ M (cutRestriction D C ((endpointSiteEquiv tail head D).symm η)) *
    cutInteriorWeight D C ((endpointSiteEquiv tail head D).symm η), ?_⟩
  funext σ
  simp only [dependentPhysicalProductFamilyMap_apply, cutMap_apply, cutCoeff]
  rw [← (endpointSiteEquiv tail head D).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  simp only [LinearMap.toMatrix'_apply, localSiteMap_apply, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Equiv.apply_symm_apply]
  ring

end TNLean.PEPS.DependentBondNetwork
