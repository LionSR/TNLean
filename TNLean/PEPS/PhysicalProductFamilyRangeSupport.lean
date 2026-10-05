/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PhysicalProductRangeSupport
import TNLean.PEPS.DependentPhysicalProductRangeSupport

/-!
# Ranges of site-dependent products of physical maps

A coefficient vector is in the range of a site-dependent product of physical
maps if and only if each one-coordinate slice belongs to the range of the map
at that site. The input and output alphabets may be empty, as may the set of
sites. No injectivity, surjectivity, or common rank is assumed.

The local retractions are chosen independently, so this applies to different
horizontal and vertical bond maps at every torus vertex. The support results
are specializations of the dependent-alphabet product theorems.

Source: the product-support argument underlying SCP10, arXiv:1001.3807,
Section 7, lines 2992–3019.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {Site In Out : Type*} [Fintype Site] [DecidableEq Site]

/-- The product matrix of a family of physical maps, one at each site. -/
def physicalProductFamilyMatrix (F : Site → Matrix Out In ℂ) :
    Matrix (Site → Out) (Site → In) ℂ :=
  fun τ σ => ∏ v, F v (τ v) (σ v)

/-- Apply a possibly different physical map at every site. -/
def physicalProductFamilyMap [Fintype In] (F : Site → Matrix Out In ℂ) :
    ((Site → In) → ℂ) →ₗ[ℂ] ((Site → Out) → ℂ) :=
  Matrix.mulVecLin (physicalProductFamilyMatrix F)

omit [DecidableEq Site] in
/-- A constant family gives the usual physical product matrix. -/
@[simp] theorem physicalProductFamilyMatrix_const (F : Matrix Out In ℂ) :
    physicalProductFamilyMatrix (fun _ : Site => F) = physicalProductMatrix Site F := rfl

/-- A constant family gives the usual physical product map. -/
@[simp] theorem physicalProductFamilyMap_const [Fintype In] (F : Matrix Out In ℂ) :
    physicalProductFamilyMap (fun _ : Site => F) = physicalProductMap Site F := rfl

/-- The coefficient formula for a site-dependent physical product. -/
theorem physicalProductFamilyMap_apply [Fintype In] (F : Site → Matrix Out In ℂ)
    (ψ : (Site → In) → ℂ) (τ : Site → Out) :
    physicalProductFamilyMap F ψ τ =
      ∑ σ : Site → In, (∏ v, F v (τ v) (σ v)) * ψ σ := rfl

/-- Products of physical matrices compose separately at each site. -/
theorem physicalProductFamilyMatrix_mul {Mid : Type*} [Fintype Mid]
    (F : Site → Matrix Out Mid ℂ) (L : Site → Matrix Mid In ℂ) :
    physicalProductFamilyMatrix F * physicalProductFamilyMatrix L =
      physicalProductFamilyMatrix (fun v => F v * L v) := by
  exact dependentPhysicalProductFamilyMatrix_mul F L

/-- Products of physical maps compose separately at each site. -/
theorem physicalProductFamilyMap_comp {Mid : Type*} [Fintype In] [Fintype Mid]
    (F : Site → Matrix Out Mid ℂ) (L : Site → Matrix Mid In ℂ) :
    physicalProductFamilyMap F ∘ₗ physicalProductFamilyMap L =
      physicalProductFamilyMap (fun v => F v * L v) := by
  exact dependentPhysicalProductFamilyMap_comp F L

omit [DecidableEq Site] in
/-- Identity matrices at every site give the identity product matrix. -/
@[simp] theorem physicalProductFamilyMatrix_one [DecidableEq Out] :
    physicalProductFamilyMatrix (fun _ : Site => (1 : Matrix Out Out ℂ)) = 1 := by
  exact dependentPhysicalProductFamilyMatrix_one (Site := Site) (Out := fun _ ↦ Out)

/-- Identity maps at every site give the identity product map. -/
@[simp] theorem physicalProductFamilyMap_one [Fintype Out] [DecidableEq Out] :
    physicalProductFamilyMap (fun _ : Site => (1 : Matrix Out Out ℂ)) = LinearMap.id := by
  exact dependentPhysicalProductFamilyMap_one (Site := Site) (Out := fun _ ↦ Out)

/-- A product with only one nonidentity coordinate acts on that coordinate's slice. -/
theorem physicalProductFamilyMap_oneCoordinate_apply [Fintype Out] [DecidableEq Out]
    (v : Site) (P : Matrix Out Out ℂ) (ψ : (Site → Out) → ℂ) (τ : Site → Out) :
    physicalProductFamilyMap (fun w => if w = v then P else 1) ψ τ =
      ∑ s : Out, P (τ v) s * ψ (Function.update τ v s) := by
  have hmask : Function.update (fun _ : Site ↦ (1 : Matrix Out Out ℂ)) v P =
      fun w ↦ if w = v then P else 1 := by
    funext w
    simp [Function.update_apply]
  have h := dependentPhysicalProductFamilyMap_oneCoordinate_apply (Out := fun _ ↦ Out) v P ψ τ
  rw [hmask] at h
  exact h

/-- If each local matrix fixes every slice at its own site, the full product
fixes the coefficient vector. The local matrices need not be projections. -/
theorem physicalProductFamilyMap_fixed_of_slices_fixed [Fintype Out]
    (P : Site → Matrix Out Out ℂ) (ψ : (Site → Out) → ℂ)
    (hψ : ∀ v τ, P v *ᵥ (fun s => ψ (Function.update τ v s)) =
      fun s => ψ (Function.update τ v s)) :
    physicalProductFamilyMap P ψ = ψ := by
  exact dependentPhysicalProductFamilyMap_fixed_of_slices_fixed P ψ hψ

/-- Every one-coordinate slice of a physical product image lies in the local
physical range, with all other output coordinates left arbitrary. -/
theorem physicalProductFamilyMap_slice_mem_range [Fintype In]
    (F : Site → Matrix Out In ℂ) (ψ : (Site → In) → ℂ) (v : Site) (τ : Site → Out) :
    (fun s => physicalProductFamilyMap F ψ (Function.update τ v s)) ∈
      LinearMap.range (Matrix.mulVecLin (F v)) := by
  exact dependentPhysicalProductFamilyMap_slice_mem_range F ψ v τ

/-- A vector lies in the product range exactly when every one-coordinate
slice is in the range of the map at that site. This allows site-dependent
matrices of different ranks, including zero matrices and empty alphabets.
Source: the product support underlying SCP10, Section 7, lines 2992–3019. -/
theorem mem_range_physicalProductFamilyMap_iff [Fintype In] [Finite Out]
    (F : Site → Matrix Out In ℂ) (ψ : (Site → Out) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductFamilyMap F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin (F v)) := by
  exact mem_range_dependentPhysicalProductFamilyMap_iff F ψ

end TNLean.PEPS
