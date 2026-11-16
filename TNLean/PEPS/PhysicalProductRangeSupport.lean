/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondProductIsometry
import TNLean.Lattice.Compression.DependentPhysicalProductRangeSupport

/-!
# Product ranges from one-coordinate support

A coefficient vector lies in the range of a product of physical maps exactly
when each one-coordinate slice lies in the range of the corresponding local
map. Neither injectivity nor surjectivity is required. In particular, the
statement includes empty site sets and empty input and output alphabets.

The reverse implication uses a linear section on the local range, extended to
the full output space, and applies its associated retraction at every site.
This supplies the product-support step for the supported bond transformations
in SCP10, arXiv:1001.3807, Section 7, lines 2992–3019.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {Site In Out : Type*} [Fintype Site] [DecidableEq Site]

/-- If a local matrix fixes every one-coordinate slice, its full product fixes
the coefficient vector. The matrix need not be a projection. -/
theorem physicalProductMap_fixed_of_slices_fixed [Fintype Out]
    (P : Matrix Out Out ℂ) (ψ : (Site → Out) → ℂ)
    (hψ : ∀ v τ, P *ᵥ (fun s => ψ (Function.update τ v s)) =
      fun s => ψ (Function.update τ v s)) :
    physicalProductMap Site P ψ = ψ := by
  exact TNLean.Lattice.dependentPhysicalProductFamilyMap_fixed_of_slices_fixed
    (fun _ : Site ↦ P) ψ hψ

/-- Every one-coordinate slice of a physical product image lies in the local
physical range, with all other output coordinates left arbitrary. -/
theorem physicalProductMap_slice_mem_range [Fintype In]
    (F : Matrix Out In ℂ) (ψ : (Site → In) → ℂ) (v : Site) (τ : Site → Out) :
    (fun s => physicalProductMap Site F ψ (Function.update τ v s)) ∈
      LinearMap.range (Matrix.mulVecLin F) := by
  exact TNLean.Lattice.dependentPhysicalProductFamilyMap_slice_mem_range
    (fun _ : Site ↦ F) ψ v τ

/-- A vector is in the full product range precisely when every one-coordinate
slice is in the local range. No rank or nonemptiness assumption is needed.
Source: the product support underlying SCP10, Section 7, lines 2992–3019. -/
theorem mem_range_physicalProductMap_iff [Fintype In] [Finite Out]
    (F : Matrix Out In ℂ) (ψ : (Site → Out) → ℂ) :
    ψ ∈ LinearMap.range (physicalProductMap Site F) ↔
      ∀ v τ, (fun s => ψ (Function.update τ v s)) ∈
        LinearMap.range (Matrix.mulVecLin F) := by
  exact TNLean.Lattice.mem_range_dependentPhysicalProductFamilyMap_iff
    (fun _ : Site ↦ F) ψ

end TNLean.PEPS
