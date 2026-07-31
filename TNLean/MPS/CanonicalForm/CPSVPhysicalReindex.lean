/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.Core.PhysicalReindexTransport

/-!
# Literal CPSV canonical form under physical relabeling

A bijective relabeling of the physical alphabet leaves the transfer map unchanged.  It therefore
preserves normal tensors and the retained-block reconstruction of literal CPSV canonical form.

## Main results

* `MPSTensor.IsNormalTensor.reindexPhysical`: physical relabeling preserves normal tensors.
* `MPSTensor.CPSVCanonicalFormData.reindexPhysical`: relabel literal canonical-form data.
* `MPSTensor.IsCPSVCanonicalForm.reindexPhysical`: physical relabeling preserves literal
  canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Section 2.3.
-/

open scoped Matrix

namespace MPSTensor

variable {d₁ d₂ D : ℕ}

namespace IsNormalTensor

/-- A bijective relabeling of the physical alphabet preserves a normal tensor.

The transfer map is unchanged, so its spectral radius and peripheral spectrum are unchanged.  The
invariant-projection condition is likewise invariant under the relabeling.

Source: arXiv:1606.00608, normal-tensor definition at lines 233--235. -/
theorem reindexPhysical {A : MPSTensor d₂ D} (hA : IsNormalTensor A)
    (e : Fin d₁ ≃ Fin d₂) :
    IsNormalTensor (MPSTensor.reindexPhysical e A) := by
  refine ⟨(isIrreducibleTensor_reindexPhysical_equiv e A).2 hA.no_invariant_proj, ?_, ?_⟩
  · rw [transferMap_reindexPhysical_equiv e A]
    exact hA.spectral_radius_one
  · exact (isPrimitive_transferMap_reindexPhysical_equiv e A).2 hA.primitive_transfer

end IsNormalTensor

namespace CPSVCanonicalFormData

/-- Relabel the physical alphabet in literal CPSV canonical-form data.

The retained dimensions, weights, and ambient coisometry are unchanged; only each retained normal
block is relabeled.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--245. -/
noncomputable def reindexPhysical {A : MPSTensor d₂ D}
    (data : CPSVCanonicalFormData A) (e : Fin d₁ ≃ Fin d₂) :
    CPSVCanonicalFormData (MPSTensor.reindexPhysical e A) where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := data.weights
  blocks := fun k ↦ MPSTensor.reindexPhysical e (data.blocks k)
  blocks_normal := fun k ↦ (data.blocks_normal k).reindexPhysical e
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := by
    intro i
    simpa [MPSTensor.reindexPhysical, toTensorFromBlocks] using data.reconstruct (e i)

end CPSVCanonicalFormData

namespace IsCPSVCanonicalForm

/-- A bijective relabeling of the physical alphabet preserves literal CPSV canonical form.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--245. -/
theorem reindexPhysical {A : MPSTensor d₂ D} (hA : IsCPSVCanonicalForm A)
    (e : Fin d₁ ≃ Fin d₂) :
    IsCPSVCanonicalForm (MPSTensor.reindexPhysical e A) := by
  obtain ⟨data⟩ := hA
  exact ⟨data.reindexPhysical e⟩

end IsCPSVCanonicalForm

end MPSTensor
