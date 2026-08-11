/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Canonical form for matrix product unitaries

This file records the canonical form used by arXiv:1703.09188, lines 259--267.
Unlike the stronger CPSV normal-block canonical form, it permits irreducible
periodic blocks. The existing coisometric retained-block reconstruction supplies
the ambient zero-coordinate convention.

## Main definitions

* `MPSTensor.IsMPUCanonicalBlock`: irreducibility and transfer spectral radius one.
* `MPSTensor.MPUCanonicalFormData`: a weighted retained-block reconstruction.
* `MPSTensor.IsMPUCanonicalForm`: existence of such reconstruction data.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A canonical block for an MPU endpoint is irreducible and has transfer
spectral radius one. Peripheral eigenvalues other than one are allowed.

Source: arXiv:1703.09188, lines 259--267. -/
structure IsMPUCanonicalBlock (A : MPSTensor d D) : Prop where
  /-- The block admits no nontrivial invariant orthogonal projection. -/
  irreducible : IsIrreducibleTensor A
  /-- The block transfer map has spectral radius one. -/
  spectral_radius_one :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (transferMap (d := d) (D := D) A)) = 1

/-- Witness data for the MPU canonical form, using irreducible
spectral-radius-one blocks and an exact coisometric retained-block
reconstruction in the ambient bond space.

Source: arXiv:1703.09188, lines 259--267. -/
structure MPUCanonicalFormData (A : MPSTensor d D) where
  /-- Number of retained canonical blocks. -/
  r : ℕ
  /-- Bond dimension of each retained block. -/
  dim : Fin r → ℕ
  /-- Every retained block has positive bond dimension. -/
  dim_pos : ∀ k, 0 < dim k
  /-- Scalar weight of each retained block. -/
  weights : Fin r → ℂ
  /-- Retained canonical blocks. -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- Every retained block is irreducible and has transfer spectral radius one. -/
  blocks_canonical : ∀ k, IsMPUCanonicalBlock (blocks k)
  /-- The retained direct sum fits inside the original bond space. -/
  total_dim_le : ∑ k : Fin r, dim k ≤ D
  /-- Coisometric inclusion of the retained coordinates into the ambient bond space. -/
  ambient_coisometry : Matrix (Fin (∑ k : Fin r, dim k)) (Fin D) ℂ
  /-- The retained coordinates embed coisometrically. -/
  coisometric : ambient_coisometry * ambient_coisometryᴴ = 1
  /-- Exact reconstruction from the weighted retained blocks. -/
  reconstruct : ∀ i,
    A i = ambient_coisometryᴴ * toTensorFromBlocks (d := d) weights blocks i *
      ambient_coisometry

/-- An MPS tensor is in MPU canonical form when it has an exact retained-block
reconstruction whose blocks are irreducible and transfer-normalized.

Source: arXiv:1703.09188, lines 259--267. -/
def IsMPUCanonicalForm (A : MPSTensor d D) : Prop :=
  Nonempty (MPUCanonicalFormData A)

namespace CPSVCanonicalFormData

/-- The stronger CPSV normal-block data gives MPU canonical-form data by
forgetting peripheral-spectrum uniqueness and retaining the reconstruction.

There is intentionally no converse: MPU canonical blocks may be periodic.

Source: arXiv:1703.09188, lines 259--267. -/
def toMPUCanonicalFormData {A : MPSTensor d D} (data : CPSVCanonicalFormData A) :
    MPUCanonicalFormData A where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := data.weights
  blocks := data.blocks
  blocks_canonical := fun k ↦
    ⟨(data.blocks_normal k).no_invariant_proj,
      (data.blocks_normal k).spectral_radius_one⟩
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := data.reconstruct

end CPSVCanonicalFormData

namespace IsCPSVCanonicalForm

/-- The CPSV normal-block canonical form implies the weaker MPU canonical form.
No converse is asserted because the MPU predicate permits periodic blocks.

Source: arXiv:1703.09188, lines 259--267. -/
theorem toIsMPUCanonicalForm {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    IsMPUCanonicalForm A := by
  obtain ⟨data⟩ := hA
  exact ⟨data.toMPUCanonicalFormData⟩

end IsCPSVCanonicalForm

end MPSTensor
