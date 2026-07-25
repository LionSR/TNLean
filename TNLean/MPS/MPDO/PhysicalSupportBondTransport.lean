/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.GSNNCHOrthogonalSectors
import TNLean.MPS.MPDO.PhysicalSupportSALTransport

/-!
# Two-site bonds on a physical support

The positive commuting bond obtained from Proposition C.8 after restricting an
MPO tensor to an orthogonal one-site support is carried back to the ambient
physical space by the tensor square of the support inclusion.  The resulting
bond is positive and acts entirely within the prescribed two-site sector.

All chain statements used in this construction concern positive lengths.
In particular, saturation of the area law itself excludes zero physical and
virtual dimensions.  No empty periodic chain is introduced.

The support transport is purely algebraic.  The final existence theorem uses
the already formalized Proposition C.8 and hence inherits its sanctioned
dependence on `hayashi_ssa_equality_characterization_forward`; it introduces
no further axiom.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d e D : ℕ}

/-- Saturation of the area law excludes a zero-dimensional virtual space.
Only the one-site chain is used.

Source: arXiv:1606.00608, Definition 4.6, line 811. -/
theorem bondDim_pos_of_isSAL (M : MPOTensor d D) (hSAL : IsSAL M) :
    0 < D := by
  by_contra hD
  have hD0 : D = 0 := Nat.eq_zero_of_not_pos hD
  subst D
  obtain ⟨_, htrace, _⟩ := hSAL
  have hzero : mpo M 1 = 0 := by
    ext s t
    simp [mpo, mpoMatrixEntry, evalWord]
  exact htrace 1 (by omega) (by rw [hzero, Matrix.trace_zero])

/-- On two sites, the sitewise matrix of a one-site operator is its Kronecker
square in configuration coordinates. -/
theorem sitewisePhysicalMatrix_two_eq_twoSiteSectorProjection
    (P : Matrix (Fin d) (Fin d) ℂ) :
    sitewisePhysicalMatrix P 2 = twoSiteSectorProjection P := by
  ext s t
  simp [sitewisePhysicalMatrix, twoSiteSectorProjection,
    finTwoArrowEquiv, Matrix.reindex_apply]

/-- The sitewise tensor square of an isometry has the corresponding tensor
square of its range projection as its range projection. -/
theorem sitewisePhysicalMatrix_two_mul_conjTranspose
    (V : Matrix (Fin d) (Fin e) ℂ) :
    sitewisePhysicalMatrix V 2 * (sitewisePhysicalMatrix V 2)ᴴ =
      twoSiteSectorProjection (V * Vᴴ) := by
  rw [sitewisePhysicalMatrix_mul_conjTranspose,
    sitewisePhysicalMatrix_two_eq_twoSiteSectorProjection]

namespace PhysicalSupportRestrictionData

variable {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

/-- A two-site bond on the restricted physical space, included into the
ambient physical space. -/
noncomputable def liftedBond (F : PhysicalSupportRestrictionData P K)
    (B : Matrix (Fin 2 → Fin F.supportDim)
      (Fin 2 → Fin F.supportDim) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  singleKrausMap (sitewisePhysicalMatrix F.inclusion 2) B

/-- Positivity of a restricted two-site bond is preserved by its inclusion
into the ambient physical space. -/
theorem liftedBond_pos (F : PhysicalSupportRestrictionData P K)
    {B : Matrix (Fin 2 → Fin F.supportDim)
      (Fin 2 → Fin F.supportDim) ℂ} (hB : B.PosSemidef) :
    (F.liftedBond B).PosSemidef :=
  hB.mul_mul_conjTranspose_same (sitewisePhysicalMatrix F.inclusion 2)

/-- The tensor square of the support inclusion has the prescribed two-site
sector as its range. -/
theorem twoSiteSectorProjection_eq_lifted_range
    (F : PhysicalSupportRestrictionData P K) :
    twoSiteSectorProjection P =
      sitewisePhysicalMatrix F.inclusion 2 *
        (sitewisePhysicalMatrix F.inclusion 2)ᴴ := by
  rw [sitewisePhysicalMatrix_two_mul_conjTranspose, F.inclusion_range]

/-- A lifted bond acts entirely within the tensor square of the prescribed
one-site support.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_supported (F : PhysicalSupportRestrictionData P K)
    (B : Matrix (Fin 2 → Fin F.supportDim)
      (Fin 2 → Fin F.supportDim) ℂ) :
    twoSiteSectorProjection P * F.liftedBond B *
      twoSiteSectorProjection P = F.liftedBond B := by
  rw [F.twoSiteSectorProjection_eq_lifted_range]
  simp only [liftedBond, singleKrausMap_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
      (sitewisePhysicalMatrix F.inclusion 2)ᴴ
      (sitewisePhysicalMatrix F.inclusion 2),
    sitewisePhysicalMatrix_isometry F.inclusion F.inclusion_isometry 2,
    Matrix.one_mul]
  rw [← Matrix.mul_assoc
      (sitewisePhysicalMatrix F.inclusion 2)ᴴ
      (sitewisePhysicalMatrix F.inclusion 2),
    sitewisePhysicalMatrix_isometry F.inclusion F.inclusion_isometry 2,
    Matrix.one_mul]

end PhysicalSupportRestrictionData

end MPOTensor
