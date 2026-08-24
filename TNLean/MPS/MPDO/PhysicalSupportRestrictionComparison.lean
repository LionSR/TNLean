/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport
import TNLean.MPS.MPDO.PhysicalSupportRestriction

/-!
# Comparison of physical-support restriction coordinates

Two isometric coordinate realizations of the range of the same physical
projection differ by a matrix that is unitary between their finite coordinate
spaces.  This module records the resulting exact comparison of the restricted
MPO tensors and of neighboring trace factorizations.

These statements are project-derived coordinate facts, not results stated in
arXiv:1606.00608.  Their source context is the range restriction surrounding
equations `PjKiPj` and `generateMPDO` in Appendix C.2, lines 1680--1691 and
1733--1770.
-/

open scoped Matrix

noncomputable section

namespace MPOTensor.PhysicalSupportRestrictionData

variable {d D : ℕ} {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

open PhysicalSectorFactorization

/-- The coordinate matrix from the support coordinates selected by `G` to
those selected by `F`.

This is a project-derived comparison of two range restrictions in the setting
of arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines
1680--1691 and 1733--1770; the paper does not define this matrix. -/
noncomputable def supportCoordinateChange
    (F G : PhysicalSupportRestrictionData P K) :
    Matrix (Fin F.supportDim) (Fin G.supportDim) ℂ :=
  F.inclusionᴴ * G.inclusion

/-- The coordinate change between two isometric realizations of the same
physical support is unitary between their coordinate spaces.

This is project-derived finite-dimensional coordinate algebra in the setting
of arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines
1680--1691 and 1733--1770; it is not a theorem stated in the paper. -/
theorem supportCoordinateChange_isUnitaryBetween
    (F G : PhysicalSupportRestrictionData P K) :
    (F.supportCoordinateChange G).IsUnitaryBetween := by
  constructor
  · change
      (F.inclusionᴴ * G.inclusion)ᴴ *
          (F.inclusionᴴ * G.inclusion) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (G.inclusionᴴ * F.inclusion) *
            (F.inclusionᴴ * G.inclusion) =
          G.inclusionᴴ * (F.inclusion * F.inclusionᴴ) * G.inclusion := by
            simp only [Matrix.mul_assoc]
      _ = G.inclusionᴴ * P * G.inclusion := by rw [F.inclusion_range]
      _ = G.inclusionᴴ * (G.inclusion * G.inclusionᴴ) * G.inclusion := by
        rw [G.inclusion_range]
      _ = (G.inclusionᴴ * G.inclusion) *
          (G.inclusionᴴ * G.inclusion) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by simp only [G.inclusion_isometry, Matrix.one_mul]
  · change
      (F.inclusionᴴ * G.inclusion) *
          (F.inclusionᴴ * G.inclusion)ᴴ = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (F.inclusionᴴ * G.inclusion) *
            (G.inclusionᴴ * F.inclusion) =
          F.inclusionᴴ * (G.inclusion * G.inclusionᴴ) * F.inclusion := by
            simp only [Matrix.mul_assoc]
      _ = F.inclusionᴴ * P * F.inclusion := by rw [G.inclusion_range]
      _ = F.inclusionᴴ * (F.inclusion * F.inclusionᴴ) * F.inclusion := by
        rw [F.inclusion_range]
      _ = (F.inclusionᴴ * F.inclusion) *
          (F.inclusionᴴ * F.inclusion) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by simp only [F.inclusion_isometry, Matrix.one_mul]

/-- Changing from one set of support coordinates to another gives exactly the
restriction defined by the target coordinates.

This is a project-derived coordinate identity used with the support
restriction in arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1680--1691 and 1733--1770; the source does not state it. -/
theorem changePhysicalBasis_supportCoordinateChange
    (F G : PhysicalSupportRestrictionData P K) :
    changePhysicalBasis (F.supportCoordinateChange G)
        (changePhysicalBasis G.inclusionᴴ K) =
      changePhysicalBasis F.inclusionᴴ K := by
  rw [changePhysicalBasis_changePhysicalBasis]
  congr 1
  calc
    (F.inclusionᴴ * G.inclusion) * G.inclusionᴴ =
        F.inclusionᴴ * (G.inclusion * G.inclusionᴴ) := by
          rw [Matrix.mul_assoc]
    _ = F.inclusionᴴ * P := by rw [G.inclusion_range]
    _ = F.inclusionᴴ * (F.inclusion * F.inclusionᴴ) := by
      rw [F.inclusion_range]
    _ = F.inclusionᴴ := by
      rw [← Matrix.mul_assoc, F.inclusion_isometry, Matrix.one_mul]

/-- Existence of neighboring trace data for a restriction is independent of
the chosen isometric coordinates on a fixed physical support.

This equivalence is project-derived.  It compares presentations of the support
restriction used around arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1680--1691 and 1733--1770; it is not stated in that
source. -/
theorem exists_neighboringTraceFactorization_restriction_iff
    (F G : PhysicalSupportRestrictionData P K) :
    (∃ H : PhysicalSectorFactorization
        (changePhysicalBasis F.inclusionᴴ K),
        Nonempty H.NeighboringTraceFactorization) ↔
      ∃ H : PhysicalSectorFactorization
        (changePhysicalBasis G.inclusionᴴ K),
        Nonempty H.NeighboringTraceFactorization := by
  have hTransport :=
    exists_neighboringTraceFactorization_changePhysicalBasis_iff_of_isUnitaryBetween
        (K := changePhysicalBasis G.inclusionᴴ K)
        (F.supportCoordinateChange G)
        (F.supportCoordinateChange_isUnitaryBetween G)
  rw [F.changePhysicalBasis_supportCoordinateChange G] at hTransport
  exact hTransport.symm

end MPOTensor.PhysicalSupportRestrictionData
