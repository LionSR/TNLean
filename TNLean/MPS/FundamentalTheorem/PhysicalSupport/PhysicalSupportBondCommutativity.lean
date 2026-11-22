/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.PhysicalSupport.IsometricAdjacentBondTransport

/-!
# Commuting bonds on an isometric physical support

The positive commuting bond on an injective physical support is included into
the ambient physical space.  Its neighboring translates commute on every
periodic chain of length at least two.  The two-site crossed chain is treated
separately; every longer chain reduces by locality to the three-site
calculation.

No zero-length or one-site nearest-neighbor chain occurs.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

open scoped Matrix BigOperators ComplexOrder
open ManyBody

namespace MPOTensor.PhysicalSupportRestrictionData

variable {d D : ℕ} {P : Matrix (Fin d) (Fin d) ℂ} {K : MPOTensor d D}

open MPOTensor.PhysicalSectorFactorization

/-- The two lifted neighboring bonds commute on a three-site chain.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_three_zero_one_comm
    (F : PhysicalSupportRestrictionData P K)
    (data : TranslationInvariantBondData F.supportDim) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3))
          (F.liftedBond data.bond) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3))
          (F.liftedBond data.bond) := by
  let A := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 3) (0 : Fin 3)) data.bond
  let B := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) data.bond
  have hcomm : A * B = B * A := data.bond_comm (by decide) 0 1
  have hA : A.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hB : B.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hrestricted : (A * B).IsHermitian :=
    (hA.commute_iff hB).mp hcomm
  have hambient :
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 3 ↦ F.inclusion) (A * B)).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose
      (Matrix.piKronecker fun _ : Fin 3 ↦ F.inclusion) hrestricted
  rw [singleKrausMap_adjacentBondProduct
    F.inclusion F.inclusion_isometry data.bond data.bond] at hambient
  refine Commute.eq ((Matrix.IsHermitian.commute_iff ?_ ?_).mpr ?_)
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact hambient

/-- The two oppositely oriented lifted bonds commute on the two-site periodic
chain.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_two_zero_one_comm
    (F : PhysicalSupportRestrictionData P K)
    (data : TranslationInvariantBondData F.supportDim) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (0 : Fin 2))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (1 : Fin 2))
          (F.liftedBond data.bond) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (1 : Fin 2))
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 2) (0 : Fin 2))
          (F.liftedBond data.bond) := by
  let A := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 2) (0 : Fin 2)) data.bond
  let B := placeAlong (X := fun _ ↦ Fin F.supportDim)
    (ringWindow (by decide : 2 ≤ 2) (1 : Fin 2)) data.bond
  have hcomm : A * B = B * A := data.bond_comm (by decide) 0 1
  have hA : A.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hB : B.IsHermitian :=
    (posSemidef_placeAlong _ data.bond_pos).1
  have hrestricted : (A * B).IsHermitian :=
    (hA.commute_iff hB).mp hcomm
  have hambient :
      (singleKrausMap (Matrix.piKronecker fun _ : Fin 2 ↦ F.inclusion) (A * B)).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose
      (Matrix.piKronecker fun _ : Fin 2 ↦ F.inclusion) hrestricted
  rw [singleKrausMap_crossedTwoSiteBondProduct
    F.inclusion F.inclusion_isometry data.bond data.bond] at hambient
  refine Commute.eq ((Matrix.IsHermitian.commute_iff ?_ ?_).mpr ?_)
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact (posSemidef_placeAlong _
      (F.liftedBond_pos data.bond_pos)).1
  · exact hambient

/-- The lifted bond commutes with its translate by one site on every periodic
chain of length at least two.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem liftedBond_zero_one_comm
    (F : PhysicalSupportRestrictionData P K)
    (data : TranslationInvariantBondData F.supportDim)
    {N : ℕ} (hN : 2 ≤ N) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩)
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩)
          (F.liftedBond data.bond) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩)
          (F.liftedBond data.bond) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩)
          (F.liftedBond data.bond) := by
  by_cases htwo : N = 2
  · subst N
    exact F.liftedBond_two_zero_one_comm data
  · have hthree : 3 ≤ N := by omega
    let B := F.liftedBond data.bond
    have hzero := placeAlong_ringWindow_two_zero_nested (d := d)
      hthree ⟨0, by omega⟩ B
    have hone := placeAlong_ringWindow_two_one_nested (d := d)
      hthree ⟨0, by omega⟩ B
    have hsite : finRotate N ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
      apply Fin.ext
      rw [coe_finRotate_mod]
      change 1 % N = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsite] at hone
    have hone' :
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hthree ⟨0, by omega⟩)
            (placeAlong (X := fun _ ↦ Fin d) (ringWindow (by decide : 2 ≤ 3) (1 : Fin 3)) B) =
          placeAlong (X := fun _ ↦ Fin d) (ringWindow (by omega : 2 ≤ N) ⟨1, by omega⟩)
            B := by
      exact hone
    rw [← hzero, ← hone']
    rw [← placeAlong_mul, ← placeAlong_mul]
    exact congrArg
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow hthree ⟨0, by omega⟩))
      (F.liftedBond_three_zero_one_comm data)

private theorem supportProjection_isOrthogonal
    (F : PhysicalSupportRestrictionData P K) : IsOrthogonalProjection P := by
  rw [← F.inclusion_range]
  constructor
  · exact Matrix.isHermitian_mul_conjTranspose_self F.inclusion
  · calc
      (F.inclusion * F.inclusionᴴ) *
          (F.inclusion * F.inclusionᴴ) =
        F.inclusion * (F.inclusionᴴ * F.inclusion) * F.inclusionᴴ := by
          simp only [Matrix.mul_assoc]
      _ = F.inclusion * F.inclusionᴴ := by
        rw [F.inclusion_isometry, Matrix.mul_one]

/-- A translation-invariant commuting bond on the restricted physical space
has a positive translation-invariant commuting lift to the ambient physical
space.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
noncomputable def liftedTranslationInvariantBondData
    (F : PhysicalSupportRestrictionData P K)
    (data : TranslationInvariantBondData F.supportDim) :
    TranslationInvariantBondData d where
  bond := F.liftedBond data.bond
  bond_pos := F.liftedBond_pos data.bond_pos
  bond_comm := by
    intro N hN i j
    let G : GSNNCHData d N := {
      hN := hN
      sectorCount := 1
      multiplicity := fun _ ↦ 1
      sectorProjection := fun _ ↦ P
      sectorProjection_isOrthogonal := fun _ ↦ F.supportProjection_isOrthogonal
      sectorProjection_orthogonal := by
        intro x y hxy
        exact (hxy (Subsingleton.elim x y)).elim
      bond := fun _ ↦ F.liftedBond data.bond
      bond_pos := fun _ ↦ F.liftedBond_pos data.bond_pos
      bond_supported := fun _ ↦ F.liftedBond_supported data.bond
      neighboring_comm := fun _ ↦ F.liftedBond_zero_one_comm data hN }
    simpa [G, GSNNCHData.bondAt] using G.bondAt_comm (0 : Fin 1) i j


end MPOTensor.PhysicalSupportRestrictionData
