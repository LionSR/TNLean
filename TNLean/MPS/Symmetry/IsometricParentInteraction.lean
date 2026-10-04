/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalEmbedding
import TNLean.MPS.Symmetry.PhysicalInteractionGap

/-!
# Canonical parents as isometric interaction extensions

The canonical parent of a physically embedded tensor is the isometric
extension of its original parent, with energy one on the unused two-site
space. This identifies the canonical endpoint projections with the local
extensions used in the common physical space of arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- Physical interaction extension preserves the order of local
Hermitian interactions. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym, comparison of the embedded parent projections. -/
theorem isometricInteractionExtension_mono {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) {A B : MPOTensor.ChainOperator d 2}
    (hAB : A ≤ B) :
    isometricInteractionExtension E A ≤ isometricInteractionExtension E B := by
  unfold isometricInteractionExtension
  apply sub_le_sub_left
  rw [← sub_nonneg, ← map_sub, sub_sub_sub_cancel_left]
  exact Matrix.nonneg_iff_posSemidef.mpr
    ((singleKrausMap_isKrausCP _).map_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)))

/-- The canonical two-site parent of an isometrically embedded tensor is
the isometric extension of its original parent interaction. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem parentInteraction_matrix_rotatePhysical_eq_isometricInteractionExtension
    {d m D : ℕ} (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    (A : MPSTensor d D) :
    LinearMap.toMatrix' (parentInteraction (rotatePhysical E A) 2) =
      isometricInteractionExtension E (LinearMap.toMatrix' (parentInteraction A 2)) := by
  rw [parentInteraction_matrix_rotatePhysical_isometry E hE A 2]
  simp only [isometricInteractionExtension, map_sub, singleKrausMap_apply, Matrix.mul_one]
  rw [show Matrix.rectKronecker (fun _ : Fin 2 => E) =
    MPOTensor.sitewisePhysicalMatrix E 2 from rfl]
  abel

end MPSTensor
