/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXSourceFactors
import TNLean.MPS.MPDO.CZXGaussCircuitTuple
import TNLean.MPS.MPU.StaircaseGates

/-!
# Displayed CZX movement coordinates

The contractions of the displayed factors (arXiv:2502.20257, lines 4559–4659)
are the movement circuit and its adjoint in lines 4860–4888, with the leg
ordering of `eq:wLR` (lines 811–869). We use the sparse formula for the existing
circuit, rather than expanding its six matrix factors.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPOTensor.CZX

private theorem movement_entry (i r a j : Fin 4) :
    matterMatrix w ![i, r] ![a, j] =
      if i = a.rev ∧ r = j then (-1 : ℂ) ^ (eExponent (localBits ![a, j])).val else 0 := by
  have h : ∀ i r a j : Fin 4,
      localBits ![i, r] = barFlip (localBits ![a, j]) ↔ i = a.rev ∧ r = j := by decide
  simp only [w_eq, matterMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Matrix.monomial_apply, h]

/-- The displayed right movement contraction is the CZX circuit in physical
coordinates. Source: arXiv:2502.20257, lines 811–869, 4559–4659, 4860–4888. -/
theorem displayedSourceFactors_sourceWR_coordinates (i r a j : Fin 4) :
    SourceFactors.sourceWR tensor displayedSourceFactors
      (i, displayedRightEquiv.symm r) (displayedRightEquiv.symm a, j) =
        matterMatrix w ![i, r] ![a, j] := by
  simp only [SourceFactors.sourceWR, displayedSourceFactors, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, Equiv.refl_apply, movement_entry]
  -- Discard the zero entries of the empty factor before splitting the other two indices.
  fin_cases i <;> fin_cases a <;>
    norm_num [displayedX₁, displayedY₂, Fin.sum_univ_two, Fin.rev, Fin.reduceEq] <;>
    fin_cases r <;> fin_cases j <;>
    norm_num +decide [displayedX₁, displayedY₁, displayedX₂, displayedY₂,
      Fin.sum_univ_two, daggerGauge, SpinCover.pauli_one, Fin.divNat, Fin.modNat,
      Fin.rev, Fin.reduceEq, localBits, siteBits, eExponent, ZMod.val]

/-- The displayed left movement contraction is the adjoint of the same CZX
circuit. Source: arXiv:2502.20257, lines 811–869, 4559–4659, 4860–4888. -/
theorem displayedSourceFactors_sourceWL_coordinates (l i j k : Fin 4) :
    SourceFactors.sourceWL tensor displayedSourceFactors
      (displayedLeftEquiv.symm l, i) (j, displayedLeftEquiv.symm k) =
        (matterMatrix w)ᴴ ![l, i] ![j, k] := by
  simp only [SourceFactors.sourceWL, displayedSourceFactors, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, Equiv.refl_apply, Matrix.conjTranspose_apply,
    movement_entry]
  -- Discard the zero entries of the filled factor before splitting the other two indices.
  fin_cases l <;> fin_cases j <;>
    norm_num [displayedY₂, Fin.sum_univ_two, Fin.rev, Fin.reduceEq] <;>
    fin_cases i <;> fin_cases k <;>
    norm_num +decide [displayedX₂, displayedY₂, Fin.sum_univ_two,
      Fin.divNat, Fin.modNat, Fin.rev, Fin.reduceEq,
      localBits, siteBits, eExponent, ZMod.val]

end MPOTensor.CZX
