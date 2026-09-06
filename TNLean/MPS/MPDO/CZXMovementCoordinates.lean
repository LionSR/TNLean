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

set_option maxHeartbeats 2000000 in
-- The sparse coordinate check has 256 cases, each with a two-term virtual contraction.

/-- The displayed right movement contraction is the CZX circuit in physical
coordinates. Source: arXiv:2502.20257, lines 811–869, 4559–4659, 4860–4888. -/
theorem displayedSourceFactors_sourceWR_coordinates (i r a j : Fin 4) :
    SourceFactors.sourceWR tensor displayedSourceFactors
      (i, displayedRightEquiv.symm r) (displayedRightEquiv.symm a, j) =
        matterMatrix w ![i, r] ![a, j] := by
  simp only [SourceFactors.sourceWR, displayedSourceFactors, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, Equiv.refl_apply, w_eq, matterMatrix, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.monomial_apply]
  fin_cases i <;> fin_cases r <;> fin_cases a <;> fin_cases j <;>
    norm_num +decide [displayedX₁, displayedY₁, displayedX₂, displayedY₂,
      Fin.sum_univ_two, daggerGauge, SpinCover.pauli_one, Fin.divNat, Fin.modNat,
      Fin.rev, Fin.reduceEq, localBits, siteBits, barFlip, eExponent, ZMod.val]

set_option maxHeartbeats 2000000 in
-- The sparse coordinate check has 256 cases, each with a two-term virtual contraction.
/-- The displayed left movement contraction is the adjoint of the same CZX
circuit. Source: arXiv:2502.20257, lines 811–869, 4559–4659, 4860–4888. -/
theorem displayedSourceFactors_sourceWL_coordinates (l i j k : Fin 4) :
    SourceFactors.sourceWL tensor displayedSourceFactors
      (displayedLeftEquiv.symm l, i) (j, displayedLeftEquiv.symm k) =
        (matterMatrix w)ᴴ ![l, i] ![j, k] := by
  simp only [SourceFactors.sourceWL, displayedSourceFactors, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, Equiv.refl_apply, Matrix.conjTranspose_apply,
    w_eq, matterMatrix, Matrix.reindex_apply, Equiv.symm_symm, Matrix.monomial_apply]
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num +decide [displayedX₂, displayedY₂, Fin.sum_univ_two,
      Fin.divNat, Fin.modNat, Fin.rev, Fin.reduceEq,
      localBits, siteBits, barFlip, eExponent, ZMod.val]

end MPOTensor.CZX
