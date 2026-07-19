/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.DiagonalCutRank
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Diagonal finite-chain matrix product operators

This file associates a real coefficient matrix and a joint probability
distribution to a positive diagonal finite-chain matrix product operator.
The resulting classical mutual information is at most twice the logarithm of
the bond dimension.

Only positivity and diagonality at the chain length under consideration are
assumed.  No local purification or positivity at other lengths is required.

## Main definitions

* `MPOTensor.IsDiagonalAt`: diagonality of the operator at one chain length.
* `MPOTensor.diagonalCutRealMatrix`: the real diagonal coefficients across a cut.
* `MPOTensor.diagonalCutMass`: the total mass of these coefficients.
* `MPOTensor.normalizedDiagonalCutDistribution`: their normalization.

## Main statements

* `MPOTensor.normalizedDiagonalCutDistribution_isJointDistribution`: positivity
  and positive total mass give a joint probability distribution.
* `MPOTensor.diagonalFiniteChain_classicalMutualInformation_le_two_log`: the
  classical mutual information of a positive diagonal finite-chain operator is
  at most $2\log D$.

## References

* arXiv:1606.00608, Proposition 4.5, lines 795--806.
* `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`, section
  "Diagonal matrix product operators".
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- An MPO tensor is diagonal at length `N` when the generated finite-chain
operator has no off-diagonal matrix entries.

This is the diagonal finite-chain specialization considered in the analysis of
arXiv:1606.00608, Proposition 4.5, lines 795--806; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
def IsDiagonalAt (M : MPOTensor d D) (N : ℕ) : Prop :=
  (mpo M N).IsDiag

/-- The real parts of the diagonal coefficients across a periodic cut.

For a positive finite-chain operator these coefficients are real and
nonnegative.  They are the coefficients denoted by $P_{x,y}$ in the diagonal
analysis of arXiv:1606.00608, Proposition 4.5, lines 795--806. -/
noncomputable def diagonalCutRealMatrix (M : MPOTensor d D) (L R : ℕ) :
    Matrix (Fin L → Fin d) (Fin R → Fin d) ℝ :=
  (diagonalCutMatrix M L R).map Complex.re

/-- The total mass of the real diagonal coefficients across a periodic cut.

This is the normalization constant $Z$ in the diagonal analysis of
arXiv:1606.00608, Proposition 4.5, lines 795--806. -/
noncomputable def diagonalCutMass (M : MPOTensor d D) (L R : ℕ) : ℝ :=
  ∑ x, ∑ y, diagonalCutRealMatrix M L R x y

/-- The real diagonal coefficient matrix divided by its total mass.

This is the joint distribution $\widehat P=Z^{-1}P$ in the diagonal analysis of
arXiv:1606.00608, Proposition 4.5, lines 795--806. -/
noncomputable def normalizedDiagonalCutDistribution (M : MPOTensor d D) (L R : ℕ) :
    Matrix (Fin L → Fin d) (Fin R → Fin d) ℝ :=
  (diagonalCutMass M L R)⁻¹ • diagonalCutRealMatrix M L R

/-- A diagonal cut coefficient is the corresponding diagonal matrix entry of
the finite-chain MPO operator.

This is the coefficient identity used in the diagonal finite-chain analysis of
arXiv:1606.00608, Proposition 4.5, lines 795--806; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutMatrix_apply_eq_mpo (M : MPOTensor d D) (L R : ℕ)
    (x : Fin L → Fin d) (y : Fin R → Fin d) :
    diagonalCutMatrix M L R x y =
      mpo M (L + R) (Fin.append x y) (Fin.append x y) := by
  simp [diagonalCutMatrix, mpo_apply, mpoMatrixEntry, List.ofFn_fin_append]

/-- Positivity makes every diagonal cut coefficient equal to the scalar
extension of its real part.

This is the real-coefficient step in the diagonal finite-chain analysis of
arXiv:1606.00608, Proposition 4.5, lines 795--806; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutRealMatrix_map_ofReal_of_posSemidef (M : MPOTensor d D) (L R : ℕ)
    (hpos : (mpo M (L + R)).PosSemidef) :
    (diagonalCutRealMatrix M L R).map Complex.ofReal = diagonalCutMatrix M L R := by
  ext x y
  rw [Matrix.map_apply, diagonalCutRealMatrix, Matrix.map_apply,
    diagonalCutMatrix_apply_eq_mpo]
  exact hpos.isHermitian.coe_re_apply_self _

/-- The real diagonal cut coefficients of a positive finite-chain operator are
nonnegative.

This is the positivity step in the diagonal finite-chain analysis of
arXiv:1606.00608, Proposition 4.5, lines 795--806; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutRealMatrix_nonneg_of_posSemidef (M : MPOTensor d D) (L R : ℕ)
    (hpos : (mpo M (L + R)).PosSemidef) (x : Fin L → Fin d) (y : Fin R → Fin d) :
    0 ≤ diagonalCutRealMatrix M L R x y := by
  rw [diagonalCutRealMatrix, Matrix.map_apply, diagonalCutMatrix_apply_eq_mpo]
  exact (RCLike.nonneg_iff.mp hpos.diag_nonneg).1

/-- Positive semidefiniteness and positive total mass make the normalized
diagonal cut coefficients a joint probability distribution.

This is the normalization step in the diagonal case of arXiv:1606.00608,
Proposition 4.5, lines 795--806. -/
theorem normalizedDiagonalCutDistribution_isJointDistribution (M : MPOTensor d D)
    (L R : ℕ) (hpos : (mpo M (L + R)).PosSemidef)
    (hmass : 0 < diagonalCutMass M L R) :
    (normalizedDiagonalCutDistribution M L R).IsJointDistribution := by
  constructor
  case right =>
    simp only [normalizedDiagonalCutDistribution, Matrix.smul_apply, smul_eq_mul]
    simp_rw [← Finset.mul_sum]
    change (diagonalCutMass M L R)⁻¹ * diagonalCutMass M L R = 1
    exact inv_mul_cancel₀ hmass.ne'
  case left =>
    intro x y
    simp only [normalizedDiagonalCutDistribution, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hmass.le)
      (diagonalCutRealMatrix_nonneg_of_posSemidef M L R hpos x y)

/-- **Classical estimate for a positive diagonal finite-chain MPO.** If the
operator generated on `L + R` sites is diagonal and positive semidefinite, and
its total diagonal mass is positive, then the classical mutual information of
its normalized diagonal coefficients is at most `2 * log D`.

Positivity produces the joint distribution from the diagonal entries, while
diagonality says that these entries constitute the whole finite-chain state.
Thus the normalized coefficients are the classical finite-chain distribution.

This is the diagonal finite-chain consequence of arXiv:1606.00608,
Proposition 4.5, lines 795--806, using Riazanov--Vyalyi, Theorem 4.1
(arXiv:1704.06507).  It does not assert a bound for unrestricted quantum mutual
information.

**Scope restriction (diagonal finite-chain operator):** Proposition 4.5 concerns
arbitrary MPDOs, whereas this theorem treats the classical diagonal subcase at
one chain length.  The distinction and the unrestricted quantum question are
documented in `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalFiniteChain_classicalMutualInformation_le_two_log [NeZero D]
    (M : MPOTensor d D) (L R : ℕ) (_hdiag : M.IsDiagonalAt (L + R))
    (hpos : (mpo M (L + R)).PosSemidef) (hmass : 0 < diagonalCutMass M L R) :
    Entropy.classicalMutualInformation (normalizedDiagonalCutDistribution M L R) ≤
      2 * Real.log D := by
  apply diagonalCut_classicalMutualInformation_le_two_log M L R
      (diagonalCutRealMatrix M L R) (normalizedDiagonalCutDistribution M L R)
      (diagonalCutMass M L R)
  · exact normalizedDiagonalCutDistribution_isJointDistribution M L R hpos hmass
  · exact hmass
  · rfl
  · exact diagonalCutRealMatrix_map_ofReal_of_posSemidef M L R hpos

end MPOTensor
