/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.DiagonalCutRank
import TNLean.MPS.MPDO.AreaLaw
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
* `MPOTensor.IsDiagonal`: diagonality at every positive chain length.
* `MPOTensor.diagonalCutRealMatrix`: the real diagonal coefficients across a cut.
* `MPOTensor.diagonalCutMass`: the total mass of these coefficients.
* `MPOTensor.normalizedDiagonalCutDistribution`: their normalization.

## Main statements

* `MPOTensor.normalizedDiagonalCutDistribution_isJointDistribution`: positivity
  and positive total mass give a joint probability distribution.
* `MPOTensor.diagonalFiniteChain_classicalMutualInformation_le_two_log`: the
  classical mutual information of a positive diagonal finite-chain operator is
  at most $2\log D$.
* `MPOTensor.diagonalMPDO_classicalMutualInformation_le_two_log`: the same
  estimate from global diagonality, MPDO positivity, and positive trace.

## References

* arXiv:1606.00608, Proposition 4.5, lines 792--806, and its proof at
  lines 1316--1320.
* Riazanov--Vyalyi, arXiv:1704.06507, Theorem 4.1.
* `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`, section
  "Diagonal matrix product operators".
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- An MPO tensor is diagonal at length `N` when the generated finite-chain
operator has no off-diagonal matrix entries.

This is the fixed-length diagonal restriction used here to study the bound
invoked in the proof of arXiv:1606.00608, Proposition 4.5, lines 1316--1320;
see `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
def IsDiagonalAt (M : MPOTensor d D) (N : ℕ) : Prop :=
  (mpo M N).IsDiag

/-- An MPO tensor is diagonal when it generates a diagonal operator at every
positive chain length.

This is the global diagonal restriction used here to study the bound invoked
in the proof of arXiv:1606.00608, Proposition 4.5, lines 1316--1320; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
def IsDiagonal (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 0 < N → M.IsDiagonalAt N

/-- The real parts of the diagonal coefficients across a periodic cut.

For a positive finite-chain operator these coefficients are real and
nonnegative.  This matrix belongs to the fixed-length diagonal restriction of
the bound invoked in the proof of arXiv:1606.00608, Proposition 4.5, lines
1316--1320; see `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
noncomputable def diagonalCutRealMatrix (M : MPOTensor d D) (L R : ℕ) :
    Matrix (Fin L → Fin d) (Fin R → Fin d) ℝ :=
  (diagonalCutMatrix M L R).map Complex.re

/-- The total mass of the real diagonal coefficients across a periodic cut.

This is the normalization constant for the fixed-length diagonal restriction
of arXiv:1606.00608, Proposition 4.5.  The source normalization convention is
at lines 792--793; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
noncomputable def diagonalCutMass (M : MPOTensor d D) (L R : ℕ) : ℝ :=
  ∑ x, ∑ y, diagonalCutRealMatrix M L R x y

/-- The real diagonal coefficient matrix divided by its total mass.

This is the joint distribution $\widehat P=Z^{-1}P$ for the fixed-length
diagonal restriction of arXiv:1606.00608, Proposition 4.5.  The source
normalization convention is at lines 792--793; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
noncomputable def normalizedDiagonalCutDistribution (M : MPOTensor d D) (L R : ℕ) :
    Matrix (Fin L → Fin d) (Fin R → Fin d) ℝ :=
  (diagonalCutMass M L R)⁻¹ • diagonalCutRealMatrix M L R

/-- A diagonal cut coefficient is the corresponding diagonal matrix entry of
the finite-chain MPO operator.

This is the coefficient identity used for the fixed-length diagonal restriction
of the bound invoked in the proof of arXiv:1606.00608, Proposition 4.5, lines
1316--1320; see `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutMatrix_apply_eq_mpo (M : MPOTensor d D) (L R : ℕ)
    (x : Fin L → Fin d) (y : Fin R → Fin d) :
    diagonalCutMatrix M L R x y =
      mpo M (L + R) (Fin.append x y) (Fin.append x y) := by
  simp [diagonalCutMatrix, mpo_apply, mpoMatrixEntry, List.ofFn_fin_append]

/-- Positivity makes every diagonal cut coefficient equal to the scalar
extension of its real part.

This is the real-coefficient step for the fixed-length diagonal restriction of
the bound invoked in the proof of arXiv:1606.00608, Proposition 4.5, lines
1316--1320; see `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutRealMatrix_map_ofReal_of_posSemidef (M : MPOTensor d D) (L R : ℕ)
    (hpos : (mpo M (L + R)).PosSemidef) :
    (diagonalCutRealMatrix M L R).map Complex.ofReal = diagonalCutMatrix M L R := by
  ext x y
  rw [Matrix.map_apply, diagonalCutRealMatrix, Matrix.map_apply,
    diagonalCutMatrix_apply_eq_mpo]
  exact hpos.isHermitian.coe_re_apply_self _

/-- The real diagonal cut coefficients of a positive finite-chain operator are
nonnegative.

This is the positivity step for the fixed-length diagonal restriction of the
bound invoked in the proof of arXiv:1606.00608, Proposition 4.5, lines
1316--1320; see `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutRealMatrix_nonneg_of_posSemidef (M : MPOTensor d D) (L R : ℕ)
    (hpos : (mpo M (L + R)).PosSemidef) (x : Fin L → Fin d) (y : Fin R → Fin d) :
    0 ≤ diagonalCutRealMatrix M L R x y := by
  rw [diagonalCutRealMatrix, Matrix.map_apply, diagonalCutMatrix_apply_eq_mpo]
  exact (RCLike.nonneg_iff.mp hpos.diag_nonneg).1

/-- The mass of the diagonal cut coefficients is the real part of the
finite-chain trace.

This identifies the local normalization constant with the trace in the
normalization convention of arXiv:1606.00608, lines 792--793; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalCutMass_eq_trace_re (M : MPOTensor d D) (L R : ℕ) :
    diagonalCutMass M L R = (mpo M (L + R)).trace.re := by
  classical
  have hsum :
      (∑ x : Fin L → Fin d, ∑ y : Fin R → Fin d,
        mpo M (L + R) (Fin.append x y) (Fin.append x y)) =
        (mpo M (L + R)).trace := by
    calc
      (∑ x : Fin L → Fin d, ∑ y : Fin R → Fin d,
          mpo M (L + R) (Fin.append x y) (Fin.append x y)) =
        ∑ p : (Fin L → Fin d) × (Fin R → Fin d),
          mpo M (L + R) (Fin.append p.1 p.2) (Fin.append p.1 p.2) :=
        (Fintype.sum_prod_type' _).symm
      _ = ∑ σ, mpo M (L + R) σ σ := by
        apply Fintype.sum_equiv (blockSplitEquiv d L R).symm
        rintro ⟨x, y⟩
        simp only [blockSplitEquiv_symm_apply]
      _ = (mpo M (L + R)).trace := rfl
  rw [diagonalCutMass]
  simp only [diagonalCutRealMatrix, Matrix.map_apply, diagonalCutMatrix_apply_eq_mpo]
  calc
    (∑ x : Fin L → Fin d, ∑ y : Fin R → Fin d,
        (mpo M (L + R) (Fin.append x y) (Fin.append x y)).re) =
      ∑ x : Fin L → Fin d,
        (∑ y : Fin R → Fin d, mpo M (L + R) (Fin.append x y) (Fin.append x y)).re := by
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      exact (Complex.re_sum Finset.univ _).symm
    _ = (∑ x : Fin L → Fin d, ∑ y : Fin R → Fin d,
        mpo M (L + R) (Fin.append x y) (Fin.append x y)).re :=
      (Complex.re_sum Finset.univ _).symm
    _ = (mpo M (L + R)).trace.re := congrArg Complex.re hsum

/-- Positive semidefiniteness and positive total mass make the normalized
diagonal cut coefficients a joint probability distribution.

This is the normalization step for the fixed-length diagonal restriction of
arXiv:1606.00608, Proposition 4.5.  The source normalization convention is at
lines 792--793; see
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
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

This is a fixed-length classical restriction of the bound invoked in the proof
of arXiv:1606.00608, Proposition 4.5, lines 1316--1320, using
Riazanov--Vyalyi, Theorem 4.1 (arXiv:1704.06507).  It does not assert a bound
for unrestricted quantum mutual information.

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

/-- **Classical estimate for a diagonal MPDO.** A globally diagonal MPDO with
positive trace at length `L + R` has classical mutual information of its
normalized diagonal coefficients at most `2 * log D`.

Global MPDO positivity supplies the fixed-length positive-semidefinite
hypothesis, while `diagonalCutMass_eq_trace_re` identifies the positive trace
with the normalization mass.

This is a diagonal classical restriction of the bound invoked in the proof of
arXiv:1606.00608, Proposition 4.5, lines 1316--1320, using Riazanov--Vyalyi,
Theorem 4.1 (arXiv:1704.06507).

**Scope restriction (globally diagonal MPDO):** Proposition 4.5 concerns
arbitrary MPDOs, whereas this theorem treats globally diagonal tensors.  The
unrestricted quantum question is documented in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem diagonalMPDO_classicalMutualInformation_le_two_log [NeZero D]
    (M : MPOTensor d D) (hdiag : M.IsDiagonal) (hmpdo : M.IsMPDO)
    (L R : ℕ) (hN : 0 < L + R) (htrace : 0 < (mpo M (L + R)).trace.re) :
    Entropy.classicalMutualInformation (normalizedDiagonalCutDistribution M L R) ≤
      2 * Real.log D := by
  apply diagonalFiniteChain_classicalMutualInformation_le_two_log M L R
  · exact hdiag (L + R) hN
  · exact hmpdo (L + R) hN
  · rwa [diagonalCutMass_eq_trace_re]

end MPOTensor
