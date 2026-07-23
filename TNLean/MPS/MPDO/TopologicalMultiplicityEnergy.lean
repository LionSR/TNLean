/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import TNLean.MPS.MPDO.TopologicalDensityDecomposition

/-!
# The retained one-site multiplicity energy

For the topological decomposition of a length-independent renormalization
fixed-point matrix product density operator, the multiplicity-weight factor
comes from the strictly positive diagonal multiplicity matrices in the
vertical canonical form. This file defines the corresponding one-site
operator on the retained physical coordinates and its Hermitian logarithmic
energy.

The terminal eigenvalues in the spectral topological factor are not
logarithms in this construction. They remain nonnegative coefficients of the
topological projectors, so their possible zero values cause no difficulty for
the finite logarithmic energy. This file treats only the retained one-site
factor and does not construct the many-body Hamiltonian $H_N$.

## Main results

* `MPOTensor.BNTFusionTensorClause.retainedMultiplicityOperator_posDef`:
  the retained multiplicity operator is positive definite.
* `MPOTensor.BNTFusionTensorClause.retainedMultiplicityOperator_isUnit`:
  the retained multiplicity operator is invertible.
* `MPOTensor.BNTFusionTensorClause.exp_neg_retainedMultiplicityEnergy`:
  exponentiating the negative one-site energy recovers the multiplicity
  operator exactly.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 (local source lines 943–951): positivity of the diagonal
  multiplicity matrices.
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  local source lines 999–1002: the retained multiplicity tensor factor.
* The many-body Gibbs theorem is stated later in the same source, local lines
  1013–1016; it is not formalized in this file.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The positive multiplicity weight attached to one retained physical
coordinate. The weight depends on its BNT label and multiplicity coordinate,
and is independent of its simple-bond coordinate.

Source: CPSV16, Proposition 4.13 (local source lines 943–951) and
local source lines 999–1002. -/
def retainedMultiplicityWeightEntry (H : BNTFusionTensorClause M)
    (u : Fin H.verticalRetainedDim) : ℂ :=
  let px := verticalCopyCoordinateEquiv H.bondDim H.multiplicity u
  H.weight px.1.1 px.1.2

/-- In retained copy coordinates, the one-site entry is the corresponding
diagonal entry of the multiplicity matrix.

Source: CPSV16, local source lines 999–1002. -/
@[simp]
theorem retainedMultiplicityWeightEntry_verticalCopyCoordinateEquiv_symm
    (H : BNTFusionTensorClause M) (p : H.VerticalCopy)
    (x : Fin (H.bondDim p.1)) :
    H.retainedMultiplicityWeightEntry
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩) =
      H.weight p.1 p.2 := by
  unfold retainedMultiplicityWeightEntry
  rw [Equiv.apply_symm_apply]

/-- Every retained one-site multiplicity weight is strictly positive.

Source: CPSV16, Proposition 4.13 (local source lines 943–951). -/
theorem retainedMultiplicityWeightEntry_pos (H : BNTFusionTensorClause M)
    (u : Fin H.verticalRetainedDim) :
    (0 : ℂ) < H.retainedMultiplicityWeightEntry u := by
  unfold retainedMultiplicityWeightEntry
  exact H.weight_pos _ _

/-- The real part of every retained multiplicity weight is strictly positive.

Source: CPSV16, Proposition 4.13 (local source lines 943–951). -/
theorem retainedMultiplicityWeightEntry_re_pos (H : BNTFusionTensorClause M)
    (u : Fin H.verticalRetainedDim) :
    0 < (H.retainedMultiplicityWeightEntry u).re :=
  (Complex.pos_iff.mp (H.retainedMultiplicityWeightEntry_pos u)).1

/-- The positive diagonal multiplicity operator on the retained one-site
physical space.

Its entry at the coordinate `u ↔ ((α, q), x)` is `H.weight α q`.
Source: CPSV16, local source lines 999–1002. -/
def retainedMultiplicityOperator (H : BNTFusionTensorClause M) :
    Matrix (Fin H.verticalRetainedDim) (Fin H.verticalRetainedDim) ℂ :=
  Matrix.diagonal H.retainedMultiplicityWeightEntry

/-- The retained one-site multiplicity operator is positive definite.

Source: CPSV16, Proposition 4.13 (local source lines 943–951). -/
theorem retainedMultiplicityOperator_posDef (H : BNTFusionTensorClause M) :
    H.retainedMultiplicityOperator.PosDef := by
  exact Matrix.PosDef.diagonal H.retainedMultiplicityWeightEntry_pos

/-- The retained one-site multiplicity operator is invertible.

Source: CPSV16, Proposition 4.13 (local source lines 943–951). -/
theorem retainedMultiplicityOperator_isUnit (H : BNTFusionTensorClause M) :
    IsUnit H.retainedMultiplicityOperator :=
  H.retainedMultiplicityOperator_posDef.isUnit

/-- The real one-site energy associated with a retained multiplicity weight.

Only the strictly positive multiplicity weight is logged. The terminal
eigenvalues belong to the separate topological factor and are not part of
this definition.

Source: CPSV16, Proposition 4.13 (local source lines 943–951) and
local source lines 999–1002. -/
def retainedMultiplicityEnergyEntry (H : BNTFusionTensorClause M)
    (u : Fin H.verticalRetainedDim) : ℝ :=
  -Real.log (H.retainedMultiplicityWeightEntry u).re

/-- The Hermitian diagonal one-site multiplicity energy on the retained
physical space.

Source: CPSV16, Proposition 4.13 (local source lines 943–951) and
local source lines 999–1002. -/
def retainedMultiplicityEnergy (H : BNTFusionTensorClause M) :
    Matrix (Fin H.verticalRetainedDim) (Fin H.verticalRetainedDim) ℂ :=
  Matrix.diagonal fun u ↦ (H.retainedMultiplicityEnergyEntry u : ℂ)

/-- The retained one-site multiplicity energy is Hermitian.

Source: CPSV16, Proposition 4.13 (local source lines 943–951). -/
theorem retainedMultiplicityEnergy_isHermitian (H : BNTFusionTensorClause M) :
    H.retainedMultiplicityEnergy.IsHermitian := by
  unfold retainedMultiplicityEnergy
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  rw [isSelfAdjoint_iff]
  ext u
  simp [Complex.conj_ofReal]

private theorem exp_log_retainedMultiplicityWeightEntry
    (H : BNTFusionTensorClause M) (u : Fin H.verticalRetainedDim) :
    NormedSpace.exp
        ((Real.log (H.retainedMultiplicityWeightEntry u).re : ℝ) : ℂ) =
      H.retainedMultiplicityWeightEntry u := by
  rw [← NormedSpace.ofReal_exp_ℝ_ℝ,
    ← Real.exp_eq_exp_ℝ,
    Real.exp_log (H.retainedMultiplicityWeightEntry_re_pos u)]
  apply Complex.ext
  · rfl
  · exact (Complex.pos_iff.mp (H.retainedMultiplicityWeightEntry_pos u)).2

/-- Exponentiating the negative retained one-site energy gives the
multiplicity operator exactly.

Only the strictly positive multiplicity weights enter the logarithm. The
possibly zero terminal eigenvalues remain coefficients of the separate
topological factor.

This identity concerns the retained one-site multiplicity factor only; it does
not construct the many-body Hamiltonian $H_N$ from the Gibbs theorem at local
source lines 1013–1016.

Source: CPSV16, Proposition 4.13 (local source lines 943–951) and
local source lines 999–1002. -/
theorem exp_neg_retainedMultiplicityEnergy (H : BNTFusionTensorClause M) :
    NormedSpace.exp (-H.retainedMultiplicityEnergy) =
      H.retainedMultiplicityOperator := by
  have hneg :
      -H.retainedMultiplicityEnergy =
        Matrix.diagonal fun u ↦
          ((Real.log (H.retainedMultiplicityWeightEntry u).re : ℝ) : ℂ) := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp [retainedMultiplicityEnergy, retainedMultiplicityEnergyEntry]
    · simp [retainedMultiplicityEnergy, retainedMultiplicityEnergyEntry, huv]
  rw [hneg, Matrix.exp_diagonal]
  ext u v
  by_cases huv : u = v
  · subst v
    simp [retainedMultiplicityOperator,
      exp_log_retainedMultiplicityWeightEntry]
  · simp [retainedMultiplicityOperator, huv]

end MPOTensor.BNTFusionTensorClause
