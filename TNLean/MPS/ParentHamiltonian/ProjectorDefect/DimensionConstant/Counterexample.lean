/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Basic.Real.Basic
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.DimensionConstant.ProjectorWitness
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.DimensionConstant.MarkovPrimitive

/-!
# The prescribed coefficient at overlap two

For auxiliary dimension four and rate \(1/1000\), the coefficient printed
in Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation `boundAm`,
is strictly smaller than \(1/16\) at overlap two. The physical projection
lower bound needed to contradict that estimate is proved separately.

## Failure of the dimension-only coefficient at a prescribed rate

The four-dimensional weighted matrix-unit tensor has projection defect at least
\(1/16\) at overlap two. This exceeds the coefficient with \(c=16\) and
\(\lambda=1/1000\), despite its positive denominator. This tests the simultaneous
prefactor and rate assertions following Nachtergaele, arXiv:cond-mat/9410110,
Section 6, equation `boundAm`; see `docs/paper-gaps/cpgsv21_martingale_overlap.tex`.
-/

section

namespace MPSTensor.FNWDimensionConstant

/-- The proposed coefficient satisfies its denominator condition but is less
than the physical lower bound of the four-dimensional example. -/
theorem dimensionFour_coefficient_lt :
    16 * (1 / 1000 : ℝ) ^ 2 < 1 ∧
      16 * (1 / 1000 : ℝ) ^ 2 * (1 + 16 * (1 / 1000 : ℝ) ^ 2) /
        (1 - 16 * (1 / 1000 : ℝ) ^ 2) < 1 / 16 := by
  norm_num

end MPSTensor.FNWDimensionConstant

end

section

open scoped ComplexOrder

namespace MPSTensor.FNWDimensionConstant

/-- The four-site physical defect exceeds the proposed dimension-only
coefficient at rate \(1/1000\) and overlap two. -/
theorem dimensionFour_projection_defect_exceeds_coefficient :
    16 * (1 / 1000 : ℝ) ^ 2 * (1 + 16 * (1 / 1000 : ℝ) ^ 2) /
        (1 - 16 * (1 / 1000 : ℝ) ^ 2) <
      ‖(tailBoundaryMapES (matrixUnitTensor markovAmplitude) 1 3).range.starProjection.comp
          (leftBoundaryMapES (matrixUnitTensor markovAmplitude) 3 1).range.starProjection -
        ((groundSpace (matrixUnitTensor markovAmplitude) 4).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection‖ :=
  dimensionFour_coefficient_lt.2.trans_le dimensionFour_projection_defect_lower

/-- An injective tensor with a faithful primitive stationary state violates the
proposed coefficient at an admissible observable-transfer rate. The overlap is
two and both exterior intervals have length one. The product is in the
adjoint order to Nachtergaele, arXiv:cond-mat/9410110, Section 6, equation
`boundAm`; its norm is unchanged and matches the whole-increment convention.
The rate is fixed explicitly; the counterexample does not assert failure of an
eventual estimate with a tensor-dependent prefactor. -/
theorem exists_dimensionFour_counterexample :
    ∃ (A : MPSTensor 16 4) (ρ : Matrix (Fin 4) (Fin 4) ℂ),
      Kraus.IsInjective A ∧ Kraus.HasComplementaryFixedPointGap A ρ ∧ ρ.PosDef ∧
      Matrix.trace ρ = 1 ∧
      Kraus.transferMap A ρ = ρ ∧
      0 < (1 / 1000 : ℝ) ∧ (1 / 1000 : ℝ) < 1 ∧
      (∀ ν : ℂ, Module.End.HasEigenvalue (fnwTransferMap A) ν → ν ≠ 1 →
        ‖ν‖ < (1 / 1000 : ℝ)) ∧
      16 * (1 / 1000 : ℝ) ^ 2 < 1 ∧
      16 * (1 / 1000 : ℝ) ^ 2 * (1 + 16 * (1 / 1000 : ℝ) ^ 2) /
          (1 - 16 * (1 / 1000 : ℝ) ^ 2) <
        ‖(reassocTailBoundaryMapES A 1 2 1).range.starProjection.comp
            (leftBoundaryMapES A 3 1).range.starProjection -
          ((groundSpace A 4).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection‖ := by
  refine ⟨markovTensor, markovDensity, markovTensor_isInjective,
    markovTensor_hasComplementaryFixedPointGap, markovDensity_posDef, markovDensity_trace,
    markovDensity_fixed, by norm_num, by norm_num, ?_,
    dimensionFour_coefficient_lt.1, ?_⟩
  · intro ν hν hν1
    rw [markovTensor_fnwTransfer_eigenvalue_eq_zero hν hν1]
    norm_num
  · simpa only [reassocTailBoundaryMapES_one, markovTensor] using
      dimensionFour_projection_defect_exceeds_coefficient

end MPSTensor.FNWDimensionConstant

end
