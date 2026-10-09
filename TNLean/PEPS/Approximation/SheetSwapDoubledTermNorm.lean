/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapCorrection
import QICLean.Analysis.DoubledSystemGap

/-!
# The norm of a swapped doubled interaction

The change of one doubled interaction under the actual regional sheet swap has
norm at most four times the norm of the original interaction. This estimate is
independent of its support and applies to arbitrary finite coordinate spaces.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 416–424 and 513–524, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

/-- Swapping a doubled interaction changes it by at most four times its original
norm. This is the single-interaction estimate used for the boundary perturbation
in `02-information.tex`, lines 416–424 and 513–524. -/
theorem norm_sheetSwapOp_conj_doubledHamiltonian_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (R : Finset ι) (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    ‖sheetSwapOp q R * doubledHamiltonian A * (sheetSwapOp q R)ᴴ -
      doubledHamiltonian A‖ ≤ 4 * ‖A‖ := by
  classical
  have hdouble : ‖doubledHamiltonian A‖ ≤ ‖A‖ + ‖A‖ :=
    (norm_add_le _ _).trans (add_le_add (l2_opNorm_kronecker_one_le A)
      (l2_opNorm_one_kronecker_rect_le A))
  done

end TNLean.PEPS.EncodedFrame
