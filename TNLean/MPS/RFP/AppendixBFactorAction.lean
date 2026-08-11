/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.AppendixBStructuralData
import TNLean.MPS.RFP.PairLiftCoordinates

/-!
# Appendix B factor actions

This file identifies the two hatted Appendix B coefficient representatives
with their left and right three-site factor actions.
-/

open scoped Matrix BigOperators InnerProductSpace Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-! ### Appendix B factor actions -/

/-- The hatted Appendix B (AX) coefficient representative acts on a
homogeneous three-single-site coefficient space by
\(\widehat Q_{AX}\otimes 1\) under the canonical right-associated reindexing.

This is only the three-single-site coefficient-factor specialization of the
left local action in Definition D.2. It does not construct a projector for an
arbitrary factorization
\(\mathcal H_A\otimes\mathcal H_X\otimes\mathcal H_B\).

Source: arXiv:1606.00608, factor spaces at lines 2185--2186 and Definition D.2,
lines 2205--2218. -/
theorem AppendixBStructuralData.appendixBQAX_factor_action
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finThreeArrowEquiv (Fin d))
        (finThreeArrowEquiv (Fin d))
        (LinearMap.toMatrix' (leftPairLift hStruct.appendixBQAXOnCoeffSpace)) =
      appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' hStruct.appendixBQAXOnCoeffSpace)) := by
  exact leftPairLift_toMatrix_reindex _

/-- The hatted Appendix B (XB) coefficient representative acts on a
homogeneous three-single-site coefficient space by
\(1\otimes\widehat Q_{XB}\) under the canonical right-associated reindexing.

This is only the three-single-site coefficient-factor specialization of the
right local action in Definition D.2. It does not construct a projector for an
arbitrary factorization
\(\mathcal H_A\otimes\mathcal H_X\otimes\mathcal H_B\).

Source: arXiv:1606.00608, factor spaces at lines 2185--2186 and Definition D.2,
lines 2205--2218. -/
theorem AppendixBStructuralData.appendixBQXB_factor_action
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Matrix.reindex (finThreeArrowEquiv (Fin d))
          (finThreeArrowEquiv (Fin d))
          (LinearMap.toMatrix' (rightPairLift hStruct.appendixBQXBOnCoeffSpace)) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' hStruct.appendixBQXBOnCoeffSpace)) := by
  exact rightPairLift_toMatrix_reindex _


end MPSTensor
