/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVBNTTheoremEquivalence
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPCanonicalForm
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPViaTS

/-!
# BNT algebra tensor clause for the rescaling-stable example

This file attaches the existential BNT algebra tensor clause to the explicit
rescaling-stable renormalization fixed-point tensor.
-/

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The rescaling-stable tensor has a BNT algebra tensor clause.

This is the existential tensor attachment only: it supplies the witness asserted
by the BNT algebra clause without identifying its labels or coefficient data with
any separately defined explicit family.

Source: CPSV16, Theorem 4.14(i)--(ii), lines 972--985, and Appendix C.4,
lines 1929--2085. -/
theorem R_hasBNTAlgebraTensorClause : HasBNTAlgebraTensorClause R :=
  (MPOTensor.isRFPViaTS_iff_hasBNTAlgebraTensorClause
    R R_toMPSTensor_isCPSVCanonicalForm R_isMPDO).mp isRFPViaTS_R

end MPOTensor.RescalingStableLengthDependentRFP
