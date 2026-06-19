/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Examples.Cluster
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Zero correlation length of the GHZ and cluster states

This module records the zero-correlation-length property of the GHZ and cluster
states, contrasting them with the AKLT state (`TNLean.MPS.Examples.AKLTCorrelation`),
whose transfer map has a subleading eigenvalue `-1/3` and hence a finite
correlation length `ξ = 1/log 3`.

Both the GHZ tensor and the length-`2` blocked cluster tensor are renormalization
fixed points: their transfer maps are idempotent.  By the single-block
equivalence `zcl_iff_idempotent_transfer`, an idempotent transfer map has zero
correlation length, so the connected correlator is independent of the separation
(here, constant beyond range, in contrast to the exponential `(1/3)ⁿ` decay of
the AKLT state).

## Main results

* `ghz_isZCL` — the GHZ tensor has zero correlation length
* `clusterBlocked_isZCL` — the blocked cluster tensor has zero correlation length

The supporting blocked-cluster transfer-map idempotence theorem is proved in
`TNLean.MPS.Examples.Cluster`.

## References

* RMP review (arXiv:2011.12127), Example III.1 (GHZ) and Appendix (cluster
  state).  Renormalization fixed points have zero correlation length.
* arXiv:1606.00608, Section 3.2 — the single-block zero-correlation-length
  equivalence with transfer-map idempotence.
-/

open scoped Matrix BigOperators
open Matrix MPSTensor

namespace MPSTensor

/-! ### GHZ -/

/-- The GHZ tensor has zero correlation length: its idempotent transfer map
(`ghz_isRFP`) yields correlations independent of the separation.  This is the
contrast with the AKLT state, whose subleading eigenvalue `-1/3` gives a finite
correlation length. -/
theorem ghz_isZCL : IsZCL ghzTensor :=
  (zcl_iff_idempotent_transfer ghzTensor).mpr ghz_isRFP

/-! ### Cluster -/

/-- The blocked cluster tensor has zero correlation length: its idempotent
transfer map yields correlations independent of the
separation.  The single-site cluster transfer map is not idempotent; blocking
two sites produces the renormalization fixed point. -/
theorem clusterBlocked_isZCL : IsZCL clusterBlocked :=
  (zcl_iff_idempotent_transfer clusterBlocked).mpr clusterBlocked_transferMap_idempotent

end MPSTensor
