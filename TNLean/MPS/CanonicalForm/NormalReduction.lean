/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction.Main
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge

/-!
# Normal canonical-form reduction

This module keeps the historical import path
`TNLean.MPS.CanonicalForm.NormalReduction` available while the development is
split across two supporting modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.NormalReduction.Main` — the reduction from a
  primitive weighted block decomposition to blocked normal canonical-form data.
* `TNLean.MPS.CanonicalForm.NormalReduction.TPGauge` — the blockwise TP-gauge
  normalization results, including the arbitrary-input zero-tail statement.

## Main statements

The imported modules provide the original public declarations:

* `MPSTensor.exists_tp_gauge_blockwise`
* `MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp`
* `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail`
-/
