/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction.Main
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge
import TNLean.MPS.CanonicalForm.NormalReduction.WeightNormalization

/-!
# Normal canonical-form reduction

This module keeps the historical import path
`TNLean.MPS.CanonicalForm.NormalReduction` available while the development is
split across supporting modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.NormalReduction.Main` — the reduction from a
  primitive weighted block decomposition to blocked normal canonical-form data.
* `TNLean.MPS.CanonicalForm.NormalReduction.TPGauge` — the blockwise TP-gauge
  normalization results, including the arbitrary-input zero-tail statement.
* `TNLean.MPS.CanonicalForm.NormalReduction.WeightNormalization` — the
  finite-family positive-weight normalization for the positive-length witness.

## Main statements

The imported modules provide the original public declarations:

* `MPSTensor.exists_tp_gauge_blockwise`
* `MPSTensor.exists_pgvwc07_unital_dualDiag_blockwise`
* `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail`
* `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`
* `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound`
* `MPSTensor.exists_pgvwc07_positiveLengthWitness`
* `MPSTensor.PGVWC07PositiveLengthWitness.exists_weight_normalization`
* `MPSTensor.PGVWC07PositiveLengthWitness.exists_weight_normalization_projective`
* `MPSTensor.PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv`
* `MPSTensor.exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv`
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv`
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_or_forall_pos_mpv_eq_zero`
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty`
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_with_zeroTail`
* `MPSTensor.exists_pgvwc07_normalized_projective_form_or_forall_pos_mpv_eq_zero`
* `MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp`
* `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail`
-/
