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

The imported modules expose the following public declarations:

* `MPSTensor.exists_tp_gauge_blockwise` — blockwise TP-gauge normalization for
  finite-direct-sum input.
* `MPSTensor.exists_tp_gauge_from_arbitrary_with_zeroTail` — TP-gauge
  normalization for arbitrary input, keeping the explicit zero-block summand.
  This is the canonical-form bridge declaration consumed by
  `SectorComparison/CommonSectorData.lean` and
  `SectorComparison/TPPrimitiveReduction.lean`.
* `MPSTensor.exists_normalCanonicalForm_of_primitive_blockDecomp` — reduction
  from a primitive blocked decomposition to blocked normal canonical-form data.

### Source-faithful PGVWC07 intermediate steps

The following declarations record the intermediate construction steps of
\cite[Theorem~Th:TIcanonical]{PerezGarcia2007Matrix}.  They are not consumed by
the canonical-form reduction used in the proof of the Fundamental Theorem
(which goes through `exists_tp_gauge_from_arbitrary_with_zeroTail` and the
after-blocking statements), but record the source proof structure for
completeness.

* `MPSTensor.exists_pgvwc07_unital_dualDiag_data_of_irreducible` — single
  irreducible-block unital and dual-diagonal form.
* `MPSTensor.exists_pgvwc07_unital_dualDiag_blockwise` — blockwise composition
  on a finite direct sum with unit weights.
* `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail` —
  arbitrary-input form with the explicit zero summand kept.
* `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_with_zeroTail_bondDimBound`
  — the length-zero dimension identity for the zero-tail form.
* `MPSTensor.exists_pgvwc07_unital_dualDiag_from_arbitrary_posMPV_bondDimBound`
  — positive-length form after stripping the zero summand.
* `MPSTensor.PGVWC07PositiveLengthWitness` — structure bundling the
  positive-length form.
* `MPSTensor.exists_pgvwc07_positiveLengthWitness` — existence of the
  positive-length witness for every MPS tensor.
* `MPSTensor.PGVWC07PositiveLengthWitness.exists_weight_normalization` —
  weight normalization on a nonempty witness.
* `MPSTensor.PGVWC07PositiveLengthWitness.exists_weight_normalization_projective`
  — projective form of the same weight normalization.
* `MPSTensor.PGVWC07PositiveLengthWitness.block_count_pos_of_exists_ne_zero_mpv`
  — a nonzero positive-length MPV coefficient forces a nonempty witness.
* `MPSTensor.exists_pgvwc07_normalized_projective_form_of_exists_ne_zero_mpv`
  — the nonzero-coefficient projective normalized form.
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_of_exists_ne_zero_mpv`
  — the nonzero-coefficient exact normalized form after a global rescaling.
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_or_forall_pos_mpv_eq_zero`
  — the zero/nonzero dichotomy for the exact normalized form.
* `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty`
  — the source-faithful PGVWC07 translation-invariant canonical-form headline
  statement.
-/
