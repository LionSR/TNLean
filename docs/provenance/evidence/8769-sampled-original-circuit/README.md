# Sampling the original distributed circuit

The four declarations in `SampledOriginalCircuit.lean` derive the coefficient bound from the original gate expansion and choose one Gaussian sample whose physical operator differs from the original physical density by at most three quarters of the prescribed error. The estimate combines the exact-source replacement bound with the sampling bound. It does not yet identify the sampled operator with a contraction of local tensors.

The source revision is `dae297bb54a3c08e41afe7e65d6d8754f1e4e06c`. Raw Lean checks use the immutable approved dependency environment and the package options recorded in `direct-checks.json`. Both compressed logs preserve the complete original output, including the empty strict-check log. Every named public declaration was audited; its dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`.

The checked copy differs from the production file only in import prefixes. The preceding physical-output modules and their evidence are recorded in `../8769-physical-first-output/`. Canonical Lake verification, blueprint declaration checking, the full-library audit, and manuscript builds are reserved for the coordinating integration branch.
