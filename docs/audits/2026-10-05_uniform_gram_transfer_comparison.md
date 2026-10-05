# Uniform physical Gram and transfer-matrix comparison

## Public statement and reuse

`MPSTensor.exists_norm_gram_transferMatrix_sub_le` in `PositivePartRate`
chooses one positive constant from the bond dimension before the physical
size, tensor, and positive semidefinite reference. Both directions use the
L² operator norm. Neither direction requires trace one, stationarity,
faithfulness, a spectral hypothesis, or a positive physical dimension.
The fixed-point tensor represents the trace-reset map only under the PSD
hypothesis; the underlying reset-map identity is algebraic.

The proof uses the existing physical Gram and reset entry identities,
then bounds one continuous linear reshuffling. The same reshuffling is an
involution, so its norm bounds the reverse direction too. No separate
channel structure or public reshuffling definition is added.

The forward bound now supplies both the faithful Lipschitz polar estimate
and the varying-PSD Hölder estimate. Their signatures are unchanged, so the
faithful exponent is not weakened. The reverse bound supplies the actual-site
Doeblin and local-window estimates, also with unchanged signatures.

The following declarations are removed, with all production consumers and
blueprint references migrated to the reverse component of the comparison:

- `MPSPreparation.exists_norm_transferMatrix_sub_le_gram_uniform_reference`
- `MPSPreparation.exists_norm_transferMatrix_sub_le_gram`

Three copies of the reshuffling argument become one. Production Lean loses
23 lines; the two strict regression examples add 22 lines. The examples
check the forward quantifier order and the reverse estimate at the zero
reference, which excludes accidental normalization or faithfulness premises.

## Import boundary and source audit

No import line changes. `PositivePartRate` was already below both overlap
modules and `InhomogeneousChoiResidual`, so the window consumers acquire no
additional spectral or normal-gauge dependency. The reachable production
source graph is acyclic. The QICLean/Mathlib search found related Choi
reshufflings but no existing tensor-level two-sided comparison with this
constant order and physical-matrix convention.

Blueprint proof dependencies now cite the shared comparison; its own proof
cites the fixed-point transfer identity. The qualitative finite-correlation
and rectangular-bond caveats are unchanged. This comparison supplies no
mixing rate by itself.

## Verification

The exact theorem bodies, both polar consumers, the actual-site and window
consumers, and all three inhomogeneous/varying/window regression files pass
a consolidated single-thread Lean check with strict implicit arguments,
standard linters, and warnings treated as errors. This is an exact-body
check, not a compilation of the production import graph. The structural
imports use the warmed source-matched preparation overlay; the two new
ordered-telescoping declarations are checked from their exact source bodies.
All 222 reachable QICLean sources match the target dependency pin; the
other dependency pins and Lean toolchain match the warm cache.

Blueprint source synchronization passes against the target-pinned QICLean
sources. Import-aggregator, file-size, numbered-file, proof-integrity,
tactic-pattern, and whitespace checks pass. The final combined pull-request
head still requires full CI, including its actual production imports and
compiled blueprint declaration checks.
