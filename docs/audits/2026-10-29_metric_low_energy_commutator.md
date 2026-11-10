# Local low-energy commutators on finite metric spaces

This contribution restores `TNLean/Lattice/LowEnergyMetricCommutator.lean`
from preserved revision `1659116509dc8cec5d4a2aec8ddd131cc88da31d`.
The mathematical source is byte-identical, with SHA256
`cfdf600754783650b4e70fced98073d94ea96c58849e23d2582f2fd9c0ffff34`.
The comparison providers are TNLean `9ad6cdd3c23da0ce9b5e6cc36edfec99f0211ff7`
and QICLean `e51354163d2dd9cf2a15d65722c544c6b4736182`.

For finite supports separated by graph distance at least m, the compressed
commutator is bounded by

    (4 |X| + 4) ||W|| ||B|| exp(-gamma m).

The proof combines the existing finite-support propagation estimate with a
second Gaussian filter under the original Hamiltonian and its gap. Passing
to a finite metric space gives a positive decay rate for positive interaction
radius. For radius-rho observables, the prefactor is
`4 |B(j,rho)| + 4`, and the decay includes `exp(2 lambda rho)`.
The actual locally truncated Gaussian terms satisfy the estimate with the
product of norms bounded by J squared. No spectral gap of a locally
truncated Hamiltonian is assumed.

No polynomial bound on metric spheres is required for these local estimates.
Uniform sums over all sites remain a separate assertion with their explicit
geometric hypotheses. The exact zero-radius filter identities remain in
`GaussianZeroRange.lean`; the positive-radius decay formula is not asserted
at radius zero. The geometric-growth scope note records these distinctions.

## Private verification

The actual-name strict source check passes, with all 107 selected source and
object pairs unchanged. Its wall time is 57.755 seconds, so the ordinary
changed-module timing requirement remains unresolved at this stage.
A single diagnostic profile passes in 26.194 seconds; it does not replace
the ordinary timing check or change its threshold.
An imported inspection of all four public declarations passes in 37.09
seconds, with only `propext`, `Classical.choice` and `Quot.sound`.

The source-only blueprint synchronization, reader-prose and tactic-pattern
checks pass. The new two-page chapter excerpt and the revised two-page
scope note have been rendered and every page visually inspected; their
final rendering has no layout warnings. Ordinary integration builds and
compiled declaration checks remain pending.

Evidence is retained under
`/tmp/tnlean-hastings-growth-free-commutator-20261029`,
`/tmp/tnlean-hastings-metric-commutator-docs-20261029`, and
`/tmp/tnlean-metric-commutator-blueprint-sync-20261029.json`.
The source-only worktree has no Lake build directory. No Mathlib source
build or common-cache mutation was performed by this private verification.
