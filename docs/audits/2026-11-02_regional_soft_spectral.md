# One actual regional approximation for every buffered cutoff

The new theorem first constructs one Hermitian matrix product operator
from the original local interactions and the regional soft replacements.
Only then does it quantify over every real cutoff and positive buffer.
Both directed low-energy comparisons follow from its actual global norm
error. The witness includes the original approximation bound and both
Hermiticity proofs. No successful spectral approximation, gap, unique
ground state or restriction on intervening eigenvalues is supplied.

The common loss uses `U = norm G + xi`, the lower endpoint
`min (c - 1) (-U)` and the explicit finite window count. It is independent
of the represented approximant. The construction permits zero regions,
overlapping regions, an empty interaction family and local dimension one.
Positive accuracy and buffer are explicit. The tensor family is the same
for every cutoff, buffer and vector.

This is a bounded auxiliary for ALVV, arXiv:1602.08828v2,
`t:aisefficient` and `t:aisgaplessefficient`, lines 1412–1420 and
1446–1457. It compares the actual regional soft sum with its represented
approximant. Comparison with the original Hamiltonian, construction of a
filter and the source's full GEN bounds remain separate. The corrected
interaction-label estimate is still used. The false printed cluster
estimate, the counterexamples and the independent-scale restriction remain
recorded in `docs/paper-gaps/alvv16_cluster_approximation.tex`.

Build inputs and the prebuilt Mathlib record were guarded. No provider,
dependency cache or Mathlib source was changed.

The mathematical book entry is included. Ordinary integrated full-library
and compiled-book checks remain pending. Foundation commands occur only
in the temporary audit; no permanent Lean fixture is introduced.
