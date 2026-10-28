# Verification of the area-law construction on current main

The mathematical snapshot `fea97ebd91cb1858b670892eadbb8d5028c46b7b` proves a
polynomial successive viable-set construction and the general iid complex matrix
Bernstein inequality. The construction starts with the scalar singleton, obtains
each family from its actual predecessor by extension, size trimming, independent
bond trimming and physical Gaussian error reduction, and extracts a normalized MPS
from the span of that same run's final family.

For fixed local dimension $q\ge2$ and gap $\Delta>0$, the polynomial coefficient
and degree precede the chain length and Hamiltonian. Every retained family has
polynomial cardinality and individual bond bound. Every actual gapped ground pair
has a normalized final-span approximation with overlap at least
$1-(\Delta/169)^2/L$ and polynomial bond dimension. The statements concern these
mathematical constructions; arbitrary accuracy, computational running time and
the sharper printed parameter dependence are not asserted.

The worktree starts from main revision
`c457d2be30e12c770fb7807e822f0ca72739f498`. It was seeded by the canonical script
from clean, fully built hot-main at that exact revision, before the mathematical
changes were applied. Lean, Mathlib and QICLean dependency pins are unchanged.
Ordinary builds use `scripts/lake_build_locked.sh` and the pinned prebuilt
Mathlib artifacts. Neither integration build compiled Mathlib source.

## Verification evidence

| Mathematical snapshot | Full library | Strict changed sources | Manual public-declaration inspection | Compiled blueprint declarations |
|---|---:|---:|---:|---|
| `bacd5b7d73b144f7d828b8e0473bdfac89af3063` | 15004 jobs | 52 files | 251 declarations | Passed |
| `fea97ebd91cb1858b670892eadbb8d5028c46b7b` | 15013 jobs | 11 files | 24 newly added declarations | Passed |

All inspected declarations use only `propext`, `Classical.choice` and `Quot.sound`.
The strict checks use the package's proof options, standard linters, warnings as
errors and the unchanged 50-second per-file limit. No new reported job in either
full integration build reached the 25-second diagnostic threshold. Source and
blueprint declarations are synchronized, and completion marks refer only to the
explicitly stated mathematical scopes.

Foundation inspection is a manual local operation using temporary files. No
permanent theorem or foundation fixture is introduced, and the current-main removal
of the permanent Lean test directory is preserved. The earlier report
`2026-10-28_lvv_integrated_verification.md` concerns a historical snapshot under
the earlier policy; its fixture descriptions do not prescribe the current workflow.

## Mathematical scope and remaining work

The size-trimming theorem uses the library constant-cut estimate and corrected net
exponent. Independent bond trimming uses the corrected quadratic radius. Unknown
energy is handled by a finite family of physical Gaussian approximants, chosen
before every ground pair, with conservative polynomial parameters. See
`2026-10-28_lvv_successive_construction.md` and
`2026-10-28_physical_viable_filter.md` for the constructions and their source passages.

The matrix Bernstein theorem uses the actual centered Gram variance norms,
coefficient $1/3$ and dimension factor $2d$ on arbitrary probability spaces.
It derives integrability, centering, dilation and the required variance bound.
Its proof and source comparison are recorded in
`2026-10-28_lvv_matrix_concentration_plan.md`. The original LVV power sampler,
its simultaneous word-frequency estimate and its ground-energy dependence remain
separate from both this concentration theorem and the Gaussian construction.

The generic probability and matrix-analysis modules are staged in TNLean pending
reconciliation with the companion library's existing results and active work.
QICLean must not depend on these TNLean copies. The source-specific Hamiltonian,
filter and tensor-network constructions remain in TNLean.

The ALVV results are verified separately with their required companion revision.
Their interval and capped-gap quantitative scope, and the source's assumption of
an excited spectral value, remain explicit. The low-energy bootstrap and binary
tree are not supplied by a per-vector MPS approximation. The optimized AKLV rank
bound and the remaining Hastings source comparisons also remain distinct tasks.
The six methods and their different conclusions are compared in
`../formalization/classical-area-law-comparison.md`.
