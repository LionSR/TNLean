# Source-only reduction of distributed densities

The construction formalizes the pair-effect elimination step in the proof of
Theorem 5.2 of the polynomial-PEPS manuscript, `04-compression.tex`, lines
199–229, at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
It starts from the original chronology and its actual monomial expansions.
Replacing each nonprivate gate retains one fixed normalized auxiliary vector,
all earlier auxiliary registers as spectators, and the original participating
parties. The operator error is at most `2 * δ * N`, and the actual physical
density error is at most `4 * δ * N`, where `N` counts original nonprivate gates.
For `N ≤ M`, the chosen budget gives physical error at most `ε / 2`.

The original chronology distinguishes private operations on one party from
nonprivate operations whose participant count differs from one. Empty
participating sets are permitted. The zero-nonprivate-gate case has zero error.
Whole-party input vectors may be entangled among their own private registers.
No numerical bound on private-memory dimensions is imposed.

The final regional corollary constructs the readout from one owned physical
register of dimension `d` per party and the actual discarded private registers.
Regional physical indices have cardinality and Hilbert-space dimension exactly
`d ^ A.card`. Finite-dimensionality of the discarded private memory is the
manuscript's convention, rather than a numerical dimension restriction.

All seven modules passed direct Lean checks with package options and warnings
as errors. Their temporary module paths use the distinct prefix
`TNLeanReduction`, to avoid writing into or copying the shared imported cache.
Only imports among these seven new source files were renamed for the checks;
the mathematical declaration namespaces and proof bodies were unchanged.
The 29 selected importing kernel reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The proof sources contain no prohibited
proof placeholders or additional axioms. Exact source and artifact hashes are
recorded in `direct-checks.json`.

This evidence records local elaboration and kernel checks. The production
module names still require the integration owner's canonical checks with a
coherent imported-artifact set. A full Lake build, full blueprint rendering and
declaration check, and canonical provenance replay have not been run for this
branch. The full distributed compression theorem and the area-law theorem
remain unfinished; subsequent sampling and polynomial bounds are separate
arguments.

The final seven-module chain was recompiled against the recovered immutable
Gaussian artifact environment, preserving all 14,643 audited imported module
hashes. The source freeze is `1458060da2d52da27b1c89d5eadc0c2c36550781`. The final importing audit has 34
stock-axiom reports, adding the actual owned-register restriction and its
labelled basis. `immutable-direct-checks.json` records the exact source,
checked-source, and generated artifact hashes, and the recovered baseline
manifest hash. The earlier 29-report evidence is retained separately. These
checks still use the temporary module prefix and do not replace canonical
integration verification.

The tactic-pattern scan is preserved byte-for-byte in `tactic-pattern-scan.log.gz`.
Its decompressed SHA-256 is `7e60fcde4c763ca9b289a8d98dd1e9767774edda911121a4e57933df40332c42` (1235 bytes).
