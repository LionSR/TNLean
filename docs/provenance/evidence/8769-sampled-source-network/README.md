# Actual sampled-source factors and zero-party gates

Source freeze: `0f932eb5719ee74b302a2393662c11d382acb89c`.

`SampledSourceNetwork` identifies the actual Gaussian endpoint factors, their
shared sample average, and the actual prepared source positions with the
unordered participant-pair sample edges. The equivalence preserves chronological
gate occurrences, endpoint sets and literal sample indices. The common density
labels have the square of the actual branch cardinality. Thus the virtual
alphabets are bounded by `max(M²,k)` from the actual branch-count bound `M`;
private dimensions and source Schmidt ranks do not enter this estimate.

`ZeroPartyGates` proves that a gate on no participating parties acts by the sum
of its given branch coefficients, both on scalar memory and beside arbitrary
spectator memory. Its actual contraction bounds that scalar's norm by one.
The participation-based theorem derives the empty local party type internally,
and its printed signature is retained in the kernel report. Empty branch sets
are permitted and contribute scalar zero. This preserves the manuscript's
classification of only one-party gates as private.

Both modules passed strict direct Lean checks and independent mathematical
review. The 14 selected kernel reports contain only `propext`, `Classical.choice`
and `Quot.sound`. Only imports among the new modules are renamed to the scratch
prefix `TNLeanReduction`; mathematical namespaces and proof bodies are retained.
Exact production source, checked source, artifact and baseline hashes are in
`direct-checks.json`.

These statements do not identify the complete sampled physical operator with
the contraction of chronological party-local matrices. That identity and the
actual output-order/physical-readout join remain separate proofs. No full Lake
build, blueprint verification, or canonical provenance replay is asserted here;
those checks belong to integration.

The tactic scan is preserved in `tactic-pattern-scan.log.gz`; its exact
decompressed SHA-256 is `491f415cc22edbb3da2dc32b56d34a365a91bbcd3f8fbf1cef321c3d86b48120` (1235 bytes).

The complete named public inventory contains 17 sampled-source declarations
and four scalar-gate theorems. All 21 have now been audited, with only the
standard axioms, in `AllPublicAxioms.lean` and `all-public-axioms.log`; the
exact list is `public-declarations.json`. The earlier 14 selected reports
remain unchanged. One anonymous local decidable-equality instance and two
private helper lemmas are implementation details, excluded from this public
inventory. Canonical integration may audit the generated declarations as well.
