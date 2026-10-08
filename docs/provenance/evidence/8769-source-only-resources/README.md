# Resources and original physical dimensions

The source freeze is `17af56b27c467ab1f6ea88b5636c9c854b75e052` on `codex/peps-source-only-reduction`.
The four replacement-resource modules and two physical-dimension modules extend
the source-only density reduction. They independently formalize the corresponding
steps in the proof of Theorem 5.2 of the polynomial-PEPS manuscript,
`04-compression.tex`, lines 137–151, 199–251 and 342–364, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For original monomial count `K`, effect count `r`, and absolute coefficient-sum
bound `S`, every gate of the actual source-only replacement has monomial count
at most `K * m^r` and absolute coefficient sum at most `S`. The chosen stack
length satisfies `m ≤ (r*S/δ)^2 + 2`. These bounds are derived from the original
expansions and the actual replacement coefficient function; they are not
additional premises about the replacement circuit.

A prepared gate on `q` parties has exactly `q.choose 2` common source positions.
Thus an original circuit with `N` nonprivate occurrences and at most `b` parties
per occurrence yields at most `N * b.choose 2` positions. Its participating set
at each occurrence and each party's participation count over the whole circuit
are preserved exactly.

The physical register at party `p` retains its original dimension `d p`.
The actual tensor memory selected by a region `A` has dimension
`∏ p ∈ A, d p`, bounded by `D ^ A.card` from the original local bounds.
The regional readout is constructed from the dependent tensor basis and the
actual discarded private memory. No padding or equal-dimension hypothesis is
used. The final whole-party-input corollary proves actual physical density error
at most `ε / 2`, choosing the budget from the original gate-count upper bound.
Private finite dimensions have no numerical bound.

All six modules passed strict direct Lean checks against the recovered immutable
Gaussian artifact environment. The checks use the separate temporary module
prefix `TNLeanReduction`, with only imports among new modules renamed; public
mathematical namespaces and proof bodies are unchanged. Exact production source,
checked source, artifact and imported-baseline manifest hashes are recorded in
`direct-checks.json`. The resource audit has 31 stock-axiom reports, and the
family-dimension audit has 15. Together with the separately preserved 34 core
reports, there are 80 selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

These records do not assert a full Lake build, full blueprint declaration check
or rendering, or canonical provenance replay for this branch. Those belong to
the integration verification. They do not establish the subsequent sampled
operator-network construction or either full headline theorem.

The tactic-pattern scan is preserved byte-for-byte in `tactic-pattern-scan.log.gz`.
Its decompressed SHA-256 is `04f27572e81cae76bdf33c60032368d3ff9f8026d84f81b06099c5b5aedf5243` (1235 bytes).

The final newline correction is frozen at
`1ad40310757fb5d95345a431038b4427c539739c`. The two affected module
checks and the repeated 31-report resource audit are recorded in
`format-checks.json` and `format-resources-axioms.log`. The original
checks above remain unchanged as historical records.
