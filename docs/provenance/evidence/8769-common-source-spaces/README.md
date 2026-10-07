# Common private source spaces: verification evidence

The 34 public declarations in `declarations.json` were verified at source
revision `b8864ae6ca2a3fbd5ecf0989e682a38d33ee02a6`. They establish the common
private source spaces in the proof of Theorem 5.2 of the pinned polynomial-PEPS
manuscript, `04-compression.tex`, lines 233–299.

The construction orders and orients the actual branch sources, embeds their
halfspaces into finite orthogonal sums, and recovers every original preparation
by local coordinate projections. The resulting branch maps are contractions.
The weighted gate identity retains the original coefficients and external
register layouts. A further finite tensor-support argument supplies common
Euclidean coordinates for all branch source vectors and recovers them by local
isometries. This argument concerns algebraic tensor products and requires no
finite-dimensionality assumption on the original ambient spaces. It does not
bound the private coordinate dimensions.

All nine exact-source modules compiled directly with the package options and
warnings treated as errors, without diagnostics. `direct-build.log` records the
commands, source hashes, and durations. No Lake command was used: sources were
copied to temporary directories, new output artifacts were written there, and
predecessor artifacts were read without modification. A full package build is
a separate CI check.

The imported audit `AllAxioms.lean` checks all 34 explicit public declarations.
Every report in `axioms.log` contains only `propext`, `Classical.choice`, and
`Quot.sound`. The compressed manifests record all 4,343 imported modules and
the SHA256 of each resolved artifact. Final verification compared the committed
sources with the compiled snapshots and rechecked all imported artifact hashes.

The source revision predates the canonical provenance framework.
`validate-shard.py` uses the packaged, unmodified checker and schema from
revision `18a6dd4d2683cea18b585ffe0467910f76eb23ff` in
`../canonical-policy-18a6dd4d`. The policy commit need not be available in a
checkout; the proof revisions named by the four provenance files must be
available. The following command checks all four contributions, their source
notices, the manuscript labels, and collisions with the packaged canonical
identifier collection:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-common-source-spaces/validate-shard.py \
  --root . \
  --shard docs/provenance/openai-math.d/8768-source-preparation.json \
  --shard docs/provenance/openai-math.d/8769-party-factorization.json \
  --shard docs/provenance/openai-math.d/8769-unused-pair-sources.json \
  --shard docs/provenance/openai-math.d/8769-common-source-spaces.json \
  --upstream-root /path/to/openai-math
```

This scoped check does not repeat unrelated historical verification or the
canonical command's license-history audit. All 34 declarations are independent
formalizations; no upstream Lean proof text was reused.

The `blueprint` directory records exact source comparison, complete source
synchronization, an acyclic dependency graph, canonical formatting, and focused
PDF and web checks. The new mathematical pages were inspected visually, and the
browser checks passed at desktop and mobile widths. The report distinguishes
these checks from a full-root compiled declaration check. The one small PDF
overfull-line diagnostic is recorded with its visual assessment.

The `regression` directory contains seven checked theorems covering an empty
branch family with a nonempty pair inventory, unequal one- and two-dimensional
branch sectors, normalization, and recovery of a nonreal source phase by both
endpoint projections. Strict compilation and an imported standard-axiom audit
pass. Source and log compression is deterministic; the recorded hashes refer
to their uncompressed bytes.

The sampling estimates, their application to the actual circuit density, and
the remaining compression argument are separate obligations. This contribution
does not establish the full Theorem 5.2.
