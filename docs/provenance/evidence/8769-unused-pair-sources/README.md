# One-dimensional sources on unused pairs: verification evidence

The eleven public declarations in `declarations.json` were verified at source
revision `8eccd116408d22a115220881e7e07c96aa4f23ea`. They formalize the insertion
of one-dimensional sources on unused pairs in the proof of Theorem 5.2,
`eq:compression-source-gate`, lines 233–251 of the pinned polynomial-PEPS
manuscript. Existing source records remain unchanged. The final local
factorization explicitly retains one-dimensional halves on pairs absent
from the original monomial.

All three exact-source modules compiled directly with the package options and
warnings treated as errors, without diagnostics. `direct-build.log` records
the commands and source hashes. No Lake command was used; source copies and
output artifacts remained in temporary directories, and pinned predecessor
artifacts were read without modification. A full package build is a separate
CI check.

The imported audit `AllAxioms.lean` checks all eleven explicit public
declarations. Every report in `axioms.log` contains only `propext`,
`Classical.choice`, and `Quot.sound`. The compressed manifests record all
4,334 imported modules and the SHA256 of each resolved artifact. Final
verification compared the committed sources with the compiled snapshots and
rechecked every imported artifact hash.

The branch predates the canonical provenance framework. The copied
`validate-shard.py` loads its unmodified checker and schema at immutable
revision `18a6dd4d2683cea18b585ffe0467910f76eb23ff`, verifies their hashes,
validates all three stacked shards with a complete branch notice scan,
and checks for collisions against the canonical ledger:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-unused-pair-sources/validate-shard.py \
  --root . \
  --shard docs/provenance/openai-math.d/8768-source-preparation.json \
  --shard docs/provenance/openai-math.d/8769-party-factorization.json \
  --shard docs/provenance/openai-math.d/8769-unused-pair-sources.json \
  --upstream-root /path/to/openai-math
```

This scoped check does not repeat unrelated historical verification or the
canonical command's license-history audit. The eleven proofs are independent
formalizations; no upstream Lean proof text was reused.

The result concerns each allowed monomial on its prescribed finite gate party
type. Common source spaces across different monomials, sampling, and the
remaining compression argument are separate constructions. The full
Theorem 5.2 is not established by this contribution.

The `blueprint` directory records source comparison, full-source synchronization,
acyclic mathematical dependencies, formatting, focused PDF inspection, and
browser checks. The corresponding report distinguishes the 20,076 mathematical
entries from their 20,082 unique declaration references.

The `regression` directory checks the empty and singleton party cases by
instantiating the actual completion theorem. Both final strict compilations and
imported axiom reports pass. Source and log files are compressed without changing
their bytes; recorded hashes refer to the uncompressed contents. The compiled
regression artifact and rendered PDF are represented by their hashes rather
than committed. An initial
linter diagnostic about an unused enumeration instance is retained separately
from the successful final check.
