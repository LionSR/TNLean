# Collection of local operations by party: verification evidence

The sixty-one public declarations in `declarations.json` were checked at source
revision `7edadbfe8cf40ee520349a3f7068e8a48914c2f3`. They prove the collection
of local operations in the proof of Theorem 5.2, equation
`eq:compression-source-gate`, lines 233–251 of the pinned polynomial-PEPS
manuscript. The final result concerns one allowed monomial on its prescribed
finite gate party type. Common source spaces across monomials, one-dimensional
padding of unused pairs, sampling, and the remaining compression argument
are subsequent steps.

`direct-build.log` records successful direct Lean compilation of all seven
modules with the package options and warnings treated as errors. The exact
source copies and output artifacts were confined to temporary directories;
no Lake command or worktree build-cache mutation was used. The pinned
prebuilt dependency environment and the preceding source-preparation
artifacts were read without alteration. A full package build remains a
separate CI check.

`AllAxioms.lean` imports the resulting modules and audits every explicit public
declaration. All sixty-one reports in `axioms.log` contain only `propext`,
`Classical.choice`, and `Quot.sound`. The JSON command records contain source
and output hashes. The compressed manifests record the 4,331 modules actually
imported and the SHA256 of each resolved artifact. Compilation preceded the
source commit; final verification compared every compiled source with the
committed blob and confirmed that all seven output artifacts and all seventeen
recorded direct dependency artifacts were unchanged.

`PartyFactorizationRegression.lean.gz` checks a local scalar multiplication by
one half on empty memories: its party remains recorded, an empty party list
cannot cover it, and the contraction obtained from the factorization theorem
has that scalar value. Further examples check reversed register order and
an additional party with no registers. The compressed source preserves the exact tested bytes. Compilation with the same strict
options and the two endpoint axiom reports passed; exact commands and hashes
are recorded in `regression-check.json`.

The branch predates the canonical provenance framework. `validate-shard.py`
uses the packaged, unmodified checker and schema from revision
`18a6dd4d2683cea18b585ffe0467910f76eb23ff` in
`../canonical-policy-18a6dd4d`. It verifies the packaged hashes, validates
both shards with the complete branch notice scan, and checks the packaged
canonical identifier/declaration collection for collisions. The policy commit
need not be present in the checkout; the recorded proof revisions must be
available. Run from the repository root, supplying a local
`openai/math` repository containing the pinned manuscript commit:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-party-factorization/validate-shard.py \
  --root . \
  --shard docs/provenance/openai-math.d/8768-source-preparation.json \
  --shard docs/provenance/openai-math.d/8769-party-factorization.json \
  --upstream-root /path/to/openai-math
```

This is scoped validation of these shards. It does not repeat unrelated
historical verification or the canonical command's license-history audit.
Every proof in this contribution was independently written; no upstream Lean
proof text was reused.
