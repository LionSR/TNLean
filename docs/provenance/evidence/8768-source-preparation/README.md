# Pair-source preparation and grouping: verification evidence

The sixty public declarations in `declarations.json` were checked at source
revision `75d3f124406bf0f5b6935f77d26a818c171f3807`.
The proof of Lemma 5.1 is `partyPairEffectElimination_with_grouped_sources`.
It retains the original hypotheses and adds unrestricted grouping of sources
by unordered pairs of parties to the previous conclusions.

`direct-build.log` records successful direct Lean compilation of the five new
modules and their exact `PartyLayout` dependency, with package options and
warnings treated as errors. Source copies and output artifacts were confined
to temporary directories. This check did not run Lake or mutate a worktree's
build cache. The prebuilt dependency environment was read from the parent
party-layout worktree. A full package build remains a separate CI check.

`AllAxioms.lean` imports the resulting modules and audits every explicit public
declaration. `axioms.log` contains all sixty reports; each is a subset of
`propext`, `Classical.choice`, and `Quot.sound`. The JSON command records contain
source and output hashes. The compressed import manifests record all 4,324
modules actually imported and the SHA256 of every resolved `.olean` artifact.
The build began before the source commit was created; the final verification
compared every compiled source byte-for-byte against that commit.

The branch predates the canonical provenance framework. `validate-shard.py`
uses the packaged, unmodified checker and schema from revision
`18a6dd4d2683cea18b585ffe0467910f76eb23ff` in
`../canonical-policy-18a6dd4d`. It verifies the packaged hashes, validates this
shard with the complete branch notice scan, and checks the packaged canonical
identifier/declaration collection for collisions. The policy commit need not
be present in the checkout; the recorded proof revision must be available.
Run from the repository root, supplying a local
`openai/math` repository containing the pinned manuscript commit:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8768-source-preparation/validate-shard.py \
  --root . --shard docs/provenance/openai-math.d/8768-source-preparation.json \
  --upstream-root /path/to/openai-math
```

This is scoped validation of the new shard. It does not revalidate unrelated
historical evidence or repeat the canonical command's license-history audit.
No upstream Lean proof text was reused.

Theorem 5.2 is not established by these files. In particular, the collection
of all remaining operations into a tensor product of one map per party,
common source spaces across branches, sampling, and final compression are
subsequent mathematical steps.
