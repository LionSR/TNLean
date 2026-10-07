# Canonical provenance policy for independent replay

This directory contains the exact canonical checker and schema from TNLean
revision `18a6dd4d2683cea18b585ffe0467910f76eb23ff`. Their original bytes are
unchanged. `manifest.json` records their source paths and SHA256 hashes.

`canonical-collisions.json` records the identifier, case-folded repository name,
and downstream declaration of all 151 entries in that revision's root ledger
and its four shards. It is the exact projection used by the previous
collision check, sorted by identifier. The manifest records the hash of each
source ledger and the resulting comparison file. Historical proof evidence is
not required for this collision check and is not revalidated.

`validate-shards.py` verifies all three packaged file hashes before loading the
unmodified checker. It validates the requested shards, scans every provenance
notice in the current branch, and rejects collisions with the canonical
collection. It does not read the policy revision from Git. The proof revisions
named by the shards must still be present, as in a normal clone of the branch;
the canonical checker compares their source bytes with the working tree.

The per-contribution `validate-shard.py` commands delegate to this shared
implementation. Supply every shard whose notices occur in the checked branch.
The optional `--upstream-root` performs the manuscript-label checks against the
pinned upstream source. The canonical command's separate license-history and
full upstream-source audits are outside this scoped replay.
