# Verification of dyadic layers, cell counts, and exhaustion

The two mathematical modules and their planned provenance entries were committed
at `5e863a2ef04989154da0be5fe4be0dfd85a66eb0` before recording their combined
verification evidence.
The twenty public declarations independently formalize elementary parts of
Section 11, lines 151–185, of the September 24, 2026 area-law manuscript,
`prop:two-families`. No upstream Lean proof text is reused.

The modules define translated half-open dyadic cells, their floor indices and
parents, occupied indices, planar neighborhoods, and planar layers. They prove
the index and parent identities, nesting of the actual neighborhoods, the exact
cell union for a layer, and uniform bounds on the number of layer cells. They
also prove exhaustion of the plane for a nonempty endpoint set and neighborhood
radius at least two. Scales are nonnegative integers; the origin is arbitrary.
Closure-distance and clearance estimates and the two-family construction remain
open. These auxiliary results do not prove a source headline theorem.

Verification reuses the prebuilt cache already seeded and verified in the model
worktree. The canonical repository-wide lock is provided by
`scripts/lake_build_locked.sh`. Mathlib is not rebuilt from source. The
mathematical module and dependency pins remain fixed during verification.

The official linter-bearing PEPS build, twenty-name axiom audit, and complete
blueprint declaration check all passed at the exact source revision. Their
recorded elapsed times are 42.663 seconds, 6.390 seconds, and 11.612 seconds,
respectively. Every reported axiom dependency is among `propext`,
`Classical.choice`, and `Quot.sound`; the parent-index definition has none.

The exhaustion module compiled in 8.8 seconds without warnings. The layer
module had already passed the canonical build at
`8a7ab76fcbd03b1434426ac731654ace69cbbb42` without warnings; its source bytes
are identical at the final verification revision. Warnings replayed from
existing dependencies remain in the final build log.

The new evidence is separate from the six previously verified counting results;
their source revisions and evidence remain unchanged. Logs record the command,
source revision, elapsed time, exit status, and warnings. Trailing whitespace is
removed from captured terminal output before computing the SHA-256 values
recorded in the issue-owned provenance shard.

Reproduction commands are:

```bash
scripts/lake_build_locked.sh TNLean.PEPS
scripts/lake_build_locked.sh -- lake env lean docs/provenance/evidence/8758-dyadic-axioms.lean
scripts/lake_build_locked.sh -- lake exe checkdecls blueprint/lean_decls
```

Maintainer mathematical review remains pending. OpenAI Codex (GPT-6) assisted
the original definitions and proofs, manuscript comparison, and verification
preparation.
