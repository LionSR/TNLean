# Verification of dyadic layer distances and separation

The mathematical source module and its planned provenance entries were committed
at `664852f322153faceb0c63ecf30e5886bcd1f228` before recording final verification
evidence. Seven original theorems establish closed-cell distance bounds, lower
and upper endpoint-distance bounds for points in closed layers, their infimum-
distance formulation, and separation of nonadjacent closed layers. They formalize
`geometry:layer-distance` and `geometry:nonadjacent` in Section 11 of the
September 24, 2026 area-law manuscript. No upstream Lean proof text is reused.

The geometric conclusions are derived from the actual cell-index construction;
no distance or separation estimate is assumed as data. Origins are arbitrary and
dyadic scales are nonnegative. These results do not establish the two-family
construction, its repairs and birth separation, or a source headline theorem.

Verification reused the seeded hot-main and prebuilt cache in the model worktree.
The canonical wrapper `scripts/lake_build_locked.sh` ran under the same repository
lock, inherited from a process that blocks in the kernel while another build
holds it. Mathlib was not rebuilt from source. Mathematical source bytes and
dependency pins remained fixed during final verification.

The linter-bearing PEPS build, seven-name axiom audit, and complete blueprint
declaration check passed at the exact source revision. Their recorded elapsed
times are 14.139 seconds, 2.988 seconds, and 7.320 seconds, respectively.
The distance-layer module compiled in 2.0 seconds without warnings. Existing
dependency warnings remain recorded in the build log. Every reported axiom
dependency is among `propext`, `Classical.choice`, and `Quot.sound`.

The twenty-eight previously verified entries retain their source revisions and
evidence. The new logs, `8758-distance-build.log`, `8758-distance-axioms.log`,
and `8758-distance-checkdecls.log`, record command, source revision, elapsed time,
exit status, and warnings. Trailing whitespace is removed before computing the
SHA-256 values recorded in the issue-owned provenance shard.

Reproduction commands are:

```bash
scripts/lake_build_locked.sh TNLean.PEPS
scripts/lake_build_locked.sh -- lake env lean docs/provenance/evidence/8758-distance-axioms.lean
scripts/lake_build_locked.sh -- lake exe checkdecls blueprint/lean_decls
```

Maintainer mathematical review remains pending. OpenAI Codex (GPT-6) assisted
the original proofs, manuscript comparison, and verification preparation.
