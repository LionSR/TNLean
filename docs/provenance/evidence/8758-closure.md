# Verification of dyadic cell and layer closures

The mathematical source module and its planned provenance entries were committed
at `d1dd8af2bd97fcc76b4aea489adca0ac6f5455ef` before recording verification evidence.
The two original theorems identify the closure of a half-open dyadic cell with
its closed rectangle and the closure of an actual layer with the finite union
of its cell closures. They use the finite-dimensional geometric conventions of
Section 11, lines 151–189, in the September 24, 2026 area-law manuscript,
`prop:two-families` and `geometry:layer-distance`. No upstream Lean proof text
is reused. These auxiliary closure formulas do not establish the layer-distance
estimate, clearance estimates, the two-family construction, or a source headline
theorem.

Verification reused the already seeded and verified prebuilt cache in the model
worktree and the canonical repository-wide lock provided by
`scripts/lake_build_locked.sh`. Mathlib was not rebuilt from source. Mathematical
source bytes and dependency pins remained fixed during verification.

The linter-bearing PEPS build, two-name axiom audit, and complete blueprint
declaration check all passed at the exact source revision. Their recorded elapsed
times are 32.647 seconds, 2.833 seconds, and 10.185 seconds, respectively.
Both theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The retained build output contains no warnings attributed to the closure module;
warnings replayed from existing dependencies remain recorded.

The twenty-six previously verified entries retain their existing source revisions
and evidence. The new closure logs record command, source revision, elapsed time,
exit status, and warnings. Trailing whitespace is removed before computing the
SHA-256 values recorded in the issue-owned provenance shard.

Reproduction commands are:

```bash
scripts/lake_build_locked.sh TNLean.PEPS
scripts/lake_build_locked.sh -- lake env lean docs/provenance/evidence/8758-closure-axioms.lean
scripts/lake_build_locked.sh -- lake exe checkdecls blueprint/lean_decls
```

Maintainer mathematical review remains pending. OpenAI Codex (GPT-6) assisted
the original proofs, manuscript comparison, and verification preparation.
