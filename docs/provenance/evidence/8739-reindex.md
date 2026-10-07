# Verification of regional states under site relabelling

The mathematical source module and its planned provenance entries were committed
at `19521214f674c3e8c375f89e4f76ac788ad6eea3` before recording verification evidence.
The six original declarations define configuration transport, regional
configuration transport, and vector relabelling, then prove covariance of
regional reduced states, invariance of regional entropy, and preservation of
the Euclidean norm. They formalize the finite tensor-factor conventions in
Section 2, `sec:prelim`, lines 10–25, of the September 24, 2026 area-law manuscript.
No upstream Lean proof text is reused.

The reduced-state and entropy identities hold for every site bijection preserving
the specified cut. The norm identity holds for every site bijection. No
normalization, lattice-adjacency, or spectral-gap hypothesis is imposed. The
proofs use the pinned existing QICLean partial-trace and entropy APIs and Mathlib's
configuration isometry. This finite-domain relabelling is distinct from the
native-PEPS conversion. It does not prove a source headline theorem.

Verification reused the already seeded and verified prebuilt cache in the model
worktree and the canonical repository-wide lock provided by
`scripts/lake_build_locked.sh`. Mathlib was not rebuilt from source. Mathematical
source bytes and dependency pins remained fixed during verification.

The linter-bearing PEPS build, six-name axiom audit, and complete blueprint
declaration check all passed at the exact source revision. Their recorded elapsed
times are 13.373 seconds, 3.680 seconds, and 7.223 seconds, respectively.
The regional-reindexing module compiled in 3.8 seconds without warnings.
Warnings replayed from existing dependencies remain in the build log. Every
reported axiom dependency is among `propext`, `Classical.choice`, and `Quot.sound`.

The six previously verified regional-state entries retain their existing source
revision and evidence. The new logs record command, source revision, elapsed time,
exit status, and warnings. Trailing whitespace is removed before computing the
SHA-256 values recorded in the issue-owned provenance shard.

Reproduction commands are:

```bash
scripts/lake_build_locked.sh TNLean.PEPS
scripts/lake_build_locked.sh -- lake env lean docs/provenance/evidence/8739-reindex-axioms.lean
scripts/lake_build_locked.sh -- lake exe checkdecls blueprint/lean_decls
```

Maintainer mathematical review remains pending. OpenAI Codex (GPT-6) assisted
the original definitions and proofs, manuscript comparison, and verification
preparation.
