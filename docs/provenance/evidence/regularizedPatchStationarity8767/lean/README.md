# Regularized coordinate-unitary validation

These are actual bounded local runs against the exact published native-minimum
base `e9311cbbaf55517308f416b008df5ddafcc047c9` and accepted QICLean revision
`378bef486fc0241dee8ad875ccaf659d51d33ac9`. The source/artifact audit verifies
85 project-module pairs, including every imported QIC source against its pinned
Git blob. Mathlib uses the existing pinned prebuilt cache; no cold build ran.

Each compiler invocation uses one thread, a 90-second ceiling, the package
options, the Mathlib standard linters, and warnings-as-errors. Regressions also
set `autoImplicit=false`. Production and regression logs are empty on success.
Pre/post source-closure snapshots and exact artifact hashes are in
`final-runs.json`. The external axiom-reporting file disables only the
hash-command linter to allow its eighteen `#print axioms` commands. All reported
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The cache is an explicitly source-audited compiler overlay, not a fabricated
Lake build cache. No `.trace` files were manufactured. A full `lake build` was
not run locally and remains a CI gate. The included checker scripts record the
original workspace paths and make the exact source/artifact checks explicit.
The eight actual final runs are summarized in `validation-summary.json`.
