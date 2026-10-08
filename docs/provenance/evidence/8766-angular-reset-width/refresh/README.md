# Reset-width provenance refresh

The current ledger is bound to public source commit
[`b07d3ca6e4eb6b197f03aa67ff94b54a8cb41cca`](https://github.com/LionSR/TNLean/commit/b07d3ca6e4eb6b197f03aa67ff94b54a8cb41cca).
Its tree is identical to the locally checked source commit
`a506d572c05ef07a7d1c748c214f73b7b00603bc`:
`518a22dc7e45fca80645c305f6ef0496c4f7484b`.
The only production changes add the September 24, 2026 manuscript date to
four provenance comments. Lean statements and proof tokens are unchanged.

[verification.json](verification.json) preserves the actual execution identity,
commands, exit codes, elapsed times and source/output hashes. The five fresh
checks passed: the targeted native build (2,047 jobs, module 2.7 seconds),
strict production elaboration, four consumer examples, four guarded axiom
tests and four raw axiom reports. Every raw report uses only `propext`,
`Classical.choice` and `Quot.sound`. The informational hash-command diagnostics
remain in the raw log.

The ledger uses `build` only for the native Lake build. Strict source,
consumer and guarded checks use `source-audit`; only the raw declaration
reports use `axioms`. Each log has a receipt-derived command, revision,
elapsed-time and exit-code preamble, followed by the unchanged captured
output. Empty successful outputs are not fabricated into diagnostic text.

The original author checkpoint, historical commands and logs, rendering
evidence and failed attempts remain in the [original packet](../README.md).
They are not reclassified as executions of the new source revision. This
refresh does not claim a new full-root build or blueprint render. The result
remains the numerical reset-width estimate; physical reset and annular
induction are outside its scope.
