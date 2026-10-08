# Verification after the regional overview correction

The three adapter ledger rows identify public source commit
`650bbc640e475cbc944b293fce2eee1b9c902d9e`. Its complete tree
`2e1a469031737c1f6921e078354e4e79591aeb39` is identical to the actual
local execution revision `c126d9ddaf9ac393290398f95e5374fabbba6a53`.
The compiler ran at that local revision. This metadata correction records
those existing runs; it does not claim a new compiler execution.

The source change replaced one overview sentence's tracking-issue reference
with the manuscript citation. Although the declarations and proofs were
unchanged, the provenance validator compares complete module bytes. The old
`bdaa988c4` reference therefore failed in
[provenance CI](https://github.com/LionSR/TNLean/actions/runs/37663808122/job/112937773274).

[checks.json](checks.json) retains the native adapter and approximation
aggregate build (3,205 jobs), four strict adapter checks, and text-style check.
All six commands exited successfully. The axiom driver reported all three
adapter declarations using only `propext`, `Classical.choice`, and `Quot.sound`.
Commands, actual execution revision, source hashes, durations, and exit codes
are preserved. All six logs are byte-identical to the original logs.
Only manifest log destinations are made relative, and log hashes are added.
[identity.json](identity.json) records the complete-tree identity and hashes.

The four dependency pin files are byte-identical to the previous checked
integration. QICLean remains at
`83fdc804bb0ce258a41d32ecb1063e0c7fa8b84c`.
The [preceding ledger](../historical/before-prose-correction-ledger.json),
the [first public-source packet](../current-verification/README.md), and
all earlier logs and identities remain preserved. The twenty-two encoder
rows and their evidence are unchanged.

These checks apply to the cited source tree. They do not establish a later
main integration build or successful final-head remote CI.
