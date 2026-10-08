# Accepted-definition geometry integration

## Scope and base

This private integration is based on accepted TNLean
`a82c6c82a9e509673f51e5bfa0bfab13be29eca6`, which pins QICLean
`eb12c672aafdb0d536253feec158edf00f69fb54`.
It contains the strict template-clearance result and the exact
nearest-neighbor crossing-budget identity, and selected template-core counts,
with their tests and mathematical
source documentation. It does not contain the held cumulative native proof
series, an energy conclusion, a weighted-shell estimate, or glossary changes.

The clearance source was prepared at
`50262d7736fafe0ad30d8df1bfe460f21c032fa0`; its concrete crossing-edge test
was extended at `881fe3ea06d221720718fda80cb1a69ca95e5eba`.
The edge-crossing source is
`3a9f75c5fb218bb33c4069f5d70ac9a4d5e3ab10`.
The selected core-count source is
`0dce10c173123d74b03f7d9d37ad37fd9b134632`. It proves `18n` at the cap
and the stronger `4n` count below the cap for the actual capped partition
of template points, without a weighted-shell sum.
The mathematical leaf files are unchanged from those private commits.
The generated area-law import and the crossing-budget blueprint entries
connect the latter leaf to the repository's existing source organization.

## Pin compatibility and validation boundary

The leaves were checked on accepted TNLean
`3d4fdd50a1cf0f24f569d01f70622f7280bfc7c6` and QICLean
`7d9e0688a55a64474707c5f5b260163e11b30128`.
The newer TNLean base changes CI event-base handling, the QIC pin, and three
unrelated Kronecker consumers. Its area-law geometry definitions are unchanged.

Recursive source inspection found all 19 TNLean/QIC dependencies imported by
the crossing-budget leaf and all eight upstream TNLean dependencies of the
clearance leaf byte-identical across these accepted bases. The 13-module
accepted source closure upstream of the selected-core leaf is also unchanged. This is a narrow
statement about these import closures: many unrelated QIC files changed.
Both repositories retain Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, identical package Lean options,
and identical non-QIC dependency manifests.

The existing strict validation records were checked against the integrated
source, the compiler SHA-256
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`,
direct import artifacts, saved outputs, and logs. All 23 crossing-budget and
16 final clearance records, plus 15 final core-count records, matched their
original source and artifact hashes.
The historical records use one compiler thread, package linter options,
warnings as errors, and a 90-second hard cap.

This source and artifact compatibility assessment is not a new compilation
at the current QIC pin. No root build, new-pin compilation, hosted CI pass,
or rendered blueprint acceptance is claimed. Current-base CI is still required.
Source-only aggregator, blueprint-declaration synchronization, prose,
numbered-file, and file-size checks are separate from kernel checking.

The retained edge-crossing history includes a 78.91-second failed timing gate.
Later successful production and regression checks do not erase that failure.
The clearance history also retains its earlier failed proof attempts, including
the first cast-normalization attempt in the concrete regression.

The core-count checks retain their failed earlier regression attempts. Their
final production and concrete tests passed in 7.70 and 13.95 seconds,
respectively; these are historical focused checks, not current-base CI.

The PR workflow now registers the four new crossing-budget and clearance
fixtures as separate serial, warning-strict checks with 90-second hard caps.
The existing mixed-square and cut-boundary steps cover the modified fixtures.
This registration is source-checked; it is not evidence of hosted execution.
