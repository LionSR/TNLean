# Conditional labelled entropy: exact-source evidence

Published source revision: `422315a7315d33f110722443bd7e2430b1bab698`.
Local checked snapshot: `a108cb155aefd63521428c68602a43200cc06195`.
Identical Git tree: `62a9e15d99788e0b21ef29561bc22bf006e128d1`.
Accepted QICLean pin in all five fields: `826a56f5d2a3d0c5b5027c4ab536d24feadbdbb6`.

The immutable published source and local checked snapshot have identical whole
Git trees. Each Lean source/regression also matches the SHA256 of its actual
recorded invocation. `checks.json` preserves the six original command records,
working directories, options, timings, source/artifact hashes and output paths;
the corresponding `.log` files contain the unmodified compiler output (successful
silent runs legitimately have empty logs). Both old/new production and regression
checks passed, each serially with a 90-second limit, one thread, package options,
Mathlib standard linters, warnings-as-errors, and explicit autoImplicit=false for
regressions. The two axiom reports cover all nine consumer declarations and use
only propext, Classical.choice, and Quot.sound.

`accepted-pin-audit.json` verifies the exact imported 66-module TN/QIC source and
artifact closure, unchanged QIC toolchain/dependency configuration, all five
manifest/lakefile pin fields, and preservation of the original 8760 ledger.
No Mathlib cold build or cache trace edits were used. `preflight.log` preserves
static checks including all 29 cache/workflow guards, generated imports, manifest
agreement, source/blueprint sync and exact pinned latexindent 3.24.7 checks of
both entropy chapters and the touched regions chapter. The provenance preflight
log describes the then-planned two new rows; this evidence commit finalizes them.

These are strict direct Lean checks and static preflight checks. They are distinct
from full Lake builds, repository CI and blueprint checkdecls, which remain the
registered publication gates. This proves only the conditional entropy estimate
with exceptional cost 2S(D); geometric counting, dimension/site-count transport
and canonical tripartite identification remain separate.

The existing issue 8760 ledger and evidence are retained byte-for-byte.
