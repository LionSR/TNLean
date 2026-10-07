# Exact PEPS dependency synchronization

The model dependency #8788 advanced to
`162fa69a88d407d97c5ce2682c95d2f87542cf10` while the original exact-PEPS draft
completed CI. The original published head
`8d40ddee6b41997d674e764e03ea7639819f94a3` passed
[PR CI run 37634745775](https://github.com/LionSR/TNLean/actions/runs/37634745775).
Its tree is `04884af1b1989cec4fcc57e73688d1b33d3d13ae`.

The dependency merge has one textual conflict, in `references.bib`; both
bibliography additions are retained. The workflow merges the dependency's cache
updates with the exact-size regression step. All five production modules, five
consumer files and the model's 161-line `Basic.lean` remain byte-identical.
No proof statement, proof body, compiler option, dependency pin or inherited
source file is changed by this resolution.

## Current evidence and historical evidence

The newly inherited provenance workflow requires publicly retrievable source
revisions. The earlier 40-declaration ledger pointed to local revision
`c9ded2f36083c837bc884ad9d7d475f9e81a514e`, which is not published. The full
checker passed in the development object database, but GitHub returned 404 for
that source commit. Such a local pass does not establish clean-clone validity.

The original ledger and validator are preserved byte-for-byte under
`docs/provenance/evidence/8773/historical/`. All earlier source manifests,
successes, failures and compiler logs remain unchanged.

New current evidence is stored under
`docs/provenance/evidence/8773/published-verification/`. The compiler checked
local revision `aaa7b1093af49a9600dbfa676fe862bd2b281c49`: a 2,820-job native
Approximation aggregate followed by 13 strict rows covering five production
files, five consumer files and three raw axiom drivers. Every check passed.
The 13 captured source hashes match the immutable publication tree, and all
45 raw axiom reports contain only the three standard axioms.

The active 40-entry ledger now refers to published revision
`8d40ddee6b41997d674e764e03ea7639819f94a3` and these new check logs. GitHub
readback verified that its complete tree equals the locally checked tree.
This identifies identical checked source bytes; it does not pretend that the
local compiler ran under the connector's different commit metadata. The
identity record spells out that distinction and records original and retained
manifest hashes. All 14 logs are byte-identical to the new compiler outputs;
only JSON log paths are shortened to basenames, with exact log hashes added.

The five downstream theorems retain their individual hash, consumer and axiom
evidence; they are not miscounted as part of the 40-entry ledger. The uniform
large-size approximation remains unproved. The successful original CI run
does not certify this later dependency synchronization; its final source head
requires its own checks.

## Application to the published branch

The evidence repair is applied directly above published head
`c7514459ea37e802c616b931bcd6baa21b555a8f`, which already incorporates model
head `6c56312f014aa744098712a260f415ff21056c0e`. This follow-up changes only
24 documentation and provenance files. All production and test sources,
dependency pins, and historical source/log bytes are unchanged.

The full checker, including the pinned upstream mathematical sources and
licenses, passes for all 166 current entries in an independent object database
fetched only from public TNLean refs. The unpublished historical source,
checked-local and preparation commits are absent from that database. The
scoped 40-entry check also passes. The retained 136-entry clean-ref report
describes the earlier dependency context; it is not rewritten as this later
166-entry check. No new Lean execution is inferred from these source checks.
