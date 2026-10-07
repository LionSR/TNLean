# Encoder provenance migration after the validator update

This records the earlier local migration checkpoint. The adapter publication
blocker described below is resolved by the subsequent
[public-reference migration](2026-10-07_region_embedding_public_provenance.md).

The current provenance schema accepts `build`, `axioms`, and `source-audit`
command kinds. The original twenty-two encoder records used `elaboration`
and `test`, and referred to the local author checkpoint
`4fa931f810ac576e0142fa955af5fcbd71b2615a`.

The original ledger, command logs, verification index, and README are preserved
unchanged in the [historical archive](../provenance/evidence/8770-hole-encoder/historical).
All previously retained evidence remains unchanged at its original location.
The current ledger contains new command records from the actual integrated
checks at `8602b340cfe0b3b73bad634a06b75f9dd6b20049`; no old command or outcome
has been relabelled as a new run.

The current encoder verification revision is the public source commit
`d92310cca4f63cf1c2b0c91936e538f80288b48c`. Four independently compared files
are byte-identical there, at the original author checkpoint, and at the
checked integration revision: production, consumers, guards, and the raw
audit driver. The [identity record](../provenance/evidence/8770-hole-encoder/current-verification/identity.json)
lists every hash. The public revision identifies source bytes; the compiler
execution revision remains explicit in the separate run records.

The aggregate builds, strict consumer and guard checks, and fresh raw audit
passed. All twenty-two encoder declarations use only the standard three
axioms. The [current evidence packet](../provenance/evidence/8770-hole-encoder/current-verification/README.md)
also retains the adapter's integrated checks without modifying its ledger.

The three adapter records still name local-only verification revision
`61f76928032b1eef7417ae9d79dda93796019eb6`. Even when the full validator passes
locally with the pinned manuscript source, those references remain unresolved
for a clean public-only CI context. Publication and a subsequent truthful
public-reference migration require authorization. This work publishes
nothing and changes no production proof, test, import, router, or workflow.
