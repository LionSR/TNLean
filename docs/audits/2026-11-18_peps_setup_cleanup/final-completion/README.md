# Completed old-production PEPS closure

The original manifest is completely covered by disjoint tranches 5+119+261+133+73
=591. Every path has both successful build and strict command records, independently
checked during this aggregation. The all591 manifest equals the original PEPS
partition exactly; remaining.txt is empty. Honeycomb is an additional previously
validated owner outside this manifest. No unresolved failures occurred.

After the 591-file assertion, the original runner separately built TNLean.PEPS
(225.01s) and checked it strictly (5.59s); both exit zero. PID205637/session74502
has exited. Do not restart any queue. Root and final-tranche raw logs are archived.
Earlier tranches, resource-stop records, cleanup manifests and protected hashes
remain in their original audit directories. No source/cache mutation was needed
for this final reporting step.

This is production a28 with QIC729. Shared fa9 adds two separately reviewed/tested
MPS simp changes; this ledger does not claim independent recompilation of those
changes. In particular none of this certifies the pending Interaction migration
or its source-sync, fixtures, proofs, CI or root aggregation. CI success is not
inferred from this local result. Earlier old-pin failures remain historical.
