# Regional embedding public-source provenance migration

The three adapter entries previously named local-only author revision
`61f76928032b1eef7417ae9d79dda93796019eb6`. Their original ledger is preserved
unchanged in `docs/provenance/evidence/8770-region-embedding/historical/`.
Every pre-existing adapter evidence file remains unchanged.

The current verification revision is public commit `bdaa988c4cf11aa6c5b5b9e6af6cfb4945a63be7`.
It has the identical complete source tree as the actual checked integration
revision `22452861589bfb0717cad045c390736147ee94d7`. The eight source/test/audit
files are also byte-identical to the historical author revision. The
[identity record](../provenance/evidence/8770-region-embedding/current-verification/identity.json)
records these comparisons and the exact dependency hashes.

The new native aggregate and seven strict checks actually ran with QICLean
`83fdc804bb0ce258a41d32ecb1063e0c7fa8b84c`, inherited from main #8811.
Earlier checks used `8d5389d23c8e675a0117442e1a0d2c683a4bad41`; those
records have not been relabelled. Lean and Mathlib pins did not change.
The [new evidence packet](../provenance/evidence/8770-region-embedding/current-verification/README.md)
retains all eight commands, execution revision, file hashes, timings, exit codes
and output. Only one private path in the native build log is normalized;
its original and retained hashes are recorded, and seven logs are unchanged.

The three current ledger rows now name the published source and those new runs.
The twenty-two encoder rows retain their existing public source reference.
This migration changes only metadata, documentation and retained evidence.
It does not modify proof bytes, dependency pins, or old logs, and does not
claim that final-head remote CI has already completed.
