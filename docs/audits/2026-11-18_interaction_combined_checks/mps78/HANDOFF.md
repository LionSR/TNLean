# Controlled MPS handoff

The coordinator waits for the existing pin729 runner and all its compiler writers
to exit. It does not kill, restart or modify the old source queue. It snapshots
and publishes that queue's final ledger including every original failure, then
rechecks source, artifact, transitive dependency, toolchain and package revisions.

Only eligible completed artifacts are copied (never hard-linked) to the private
`/tmp/interaction-mps77-olean` overlay. The old writable cache is absent from the
new LEAN_PATH. One worker runs the smallest dependency closure first; the first
three target successes are a small initial cluster, then each ten-target batch is
published. Every completed command is fsynced to results77.jsonl. The disk guard
stops below 1 GiB free. No whole-library or Lake build is claimed.

Resume using coordinator.py. It holds an exclusive process lock and revalidates
successful source/artifact hashes before skipping completed work. Inspect
coordinator-status.json and publication-results.jsonl; push errors preserve local
evidence. A failure stops the new queue and publishes its original log.

The exact input remains dccc85e5607077b51822664e9d475287d300d607, production
3a41ae4b75eda0cb0daa0c75b74db5908b61a7f9, QIC pin729. Later three-owner cleanup
is not included and needs a separately coordinated reverse-closure recheck.

SnakeGridAreaLaw belongs exclusively to 695c. peps46.txt lists its 46 PEPS
allocated owners; peps46-cache-request.json provides exact source hashes and
provenance requirements. snake-source-closure.json includes all project imports
and hashes so 695c can identify a minimal missing MPS prerequisite set without
rebuilding the complete closure. This worker executes only manifest77.txt.

## Superseding final-version plan

Before any valid MPS77 writer started, the waiting coordinator was stopped alone.
Only the three-file 42c4ed17 delta was applied; production files now match exact
42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d. The old865 runner was not stopped.
MPS77 now runs directly at that final version; the affected 21 are a subset,
not a second queue. Source/recursive dependency checks invalidate all affected
old artifacts. Prior dccc records and the quarantined premature attempt remain
historical evidence, not final-version passes.
