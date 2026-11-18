# pin729 MPS validation shard — partial evidence

Source head: `6b7fb2e27dbc6856091e593e4226d350403beb8a`.
Production tree: `b535ccb984038d4b8f8d47bb874bc17035ab5f03`, equal to b63e6f6c.
QIC pin: `729428582b78ab7529b3796099193649f947354a`.

Selection is exactly existing tn_affected paths starting TNLean/MPS/, plus
MergeRounds once. 864 affected + 1 extra = 865. The removed PEPS owner is the
only nonexistent path among the original 1669; it is not in this shard.
Manifest SHA256: `6154be849927457d11a0e1666a778d3d68383e5884e16c08ec1252c5694cf7f5`.
The coordinator-owned impact.json was not edited.

## Execution

Recovery found no active Lean/Lake jobs, about 14 GiB disk and 16 GiB RAM
available. All old worktrees were retained; see worktree-preservation.json.
No exact-pin QIC/TN cache was available on this machine. Ten external package
HEAD revisions match the candidate manifest; see package-revisions.json.
Only those matching external package caches were reused. Old QIC/TN oleans
were excluded from LEAN_PATH. QIC was checked out separately at the exact pin.

MergeRounds compiled first. Then two small MPS targets were compiled using
a 39-module dependency closure; the smallest twenty shard targets followed,
reusing those outputs in a 122-module union closure. No parallel duplicate
builds were launched. Ordinary dependency compilation includes necessary
Circuit/Algebra/QIC files, but strict checks ran only on the twenty selected
MPS targets. No PEPS consumers or fixtures were tested.

## Resumed bounded verification

The queue is now continuing all remaining manifest targets in 30-target batches,
with two workers and a single writer per dependency. summary.json and
results.jsonl are the checkpoint record; the last committed snapshot can lag
the live queue. not-run.txt means not yet completed at the snapshot, not failure.
The original 20 successes and 122 dependency artifacts were hash-verified and
reused. No old QIC/TN oleans enter LEAN_PATH. A 5 GiB free-space guard pauses
new work; exclusive PEPS dependencies also require coordinator handling.

Each target gets direct Lean olean compilation and strict elaboration. These
are not Lake or full-library results. Each command records exact SHA, UTC,
command, exit code and elapsed time. Production editing remains zero. Evidence
preparation was not separately timed. Source errors are reported without edits.

The generated exact-source cache remains at /tmp/pin729-mps-olean (local to
this environment; not assumed shared with other workers). Driver scripts are
saved here; their absolute paths describe this execution environment. No
shared candidate branch, external author branch, PR, or issue was modified.
