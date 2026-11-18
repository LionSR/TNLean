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

All 20 selected targets passed both direct Lean olean compilation and strict
elaboration. These are **not Lake build results**, full-library results, or
verification of the remaining 845 targets. results.jsonl records exact source
SHAs, commands, exit codes, UTC starts, and durations; logs are alongside it.
summary.json separates build/strict time and records zero production editing.
Evidence-preparation time was not separately timed. The source and artifact
hashes support checking the new cache independently.

No source errors were observed and no production code was changed. A static
import scan gives 5156 project modules in the entire slice closure. This
initial bounded batch stopped before an unplanned cold rebuild of that
closure; not-run.txt explicitly lists the 845 unexecuted targets. They require
coordinated coherent cache delivery or further bounded dependency batches.
There are no still-running commands from this evidence batch.

The generated exact-source cache remains at /tmp/pin729-mps-olean (local to
this environment; not assumed shared with other workers). Driver scripts are
saved here; their absolute paths describe this execution environment. No
shared candidate branch, external author branch, PR, or issue was modified.
