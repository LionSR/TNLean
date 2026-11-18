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

## Stop at the first strict failure

Final candidate result: 327 targets passed build and strict; one target failed
strict; 537 targets were not executed. 1166 direct compiler builds (including
required dependencies) and 328 target strict invocations were recorded.
No other shard strict checks ran. No compiler process remains.

Hastings/SpectralCutoff.lean line 188 passes ordinary compilation but fails
strict on linter.unnecessarySimpa. The exact original log and exit code 1 are
retained. Suggested correction: replace the complete map_zero proof with
`map_zero' := by simp`. A temporary copy passed strict in 8.55 seconds;
this is not counted as a candidate pass and the production source is unchanged.
The first scratch attempt merely replaced the tactic token and was rejected
because `simp using` is invalid; both scratch attempts are retained separately.
No disabling of linters or suppression of the original failure occurred.

Further continuation needs coordinator disposition of the source failure.
The proposed one-line patch is evidence only, not applied to any production
branch. Build commands total 3563.41 seconds, strict commands 1204.34 seconds;
parallel command durations are summed, not claimed to be wall-clock duration.
Production editing time is zero; evidence-editing time was not separately timed.

## Authorized continuation after isolated fix

Single-source fix commit ef098ad32a728e847957320f9cf79ddcfce5245a replaces
SpectralCutoff map_zero proof with `by simp`; latest candidate a28f35a6 has
identical pre-fix SpectralCutoff content. Separate targeted compilation and
strict passed in 11.67/7.66 seconds. The original strict failure and original
artifact hash remain in the historical records. The standalone fix branch is
fix/pin729-spectralcutoff-simp; no shared PR branch was changed.

All 327 previously passed source hashes and 1166 prior artifacts were verified
before continuation. None of those 327 targets imports SpectralCutoff through
its dependency closure. The continuation runs only the 537 not-yet-executed
manifest targets. New TN records use ef098ad32 (same production tree as the
original candidate except this fix), with the same exact QIC pin.
MPS.lean root aggregation is not in the 865-path manifest and will be separate.

## Second stop: RenyiApproximation strict linter

After the authorized isolated fix, 428 manifest targets have passed build and
strict. RenyiApproximation.lean:229:4 fails strict on unnecessarySimpa; ordinary
build succeeded. ChainBootstrap has only a completed build; 435 further targets
are untouched. There are two historical strict failures, of which SpectralCutoff
is resolved by ef098ad32; RenyiApproximation remains a candidate failure.

The minimal suggestion (evidence patch only) replaces the entire line-229
`simpa using Finset.card_le_univ ...` branch with `simp`. A temporary copy passed
strict in 4.44 seconds. No second production fix was applied. Original logs and
exit codes remain intact, and the temporary result is not a candidate pass.

The MPS root is additional to the 865-path manifest and has not been run. Its
project closure is 5667 modules, with 1368 already compiled locally. There was
no cold full-library or root build. The QCA coordination check found all 98
MPS modules within our dependency closure (none direct manifest targets): 17
are compiled, 81 pending. ListOfFn is compiled too. All 99 source hashes match
other evidence 7ffe53e6. No cache payload was transferred. Direct Lean outputs
have no Lake traces; a later sanctioned transfer must validate actual payload,
source and transitive dependencies rather than infer cache hits from metadata.

Production change is exactly the single authorized SpectralCutoff line; no
shared PR or external branch was modified. Timing for that edit was not
separately measured. All verification processes have completed or stopped.

## Second isolated repair and continued queue

Authorized Renyi unnecessarySimpa correction is a separate commit
ec6168f62952ad7c7e0dbb48758f3736b33af88b on the existing isolated repair
branch. Only line 229 changes to `simp`; no mathematical assumptions change.
428 prior target source hashes and every recorded latest artifact were checked.
None of the 428 passed targets depends on RenyiApproximation. The original
Renyi failure and first SpectralCutoff failure remain historical evidence.
The repaired target gets separate fixed build/strict logs. Remaining queue
resumes with 435 untouched targets plus the one build-only target, without
recompiling completed targets. New TN source provenance is ec6168f62.

## Third stop: missing CSLib dependency

Current trial includes exactly two one-line proof simplifications, in commits
ef098ad32 and ec6168f62. The second fixed target passed direct build/strict in
17.74/3.41 seconds. Both original linter failures are preserved and resolved
for this isolated source tree; completed targets were hash-checked and reused.

The continuation reached 535 passed targets, one build failure and 329 untouched
targets. Algorithm/Query.lean could not import Cslib.Algorithms.Lean.Query.Bounds:
unknown module prefix Cslib. This environment has no CSLib directory/artifact in
its recorded LEAN_PATH. The candidate pins CSLib to
acab13b776722f5efa897c780d6fa1a3069d709e. This is not a proven source defect.
The queue stopped as instructed for errors other than unnecessarySimpa.
No dependency fetch/build workaround or mathematical change was attempted.
Next action is narrowly supplying that exact CSLib Query closure, then resuming
the failed target plus untouched targets. MPS root remains an extra unverified
target. All compiler processes stopped; approximately 13 GiB disk remains.

Original SpectralCutoff fixed-run logs were already pushed in 9630ab7e; their
zero length records successful diagnostic-free executions, not missing logs.
spectralcutoff-fixed-verification.json indexes the two complete command records
with exact source SHA, pin, exit code, elapsed time and source/artifact hashes.

## Narrow CSLib environment repair

535 previously passed target hashes were rechecked. The pinned official CSLib
checkout was genuinely absent, not merely missing from LEAN_PATH. The official repository was checked out at
acab13b776722f5efa897c780d6fa1a3069d709e; only the eight-module transitive
closure of Query.Bounds was compiled, with matching Lean
v4.36.0-rc1 and the candidate's resolved external dependencies. The existing
cache root is already on LEAN_PATH; no pin or production source changed.

All eight dependency builds passed. Query then passed build/strict separately
in 4.76/3.34 seconds; original unknown-prefix failure remains untouched.
cslib-query-plan.json records topology and source hashes, cslib-results.jsonl
records exact commands, and cslib-artifacts.json includes module sidecars.
Query.after-cslib logs distinguish the successful repair from the original
failure. Remaining 329 targets resume without rerunning old target successes.
