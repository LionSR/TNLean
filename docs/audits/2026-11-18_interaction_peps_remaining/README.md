# Remaining PEPS verification at the frozen integration source

Source: dccc85e5607077b51822664e9d475287d300d607 (production 3a41ae4b).
QICLean: 729428582b78ab7529b3796099193649f947354a.
Only the 90 PEPS paths not passed in the original combined coverage ledger are
targets. The original 17 PEPS passes, six shared owners and five complete fixtures
remain separately recorded; they are not counted as new passes here.

`manifest.txt` is sorted UTF-8 with LF and a final newline. Its SHA256 is
0df13e249d214a9a7872539d4cd364ad69322dd64c2fdb56bde4aefe873362dd.
Reconstruct it from the original `coverage.json` by selecting lane `peps` with
compile or strict other than `PASS exact source`, then sorting by path.

`target-status.json` is the target ledger; null means not yet verified, not pass.
`results.jsonl` also includes prerequisite compilations. Do not mistake the
larger command count for the number of target files passed. Each command records
source/pin, exact arguments, cwd, PID/process group, UTC start, duration, source hash,
dependency fingerprint, exit status and its retained log.

The private overlay is /workspace/reviews/interaction-shared-validation/olean.
It reuses the read-only /workspace/tn-pin729-other baseline and the recorded
shared integration checks. Reuse checks transitive TN source blob identities at
the producing commit against the frozen source and verifies dependency Git pins.
The verifier records source SHA256 values and olean fingerprints, checks dependency
source bytes before each command, holds an exclusive overlay lock, launches
controlled process groups, caps each command at 180 seconds and stops below 1 GiB.
No MPS target or root aggregation is part of the 90-target queue. No source edits
are made by the verifier. This is direct Lean overlay compilation plus strict,
not a Lake or full-library build.

The first batch permits at most five not-yet-compiled modules per target; the
second permits twenty and prioritizes SnakeGridAreaLaw's 46 overlapping targets.
The complete source import closure for Snake contains more files than that
46-target overlap. Nine missing MPS prerequisites are listed separately; their
compilation is a coordination gate, not silently added to this queue.

The adapter fix at 42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d affects exactly the
25 paths in `adapter-affected.txt`, all MPS or root aggregations, and none of the
90 PEPS targets. `final-source-reuse-proof.json` compares the full transitive TN
source blob fingerprints and the unchanged dependency manifest for each target.
It supports reuse for unchanged closures; it is not a claim of new execution at
42c4ed17. Its three changed modules and 25-path closure require separate validation.

## Final result

All 90 remaining PEPS targets passed direct overlay compilation and strict at
dccc85e5607077b51822664e9d475287d300d607. Together with the preserved 17 earlier
passes, the PEPS allocation is 107/107. None of those original 17 was recompiled.
There were 506 successful compilation commands (including prerequisites), 90
successful target strict commands, and no Lean failures. The recorded compiler
command time is 2146.653 seconds across this lane, not elapsed or editing time.

The standard-library artifact lookup guard incident is retained separately;
it happened before invoking Lean and was resolved by including the pinned
compiler's lib/lean directory in fingerprint lookup. No source check was weakened.
The final fingerprint audit reconstructed all 596 pre-command fingerprints:
zero mismatches, 506 unique fingerprints and 1699 dependency artifacts.
The underlying hash manifests are in dependency-fingerprints.tar.gz.

All 46 Snake PEPS overlap targets passed. Snake itself was not compiled: nine
MPS prerequisites plus TNLean.Algebra.FinSpanOfFinrank have no local artifact,
and all ten belong to the MPS 77-target dependency plan with matching source
hashes. snake-nine-handoff.json and snake-final-gap.json contain exact paths,
direct imports and plan records. No cross-environment cache transfer or Snake
owner transfer was attempted. The minimum next action is a coordinated exact
artifact handoff, or an explicit single-owner Snake transfer to the MPS warm
environment. Do not duplicate the queued MPS work here.

final-reuse-all.json proves unchanged transitive TN source fingerprints for
107 PEPS targets, six shared owners and five fixtures from dccc to 42c4ed17,
with identical dependency manifest and toolchain. Execution records retain
their original heads; this is hash-based reuse, not new compilation at 42c4.
The 25 affected MPS/root paths are excluded and remain with the MPS owner.

All validation processes have exited. No PR was modified, no whole-library or
root aggregation build ran, and no existing source/cache was reset or cleaned.

## Reproducible documentation checks

`source-sync-command.json` records a fresh source-sync invocation at dccc, with
complete command, cwd, selected environment, timestamps, exit, stdout/report hashes.
`check-environment.json` records Python and clean exact dependency checkouts.
`lean-binary.json` records the actual Lean executable version and hash.
The old 976-missing documentation-stage report is unchanged in its original audit.

`selector_complete.py` calls the actual selector for all nine owners explicitly
listed by FIXTURE_ACCEPTANCE, the directly exercised production interfaces,
coordinate definitions and dependency manifest, then each of the five fixtures.
The result contains 22 cases: sixteen Lean owners, one manifest and five fixtures.
This is source-level selection evidence; it does not replace Lean compilation.

Consult the final snapshot, target-status.json and process-checkpoint.json.
This completes the PEPS lane only; it is not whole-library or merge clearance.
