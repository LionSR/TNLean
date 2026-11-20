# Canonical Interaction combined verification checkpoint

The tested production source is `3a41ae4b75eda0cb0daa0c75b74db5908b61a7f9`,
with QICLean `729428582b78ab7529b3796099193649f947354a`.
This remains an integration checkpoint, not permission to merge or a whole-library pass.

## Intake and scope

PEPS `5cef6f44c4334b7dd09acb47cf96eb2df7067d20` contributes exactly its 107
allocated production files, two changed fixtures and its source ledger. The third
PEPS fixture required no source edit. MPS `550b63ccb49e4784cd42949d53996197fd0ce073`
contributes only commits `54ab66ae0`, `42229ed94`, `550b63ccb`: 85 production changes,
one fixture and evidence. Its 86th allocated file is unchanged. The duplicate
shared commit `81e70a7d4` was excluded after its stable patch-id matched `b992c791`.
Both authors reported zero compilations; that evidence is distinct from our results.

The documentation lane was merged once through `e740d046791bf4159a5d756eef7043dd71e11992`,
whose only change after `f8e80bac` corrects the fifth boxEntropy parameter to D₀.
All 34 allocated documents and seven dedicated audit paths were checked against
that allocation. The complete five-fixture acceptance report was read.

The shared wrapper now calls the canonical conversion without a norm-bound argument,
uses `hamiltonian`, and constructs its zero chain with `term` and `mem`.
The explicit targets retain arbitrary dimensions and j,m; normalization, projector
PSD, membership, non-singleton zero-H examples and weighted optimizer conclusions.
No sign premise on J or stronger Hermiticity premise was introduced.

Integration repairs remove GraphPropagation's private canonical-to-canonical adapter
and pass h directly in all four calls. Remaining production edits only rename unused
nested hypothesis binders and wrap long lines in BoxEntropySupremum,
InitialBoxEstimate, BoundaryTheorem and LatticeChannelSpatialOmission. The generic
fixture's long call is wrapped. Original strict failures remain in the logs.

## Actual verification

- Six shared owners: direct overlay compilation and strict passed for all six.
- MPS allocation: 8/86 compiled and strict; the other 78 are not certified here.
- PEPS allocation: 17/107 compiled and strict; the other 90 are not certified here.
- All five complete regression fixtures passed strict at exact recorded sources.
- Full source-sync passed: 35,615 refs, 307,809 source declarations, zero missing,
  leanok-missing, duplicate tags, stale declarations or missing declaration-file entries.
- Blueprint roles and added prose checks passed. Selector test script: 84 tests passed.
  The first unittest-module invocation failed due to its missing scripts import path;
  the documented direct script invocation passed. Both logs are retained.
- `check_selector.py` invokes the actual selector with each owner and each fixture
  as its individual changed-path input. All expected fixtures remain selected.
- The six review-reported long-line locations are repaired; GraphPropagation has
  neither the adapter definition nor calls through it. `git diff --check` passed.

`coverage.json` gives every allocated production path a separate compile/strict
status, preserving source SHA correspondence. `results.jsonl` includes commands,
source commit, pin, PID/process group, time, exit code and log name. All compiler
command time, including earlier shared checks and failed attempts, totals 600.161 s.
Editing time was not separately instrumented. No duration is inferred from waiting.

Each compilation used the pinned Lean executable, package flags, two threads,
a private overlay and an exclusive lock; strict adds warningAsError. Existing warm
TN/QIC artifacts were read, not modified. No Lake/root/full-library build ran.
Source-sync used clean manifest-matching QIC/mathlib checkouts, with fetching disabled.
The previous documentation-stage 976-missing failure is retained unchanged in its
original audit directory; this new successful source report does not rewrite it.

No full Blueprint PDF/web build, compiled checkdecls or whole-library verification
was run. The source reports and five fixtures do not establish semantic equivalence
of every migrated consumer. Independent lane reviews and the remaining exact-source
checks still govern acceptance. No current PR or external author branch was changed.
No validation queue remains running at this checkpoint.
