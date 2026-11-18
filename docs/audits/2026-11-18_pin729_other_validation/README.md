# Independent pin729 validation: non-MPS/non-PEPS shard

Validated production source commit: `6b7fb2e27dbc6856091e593e4226d350403beb8a`.
QIC pin: `729428582b78ab7529b3796099193649f947354a`.
The evidence commits change only this directory, not production sources or pins.

Selection: existing `tn_affected` paths in the fixed commit's integration impact.json,
excluding prefixes `TNLean/MPS/` and `TNLean/PEPS/`; root aggregators remain selected.
213 paths; SHA256 of sorted UTF-8 LF-terminated manifest:
`1f4bd46fccef6467f0c98ec2266c0fd0594f9f47788e49f14e9dd5be01cccff8`.

`results.jsonl` records actual commands, UTC start/end, execution seconds and exit
codes. `command-logs.tar.gz` contains completed command outputs. `snapshot.json`
lists passed/failed/blocked/remaining targets. Remaining is NOT a passing result.
The original batch is session 89069. No second queue was launched.

Initial old-pin QIC artifacts were copied independently; Lake revalidated and
rebuilt needed artifacts against the exact new pin. Mathlib pins match, and
`lake exe cache get` with workspace XDG_CACHE_HOME succeeded (9047 artifacts,
no downloads). Original worktrees and caches were preserved.

Root aggregators requiring large missing cross-family closures are not authorized
cold builds. They require matching warm artifacts and later verification. No
MPS/PEPS subtree strict checks or coordinator fixtures are part of this shard.

Build/strict execution durations include compiler work and command waits; no
separate CPU-time measurement is claimed. Preparation and monitoring are outside
those totals. Production proof/source editing time is zero. This is compilation
evidence, not a new mathematical review or whole-library validation.

## Final outcome

The original queue completed: 209 targets passed both build and strict; 4 root
aggregators remain unverified. There are no observed Lean source errors.
Lattice hit the 600-second command limit. MPS and PEPS were not launched.
QCA was stopped after 49.34 seconds: the automatic cwd-based guard could not
read /proc process cwd, so manual scoped termination was required. Its raw
nonzero status is preserved and is not a source-failure diagnosis. No root
strict command ran for these four targets. No second queue or retry was started.

See final-summary.json for exact timing and classifications. The driver returned
0 after recording all outcomes; that is not a claim that all 213 targets passed.
All selected source hashes and the pin/toolchain/lakefile were checked against
the fixed source commit. There are no active Lake/Lean/driver/guard processes.
Four defunct child-process entries remain under PID 1, with no executing work.
