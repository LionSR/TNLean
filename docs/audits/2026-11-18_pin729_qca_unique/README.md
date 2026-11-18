# QCA unique non-MPS dependency batches

Source 6b7fb2e27dbc6856091e593e4226d350403beb8a, QIC pin
729428582b78ab7529b3796099193649f947354a. Exactly 36 allowlisted targets
passed Lake build and strict, first 6 as a resource pilot, then the remaining 30.
The complete commands, UTC times, PID/PGID, return codes and outputs are retained.
The runner used an exclusive worktree lock, explicit cwd, independent process
groups and a 1 GiB free-space stop condition. Both batches exited successfully.

No MPS target, ListOfFn, or QCA root was invoked. Build outputs were checked for
actual Built entries: none of those forbidden modules was rebuilt. Previously
passed 209 shard targets were not rerun as targets. Production sources are unchanged.
This is dependency verification, not a QCA root pass; original shard coverage
remains 210/213. Of the original 159 missing QCA closure artifacts, 123 remain:
98 MPS, ListOfFn, 23 non-MPS awaiting MPS, and the root itself.

## Cache reuse and export boundary

Actual artifacts remain under
/workspace/tn-pin729-other/.lake/build/lib/lean/.
cache-artifacts.json records source and .olean/.ilean/.trace byte counts and hashes
for every verified module. Supporting dependency artifacts remain in the same
isolated .lake tree, with QIC at the exact pin. These files are local to this executor.

No cache payload was exported. Available repository tooling does not establish a
usable official cross-executor export route: ci_compatible_cache.py explicitly
never saves caches; seed_lake_build.sh requires same-machine macOS/APFS and other
input checks, which this Linux environment does not satisfy. Previously reported
export allowlist/baseline-toolchain restrictions have not been retried or bypassed.
No Library upload, Git binary-cache publication, alternative transfer channel, or
manual trace rewrite was attempted. Only audit evidence is pushed to this branch.

Later reuse needs an authorized artifact-transfer route and validation of actual
payload hashes, source, toolchain/package pins and transitive import artifacts,
followed by Lake trace verification. Metadata alone is not a compilation result.
