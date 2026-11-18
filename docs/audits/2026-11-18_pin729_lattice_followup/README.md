# Lattice narrow completion and QCA dependency plan

Production source remains 6b7fb2e27dbc6856091e593e4226d350403beb8a;
QIC remains 729428582b78ab7529b3796099193649f947354a.
All 9 allowlisted Lake builds passed, followed by TNLean.Lattice strict.
The original 600-second timeout and previous 209 passes are unchanged evidence
in the adjacent other_validation directory. This adds one manifest target pass:
210/213; MPS, PEPS and QCA roots remain unverified here.

run.py uses an exclusive worktree lock, explicit cwd, captured PID/PGID and
start_new_session. It polls free disk, stops below 1 GiB, terminates only its
own process group on timeout and reaps the child. No /proc cwd lookup is used.
All jobs finished; production edits and repeated previous targets are zero.

qca-missing159.json contains every absent dependency, source hash, transitive
missing dependencies and comparison with MPS evidence commit
9630ab7e415a462145031d973eda757ffbdafcc6. qca-plan.json gives topological batches.
None of these proposed QCA batches was executed. The 98 MPS entries are reserved
for coordination: 17 have matching-source compiled artifact metadata in that
snapshot, while none is in its direct target manifest. These are direct Lean
artifacts, not proven Lake cache hits. The /tmp export cache is absent here.
No artifact transfer, bypass of export restrictions, or cache-overlay occurred.
The unique non-MPS optional batch list also defers existing shared compile work
(ListOfFn) and consumers needing that unavailable artifact.

A later authorized cache import must check actual payload hashes, exact source,
toolchain/package pins and transitive imported artifacts, and let Lake verify
its own traces. Metadata alone does not justify reuse. Do not cold-build QCA root.
