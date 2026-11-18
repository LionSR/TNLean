# Generated module-setup cleanup and bounded resume

At production snapshot a28f35a6b (audit HEAD bb3d77494), no active Lean/Lake
process remained; all observed Lean PIDs were zombies. Only generated setup.json
files inside this task's TN and QIC build/ir directories were removed.
Lake v4.36.0-rc1 Module.recFetchSetup recomputes this setup; compileLeanModule
in Lake/Build/Actions.lean lines 66–68 writes the setup JSON before compilation.

1328 files, totaling 2918008494 bytes, were removed. Filesystem free space
increased from 1056477184 to 3977166848 bytes. All 6623 protected olean/ilean
and hash files were rehashed after cleanup and matched their recorded hashes.
Sources, Git data, logs, traces, C output and other artifacts were retained.
The archive records exact removed paths, sizes, hashes, and protected hashes.

Only the exact 467 remaining modules from the prior threshold evidence resume,
in original dependency order; the 124 passed manifest entries are excluded.
Honeycomb is an additional prior pass outside that manifest. Each target runs
build then strict, with a 1 GiB guard before the next target and a checkpoint
every 25 targets. No full-library or duplicate queue was launched. The first
resumed owner is TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport. The running ledger
is /tmp/10881-peps-resume/ledger.json; session 71491, runner PID 113318.
This cleanup evidence alone is not a claim that the remaining targets pass.
