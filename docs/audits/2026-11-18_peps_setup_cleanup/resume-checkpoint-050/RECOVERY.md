Read /tmp/10881-peps-resume/ledger.json, current.json and run.log first.
Check PID 113318 and session 71491; do not launch a second runner while alive.
Use write_stdin on session 71491 when available. If the session handle is lost,
read the files and process status without restarting. The runner enforces 1 GiB
at target boundaries. If it exits, calculate remaining from the original 467
minus successful strict entries, inspect the last exit reason, then resume only
that remainder after resolving the blocker. Never replay all 467.
All production sources/pin remain a28; audit commits only append evidence.
The earlier cleanup hashes and 124-to-151 checkpoint remain unchanged.
