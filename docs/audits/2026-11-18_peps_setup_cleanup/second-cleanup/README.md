# Second generated setup cleanup

At audit HEAD abcc18da, no active Lean, Lake or Python build process remained.
Only 919 generated setup.json files under this task's two TN/QIC build/ir
roots were deleted (2272082245 bytes). The same Lean v4.36.0-rc1 Lake setup
reconstruction verified in the first cleanup applies. The archive records
exact paths, sizes and hashes. All 11216 protected olean/ilean/hash artifacts
were rehashed and unchanged. No sources, Git data, logs or other output removed.
Free bytes increased from 1064132608 to 3338100736.

Runner PID 173290 / session 90417 resumes only the exact 206 remaining files
from resume-checkpoint-261/remaining.txt in original dependency order. Prior
385 successful manifest entries are excluded. Production snapshot remains a28
and QIC pin 729428582; no ef098ad3 changes have been integrated.

The runner retains the 1 GiB target-boundary guard, records every build/strict
command under /tmp/10881-peps-resume206/, and checkpoints each 25 targets.
Only after all 206 pass and an explicit union/disjointness assertion proves
591/591, it may run root TNLean.PEPS build and strict as separate ledger kinds.
No root result is claimed here. No new full-library CI or duplicate queue.

Recovery: inspect PID 173290, ledger.json, current.json and run.log first. Use
session 90417 if available; never restart the full queue while the PID is alive.
If stopped, resolve its recorded reason and subtract successful strict entries
from the original 206 before resuming. Prior checkpoints remain unchanged.
