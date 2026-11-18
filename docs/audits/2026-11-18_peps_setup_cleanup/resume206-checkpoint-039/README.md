# Live second-resume checkpoint

The existing runner PID 173290 / session 90417 continues without restart.
This immutable snapshot includes only files with completed successful build
and strict commands. The current in-flight target is excluded. Exact passed
and remaining sets partition the original 206; prior 385 passes are retained.
All sources and the QIC pin remain at production snapshot a28. Shared fa9 adds
only two separately validated MPS simp fixes; this old-tree queue is not a claim
of independent validation of those changes. No #10905 592a delta is integrated.

Recovery: read /tmp/10881-peps-resume206/ledger.json, current.json and run.log,
and check PID 173290 before interacting with session 90417. Never start a second
queue while alive. The 1 GiB guard remains in place. The runner checks the full
591-file union before its separately recorded root TNLean.PEPS validation.
Earlier cleanup manifests, hashes and all intermediate checkpoints are retained.
