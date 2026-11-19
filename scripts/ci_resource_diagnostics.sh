#!/usr/bin/env bash
# Source only in the full-build step. No build command runs here.
# Never signal or wait on a stored numeric PID: Bash may already have reaped it.
# All optional filesystem initialization runs in the background watchdog process.
trap 'exit 130' INT
trap 'exit 143' TERM
if [[ -n "${RUNNER_TEMP:-}" && -n "${GITHUB_OUTPUT:-}" ]]; then
  python3 "${BASH_SOURCE[0]%/*}/ci_resource_diagnostics.py" sample \
    --temp-root "$RUNNER_TEMP" --github-output "$GITHUB_OUTPUT" --parent-pid "$$" &
  _ci_resource_pid=$!  # For fixtures only; never used to signal a process.
fi
