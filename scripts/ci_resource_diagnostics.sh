#!/usr/bin/env bash
# Source only in the full-build step. No build command runs here.
# No numeric-PID signalling or wait: Bash may reap an early-exiting sampler,
# and its old PID may later belong to an unrelated process.
trap 'exit 130' INT
trap 'exit 143' TERM
_ci_resource_dir=''
if [[ -n "${RUNNER_TEMP:-}" ]]; then
  if _ci_resource_dir="$(mktemp -d "$RUNNER_TEMP/lean-resources.XXXXXXXX")"; then
    # A new mode-0700 directory cannot contain a previous run's output.
    # Publication separately verifies the sampler's closed-file receipt.
    if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
      printf 'resource_directory=%s\n' "$_ci_resource_dir" >> "$GITHUB_OUTPUT" || true
    fi
    python3 "${BASH_SOURCE[0]%/*}/ci_resource_diagnostics.py" sample \
      --output "$_ci_resource_dir/samples.jsonl" --parent-pid "$$" &
    _ci_resource_pid=$!  # For fixtures only; never used to signal a process.
  fi
fi
