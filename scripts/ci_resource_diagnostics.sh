#!/usr/bin/env bash
# Source only in the full-build step's shell. No build command runs here.
# Preserve both the original pipeline result and cancellation as non-success.
_ci_resource_cleanup() {
  local status="$1" attempt
  trap - EXIT
  if [[ -n "${_ci_resource_pid:-}" ]]; then
    kill -TERM "$_ci_resource_pid" 2>/dev/null || true
    # A stuck diagnostic write must not hold up the build's original status.
    for attempt in {1..20}; do
      kill -0 "$_ci_resource_pid" 2>/dev/null || break
      sleep 0.1 || break
    done
    kill -KILL "$_ci_resource_pid" 2>/dev/null || true
    wait "$_ci_resource_pid" 2>/dev/null || true
  fi
  exit "$status"
}
trap '_ci_resource_cleanup $?' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
python3 "${BASH_SOURCE[0]%/*}/ci_resource_diagnostics.py" \
  --output "$1" --parent-pid "$$" &
_ci_resource_pid=$!
