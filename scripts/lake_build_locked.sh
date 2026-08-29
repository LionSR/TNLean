#!/usr/bin/env bash
# Run a Lake build under the repository's standard macOS file lock.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  scripts/lake_build_locked.sh [LAKE_BUILD_ARGS...]
  scripts/lake_build_locked.sh -- COMMAND [ARGS...]

Without --, fetch the pinned prebuilt cache and run `lake build`. With --, run
the given command under the same repository lock.
EOF
}

canonical_dir() {
  (CDPATH='' cd -- "$1" && pwd -P)
}

worktree_root() {
  git -C "$1" rev-parse --show-toplevel 2>/dev/null
}

if test "${1:-}" = "-h" || test "${1:-}" = "--help"; then
  usage
  exit 0
fi

test "$(/usr/bin/uname -s)" = "Darwin" || {
  echo "lake-build-locked: requires macOS lockf" >&2
  exit 1
}

SCRIPT_DIR="$(canonical_dir "$(dirname "${BASH_SOURCE[0]}")")"
REPO_ROOT="$(worktree_root "$SCRIPT_DIR")" || {
  echo "lake-build-locked: script is not inside a Git worktree" >&2
  exit 1
}
CURRENT_ROOT="$(worktree_root "$PWD")" || {
  echo "lake-build-locked: current directory is not inside a Git worktree" >&2
  exit 1
}
test "$(canonical_dir "$REPO_ROOT")" = "$(canonical_dir "$CURRENT_ROOT")" || {
  echo "lake-build-locked: run this wrapper from its TNLean worktree" >&2
  exit 1
}

if test "${TNLEAN_LAKE_LOCK_HELD:-}" != "1"; then
  COMMON_DIR="$(canonical_dir "$(
    git -C "$REPO_ROOT" rev-parse --path-format=absolute --git-common-dir
  )")"
  # Keep the locked file description in the final Lake process and its children.
  exec 9<>"$COMMON_DIR/tnlean-lake-cache.lock"
  /usr/bin/lockf 9
  export TNLEAN_LAKE_LOCK_HELD=1
fi

if test "${1:-}" = "--"; then
  shift
  test "$#" -gt 0 || {
    echo "lake-build-locked: missing command after --" >&2
    exit 2
  }
  exec "$@"
fi

lake exe cache get
test -f "$REPO_ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" || {
  echo "lake-build-locked: prebuilt Mathlib artifact is unavailable" >&2
  exit 1
}
exec lake build "$@"
