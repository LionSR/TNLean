#!/usr/bin/env bash
# APFS-clone an existing TNLean .lake into a fresh worktree.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/seed_lake_build.sh TARGET_WORKTREE [SOURCE_WORKTREE] [--dry-run]

SOURCE_WORKTREE defaults to the repository's primary worktree. The target must
belong to the same repository and must not already contain .lake.
EOF
}

die() {
  echo "seed-lake-build: $*" >&2
  exit 1
}

canonical_dir() {
  (CDPATH='' cd -- "$1" && pwd -P)
}

worktree_root() {
  git -C "$1" rev-parse --show-toplevel 2>/dev/null
}

common_dir() {
  local root="$1"
  canonical_dir "$(git -C "$root" rev-parse --path-format=absolute --git-common-dir)"
}

validate_root() {
  local path="$1"
  local root
  test -d "$path" || die "not a directory: $path"
  root="$(worktree_root "$path")" || die "not a Git worktree: $path"
  test "$(canonical_dir "$path")" = "$(canonical_dir "$root")" ||
    die "path must name the worktree root: $path"
  test "$(common_dir "$root")" = "$REPO_COMMON_DIR" ||
    die "worktree belongs to a different repository: $path"
}

cleanup() {
  if test -n "${STAGING_DIR:-}" && test -d "$STAGING_DIR"; then
    find "$STAGING_DIR" -depth -delete
  fi
}
trap cleanup EXIT

SCRIPT_DIR="$(canonical_dir "$(dirname "${BASH_SOURCE[0]}")")"
SCRIPT_ROOT="$(worktree_root "$SCRIPT_DIR")"
REPO_COMMON_DIR="$(common_dir "$SCRIPT_ROOT")"
PRIMARY_ROOT="$(
  git -C "$SCRIPT_ROOT" worktree list --porcelain |
    sed -n 's/^worktree //p' |
    head -n 1
)"
STAGING_DIR=""
DRY_RUN="false"

test "$#" -ge 1 || {
  usage
  exit 2
}

TARGET_PATH="$1"
shift
SOURCE_PATH="$PRIMARY_ROOT"
if test "$#" -gt 0 && test "$1" != "--dry-run"; then
  SOURCE_PATH="$1"
  shift
fi
if test "$#" -gt 0 && test "$1" = "--dry-run"; then
  DRY_RUN="true"
  shift
fi
test "$#" -eq 0 || die "unknown argument: $1"

validate_root "$SOURCE_PATH"
validate_root "$TARGET_PATH"
SOURCE_ROOT="$(canonical_dir "$SOURCE_PATH")"
TARGET_ROOT="$(canonical_dir "$TARGET_PATH")"
test "$SOURCE_ROOT" != "$TARGET_ROOT" || die "source and target worktrees must differ"
test -d "$SOURCE_ROOT/.lake/build" || die "source has no .lake/build"
test -d "$SOURCE_ROOT/.lake/packages" || die "source has no .lake/packages"
test ! -e "$TARGET_ROOT/.lake" && test ! -L "$TARGET_ROOT/.lake" ||
  die "target already has .lake"

for input in lean-toolchain lake-manifest.json lakefile.toml; do
  cmp -s "$SOURCE_ROOT/$input" "$TARGET_ROOT/$input" ||
    die "build input differs between source and target: $input"
done

if test "$DRY_RUN" = "true"; then
  echo "seed-lake-build: dry-run passed"
  echo "seed-lake-build: source: $SOURCE_ROOT/.lake"
  echo "seed-lake-build: target: $TARGET_ROOT/.lake"
  exit 0
fi

STAGING_DIR="$TARGET_ROOT/.lake.seed.$$"
/bin/cp -cR "$SOURCE_ROOT/.lake" "$STAGING_DIR"
mv "$STAGING_DIR" "$TARGET_ROOT/.lake"
STAGING_DIR=""
echo "seed-lake-build: cloned $SOURCE_ROOT/.lake into $TARGET_ROOT/.lake"
