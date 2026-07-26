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

validate_packages() {
  local source_root="$1"
  local package_name
  local expected_rev
  local package_root
  local actual_rev
  PACKAGE_LIST_FILE="$(mktemp "${TMPDIR:-/tmp}/tnlean-lake-packages.XXXXXX")" ||
    die "cannot create temporary package list"
  if ! python3 - "$source_root/lake-manifest.json" >"$PACKAGE_LIST_FILE" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as manifest_file:
    manifest = json.load(manifest_file)
for package in manifest.get("packages", []):
    if package.get("type") == "git":
        print(f"{package['name']}\t{package['rev']}")
PY
  then
    die "cannot parse Git packages from lake-manifest.json"
  fi
  while IFS=$'\t' read -r package_name expected_rev; do
    package_root="$source_root/.lake/packages/$package_name"
    test -d "$package_root" && test ! -L "$package_root" ||
      die "Git package is missing or symlinked: $package_name"
    actual_rev="$(git -C "$package_root" rev-parse HEAD 2>/dev/null)" ||
      die "Git package is not a checkout: $package_name"
    test "$actual_rev" = "$expected_rev" ||
      die "Git package revision differs from lake-manifest.json: $package_name"
    test -z "$(git -C "$package_root" status --porcelain --untracked-files=all)" ||
      die "Git package has local changes: $package_name"
  done <"$PACKAGE_LIST_FILE"
  find "$PACKAGE_LIST_FILE" -delete
  PACKAGE_LIST_FILE=""
}

cleanup() {
  if test -n "${PACKAGE_LIST_FILE:-}" && test -f "$PACKAGE_LIST_FILE"; then
    find "$PACKAGE_LIST_FILE" -delete
  fi
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
PACKAGE_LIST_FILE=""
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
test ! -L "$SOURCE_ROOT/.lake" || die "source .lake must not be a symlink"
test -d "$SOURCE_ROOT/.lake/build" && test ! -L "$SOURCE_ROOT/.lake/build" ||
  die "source has no regular .lake/build"
test -d "$SOURCE_ROOT/.lake/packages" && test ! -L "$SOURCE_ROOT/.lake/packages" ||
  die "source has no regular .lake/packages"
test ! -e "$TARGET_ROOT/.lake" && test ! -L "$TARGET_ROOT/.lake" ||
  die "target already has .lake"

for input in lean-toolchain lake-manifest.json lakefile.toml; do
  cmp -s "$SOURCE_ROOT/$input" "$TARGET_ROOT/$input" ||
    die "build input differs between source and target: $input"
done
validate_packages "$SOURCE_ROOT"

if test "$DRY_RUN" = "true"; then
  echo "seed-lake-build: dry-run passed"
  echo "seed-lake-build: source: $SOURCE_ROOT/.lake"
  echo "seed-lake-build: target: $TARGET_ROOT/.lake"
  exit 0
fi

STAGING_DIR="$TARGET_ROOT/.lake"
mkdir "$STAGING_DIR" 2>/dev/null || die "target already has .lake"
/bin/cp -cR "$SOURCE_ROOT/.lake/." "$STAGING_DIR"
STAGING_DIR=""
echo "seed-lake-build: cloned $SOURCE_ROOT/.lake into $TARGET_ROOT/.lake"
