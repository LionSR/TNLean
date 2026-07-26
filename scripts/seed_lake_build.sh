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

test "$(/usr/bin/uname -s)" = "Darwin" ||
  die "requires macOS with APFS clone support"

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
  local package_status
  local metadata_link
  local reported_root
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
    test -d "$package_root/.git" && test ! -L "$package_root/.git" ||
      die "Git package metadata is not self-contained: $package_name"
    test ! -e "$package_root/.git/commondir" &&
      test ! -L "$package_root/.git/commondir" ||
      die "Git package uses external common metadata: $package_name"
    test ! -e "$package_root/.git/objects/info/alternates" &&
      test ! -L "$package_root/.git/objects/info/alternates" ||
      die "Git package uses external object storage: $package_name"
    metadata_link="$(
      find "$package_root/.git" -type l -print -quit
    )"
    test -z "$metadata_link" ||
      die "Git package metadata contains a symlink: $package_name"
    reported_root="$(git -C "$package_root" rev-parse --show-toplevel 2>/dev/null)" ||
      die "Git package is not a checkout: $package_name"
    test "$(canonical_dir "$reported_root")" = "$(canonical_dir "$package_root")" ||
      die "Git package worktree points outside its package root: $package_name"
    actual_rev="$(git -C "$package_root" rev-parse HEAD 2>/dev/null)" ||
      die "Git package is not a checkout: $package_name"
    test "$actual_rev" = "$expected_rev" ||
      die "Git package revision differs from lake-manifest.json: $package_name"
    if ! package_status="$(
      git -C "$package_root" status --porcelain --untracked-files=all
    )"; then
      die "cannot read Git package status: $package_name"
    fi
    test -z "$package_status" ||
      die "Git package has local changes: $package_name"
  done <"$PACKAGE_LIST_FILE"
  find "$PACKAGE_LIST_FILE" -delete
  PACKAGE_LIST_FILE=""
}

cleanup() {
  if test -n "${PACKAGE_LIST_FILE:-}" && test -f "$PACKAGE_LIST_FILE"; then
    find "$PACKAGE_LIST_FILE" -delete
  fi
  if test -n "${RESERVATION_DIR:-}" && test -d "$RESERVATION_DIR"; then
    reservation_inode="$(stat -f %i "$RESERVATION_DIR" 2>/dev/null || true)"
    if test -n "$reservation_inode" &&
      test "$reservation_inode" = "${RESERVATION_INODE:-}"; then
      chmod 700 "$RESERVATION_DIR"
      find "$RESERVATION_DIR" -depth -delete
    fi
  fi
  if test -n "${STAGING_DIR:-}" && test -d "$STAGING_DIR"; then
    staging_inode="$(stat -f %i "$STAGING_DIR" 2>/dev/null || true)"
    if test -n "$staging_inode" &&
      test "$staging_inode" = "${STAGING_INODE:-}"; then
      find "$STAGING_DIR" -depth -delete
    fi
  fi
}
trap cleanup EXIT

SCRIPT_DIR="$(canonical_dir "$(dirname "${BASH_SOURCE[0]}")")"
SCRIPT_ROOT="$(worktree_root "$SCRIPT_DIR")"
REPO_COMMON_DIR="$(common_dir "$SCRIPT_ROOT")"
WORKTREE_LIST="$(git -C "$SCRIPT_ROOT" worktree list --porcelain)"
PRIMARY_ROOT="$(
  sed -n '/^worktree / { s/^worktree //; p; q; }' <<<"$WORKTREE_LIST"
)"
STAGING_DIR=""
STAGING_INODE=""
PACKAGE_LIST_FILE=""
RESERVATION_DIR=""
RESERVATION_INODE=""
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
SOURCE_REV="$(git -C "$SOURCE_ROOT" rev-parse HEAD)" ||
  die "cannot read source revision"
TARGET_REV="$(git -C "$TARGET_ROOT" rev-parse HEAD)" ||
  die "cannot read target revision"
REUSE_TNLEAN_BUILD="false"
if test "$SOURCE_REV" = "$TARGET_REV"; then
  REUSE_TNLEAN_BUILD="true"
fi
test ! -L "$SOURCE_ROOT/.lake" || die "source .lake must not be a symlink"
test -d "$SOURCE_ROOT/.lake/build" && test ! -L "$SOURCE_ROOT/.lake/build" ||
  die "source has no regular .lake/build"
test -d "$SOURCE_ROOT/.lake/packages" && test ! -L "$SOURCE_ROOT/.lake/packages" ||
  die "source has no regular .lake/packages"
NESTED_CACHE_LINK="$(
  find "$SOURCE_ROOT/.lake" -type l \
    \( -name .lake -o -name build -o -name packages \
      -o -path '*/.lake/build/*' -o -path '*/.lake/lakefile.*' \) \
    -print -quit
)"
test -z "$NESTED_CACHE_LINK" ||
  die "source contains a symlinked Lake cache directory: $NESTED_CACHE_LINK"
test ! -e "$TARGET_ROOT/.lake" && test ! -L "$TARGET_ROOT/.lake" ||
  die "target already has .lake"

for input in lean-toolchain lake-manifest.json lakefile.toml; do
  cmp -s "$SOURCE_ROOT/$input" "$TARGET_ROOT/$input" ||
    die "build input differs between source and target: $input"
done
validate_packages "$SOURCE_ROOT"

if test "$DRY_RUN" = "true"; then
  test -f "$SOURCE_ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ||
    die "source lacks prebuilt Mathlib artifacts"
  echo "seed-lake-build: dry-run passed"
  echo "seed-lake-build: source: $SOURCE_ROOT/.lake"
  echo "seed-lake-build: target: $TARGET_ROOT/.lake"
  if test "$REUSE_TNLEAN_BUILD" = "true"; then
    echo "seed-lake-build: TNLean build artifacts will be reused"
  else
    echo "seed-lake-build: TNLean build artifacts will be omitted (different revisions)"
  fi
  exit 0
fi

(
  cd "$SOURCE_ROOT"
  lake exe cache get
) || die "failed to fetch current prebuilt Mathlib artifacts"
test -f "$SOURCE_ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ||
  die "source lacks prebuilt Mathlib artifacts after 'lake exe cache get'"

RESERVATION_DIR="$TARGET_ROOT/.lake"
mkdir "$RESERVATION_DIR" 2>/dev/null || die "target already has .lake"
RESERVATION_INODE="$(stat -f %i "$RESERVATION_DIR")"
chmod 000 "$RESERVATION_DIR"
STAGING_DIR="$(/usr/bin/mktemp -d "$TARGET_ROOT/.lake.seed.XXXXXX")"
STAGING_INODE="$(stat -f %i "$STAGING_DIR")"
if test "$REUSE_TNLEAN_BUILD" = "true"; then
  /bin/cp -cR "$SOURCE_ROOT/.lake/." "$STAGING_DIR"
else
  /bin/cp -cR "$SOURCE_ROOT/.lake/packages" "$STAGING_DIR/packages"
fi
test "$(stat -f %i "$STAGING_DIR")" = "$STAGING_INODE" ||
  die "staging directory changed during clone"
python3 - "$STAGING_DIR" "$RESERVATION_DIR" <<'PY'
import ctypes
import os
import sys

libc = ctypes.CDLL(None, use_errno=True)
renameatx_np = libc.renameatx_np
renameatx_np.argtypes = [
    ctypes.c_int,
    ctypes.c_char_p,
    ctypes.c_int,
    ctypes.c_char_p,
    ctypes.c_uint,
]
renameatx_np.restype = ctypes.c_int
result = renameatx_np(
    -2,
    os.fsencode(sys.argv[1]),
    -2,
    os.fsencode(sys.argv[2]),
    0x00000002,
)
if result != 0:
    error = ctypes.get_errno()
    raise OSError(error, os.strerror(error))
PY
STAGING_INODE="$RESERVATION_INODE"
RESERVATION_DIR=""
RESERVATION_INODE=""
chmod 700 "$STAGING_DIR"
find "$STAGING_DIR" -depth -delete
STAGING_DIR=""
STAGING_INODE=""
if test "$REUSE_TNLEAN_BUILD" = "true"; then
  echo "seed-lake-build: cloned $SOURCE_ROOT/.lake into $TARGET_ROOT/.lake"
else
  echo "seed-lake-build: cloned dependency packages into $TARGET_ROOT/.lake"
  echo "seed-lake-build: omitted TNLean build artifacts from different source revision"
fi
