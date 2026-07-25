#!/usr/bin/env bash
# Lightweight integration test for seed_lake_build.sh.
set -euo pipefail

SCRIPT_SOURCE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
TEST_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/tnlean-lake-seed-test.XXXXXX")"

cleanup() {
  find "$TEST_ROOT" -depth -delete
}
trap cleanup EXIT

REPO="$TEST_ROOT/repo"
TARGET="$TEST_ROOT/target"
mkdir -p "$REPO/scripts"
cp "$SCRIPT_SOURCE/seed_lake_build.sh" "$REPO/scripts/seed_lake_build.sh"
printf 'leanprover/lean4:v4.32.0\n' >"$REPO/lean-toolchain"
printf '{}\n' >"$REPO/lake-manifest.json"
printf 'name = "LakeSeedTest"\n' >"$REPO/lakefile.toml"
printf '/.lake/\n' >"$REPO/.gitignore"
git -C "$REPO" init -q
git -C "$REPO" add .
git -C "$REPO" \
  -c user.name=Test \
  -c user.email=test@example.com \
  commit -qm "Initialize test repository"
git -C "$REPO" worktree add --detach -q "$TARGET" HEAD

mkdir -p "$REPO/.lake/build" "$REPO/.lake/packages"
printf 'compiled\n' >"$REPO/.lake/build/example.olean"
printf 'dependency\n' >"$REPO/.lake/packages/example"

"$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run >/dev/null
"$REPO/scripts/seed_lake_build.sh" "$TARGET" >/dev/null
test -f "$TARGET/.lake/build/example.olean"
test -f "$TARGET/.lake/packages/example"
test ! -L "$TARGET/.lake"

if "$REPO/scripts/seed_lake_build.sh" "$TARGET" 2>"$TEST_ROOT/error.log"; then
  echo "second seed unexpectedly succeeded" >&2
  exit 1
fi
rg -q "target already has .lake" "$TEST_ROOT/error.log"

echo "Lake build seed integration test passed"
