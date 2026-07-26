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
mkdir "$REPO/.lake/packages/mathlib"
git -C "$REPO/.lake/packages/mathlib" init -q
printf '/.lake/\n' >"$REPO/.lake/packages/mathlib/.gitignore"
printf 'dependency\n' >"$REPO/.lake/packages/mathlib/tracked"
git -C "$REPO/.lake/packages/mathlib" add .gitignore tracked
git -C "$REPO/.lake/packages/mathlib" \
  -c user.name=Test \
  -c user.email=test@example.com \
  commit -qm "Initialize dependency"
DEPENDENCY_REV="$(git -C "$REPO/.lake/packages/mathlib" rev-parse HEAD)"
mkdir -p "$REPO/.lake/packages/mathlib/.lake/build/lib/lean"
printf 'prebuilt\n' >"$REPO/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
printf '{"packages":[{"name":"mathlib","type":"git","rev":"%s"}]}\n' \
  "$DEPENDENCY_REV" >"$REPO/lake-manifest.json"
cp "$REPO/lake-manifest.json" "$TARGET/lake-manifest.json"

mkdir -p "$TEST_ROOT/scripts"
mkdir -p "$TEST_ROOT/bin"
cat >"$TEST_ROOT/bin/cp" <<'EOF'
#!/usr/bin/env bash
echo "PATH cp must not be used" >&2
exit 99
EOF
chmod +x "$TEST_ROOT/bin/cp"

mv "$REPO/.lake" "$REPO/.lake.real"
ln -s .lake.real "$REPO/.lake"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "symlinked source cache unexpectedly passed" >&2
  exit 1
fi
rg -q "source .lake must not be a symlink" "$TEST_ROOT/error.log"
unlink "$REPO/.lake"
mv "$REPO/.lake.real" "$REPO/.lake"

for cache_child in build packages; do
  mv "$REPO/.lake/$cache_child" "$REPO/.lake/$cache_child.real"
  ln -s "$cache_child.real" "$REPO/.lake/$cache_child"
  if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
    echo "symlinked source cache child unexpectedly passed: $cache_child" >&2
    exit 1
  fi
  rg -q "source has no regular .lake/$cache_child" "$TEST_ROOT/error.log"
  unlink "$REPO/.lake/$cache_child"
  mv "$REPO/.lake/$cache_child.real" "$REPO/.lake/$cache_child"
done

mv "$REPO/.lake/packages/mathlib/.lake/build" \
  "$REPO/.lake/packages/mathlib/.lake/build.real"
ln -s build.real "$REPO/.lake/packages/mathlib/.lake/build"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "nested symlinked dependency cache unexpectedly passed" >&2
  exit 1
fi
rg -q "source contains a symlinked Lake cache directory" "$TEST_ROOT/error.log"
unlink "$REPO/.lake/packages/mathlib/.lake/build"
mv "$REPO/.lake/packages/mathlib/.lake/build.real" \
  "$REPO/.lake/packages/mathlib/.lake/build"

mv "$REPO/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" \
  "$REPO/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean.missing"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "missing prebuilt Mathlib cache unexpectedly passed" >&2
  exit 1
fi
rg -q "source lacks prebuilt Mathlib artifacts" "$TEST_ROOT/error.log"
mv "$REPO/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean.missing" \
  "$REPO/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"

printf '{\n' >"$REPO/lake-manifest.json"
printf '{\n' >"$TARGET/lake-manifest.json"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "invalid manifest unexpectedly passed" >&2
  exit 1
fi
rg -q "cannot parse Git packages from lake-manifest.json" "$TEST_ROOT/error.log"
printf '{"packages":[{"name":"mathlib","type":"git","rev":"%s"}]}\n' \
  "$DEPENDENCY_REV" >"$REPO/lake-manifest.json"
cp "$REPO/lake-manifest.json" "$TARGET/lake-manifest.json"

printf 'modified\n' >>"$REPO/.lake/packages/mathlib/tracked"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "modified dependency unexpectedly passed" >&2
  exit 1
fi
rg -q "Git package has local changes: mathlib" "$TEST_ROOT/error.log"
printf 'dependency\n' >"$REPO/.lake/packages/mathlib/tracked"

(
  cd "$REPO"
  CDPATH="$TEST_ROOT" scripts/seed_lake_build.sh "$TARGET" --dry-run >/dev/null
)
"$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run >/dev/null
PATH="$TEST_ROOT/bin:$PATH" "$REPO/scripts/seed_lake_build.sh" "$TARGET" >/dev/null
test -f "$TARGET/.lake/build/example.olean"
test -f "$TARGET/.lake/packages/mathlib/tracked"
test -f "$TARGET/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
test ! -L "$TARGET/.lake"

if "$REPO/scripts/seed_lake_build.sh" "$TARGET" 2>"$TEST_ROOT/error.log"; then
  echo "second seed unexpectedly succeeded" >&2
  exit 1
fi
rg -q "target already has .lake" "$TEST_ROOT/error.log"

echo "Lake build seed integration test passed"
