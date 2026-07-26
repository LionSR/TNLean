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
mkdir "$REPO/.lake/packages/example"
git -C "$REPO/.lake/packages/example" init -q
printf 'dependency\n' >"$REPO/.lake/packages/example/tracked"
git -C "$REPO/.lake/packages/example" add tracked
git -C "$REPO/.lake/packages/example" \
  -c user.name=Test \
  -c user.email=test@example.com \
  commit -qm "Initialize dependency"
DEPENDENCY_REV="$(git -C "$REPO/.lake/packages/example" rev-parse HEAD)"
printf '{"packages":[{"name":"example","type":"git","rev":"%s"}]}\n' \
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

printf '{\n' >"$REPO/lake-manifest.json"
printf '{\n' >"$TARGET/lake-manifest.json"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "invalid manifest unexpectedly passed" >&2
  exit 1
fi
rg -q "cannot parse Git packages from lake-manifest.json" "$TEST_ROOT/error.log"
printf '{"packages":[{"name":"example","type":"git","rev":"%s"}]}\n' \
  "$DEPENDENCY_REV" >"$REPO/lake-manifest.json"
cp "$REPO/lake-manifest.json" "$TARGET/lake-manifest.json"

printf 'modified\n' >>"$REPO/.lake/packages/example/tracked"
if "$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run 2>"$TEST_ROOT/error.log"; then
  echo "modified dependency unexpectedly passed" >&2
  exit 1
fi
rg -q "Git package has local changes: example" "$TEST_ROOT/error.log"
printf 'dependency\n' >"$REPO/.lake/packages/example/tracked"

(
  cd "$REPO"
  CDPATH="$TEST_ROOT" scripts/seed_lake_build.sh "$TARGET" --dry-run >/dev/null
)
"$REPO/scripts/seed_lake_build.sh" "$TARGET" --dry-run >/dev/null
PATH="$TEST_ROOT/bin:$PATH" "$REPO/scripts/seed_lake_build.sh" "$TARGET" >/dev/null
test -f "$TARGET/.lake/build/example.olean"
test -f "$TARGET/.lake/packages/example/tracked"
test ! -L "$TARGET/.lake"

if "$REPO/scripts/seed_lake_build.sh" "$TARGET" 2>"$TEST_ROOT/error.log"; then
  echo "second seed unexpectedly succeeded" >&2
  exit 1
fi
rg -q "target already has .lake" "$TEST_ROOT/error.log"

echo "Lake build seed integration test passed"
