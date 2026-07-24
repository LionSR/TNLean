#!/usr/bin/env bash
# tenkz_pixelpair.sh -- same-session paired pixel sweep.
#
# Renders the standalone corpus at TWO worktree states (a base commit-ish and
# the current tree), rasterizes every page at 300 dpi, and byte-compares the
# pairs.  Pixel parity is only ever judged this way: both sides render in one
# session on one machine, because raster bytes are environment-epoch
# sensitive and stored manifests go stale invisibly.
#
# Usage: scripts/tenkz_pixelpair.sh <base-commit-ish>
# Env:   TENKZ_CORPUS_JOBS  parallel compiles (default 8, positive integer)
#
# The base package must support the public syntax used by the renderer-only
# manifest at tests/tenkz/pixelpair-sources.txt.  Comparing against a ref older
# than that syntax fails during compilation rather than reporting a pixel diff;
# use a manifest whose fixtures are compatible with both package revisions.
set -euo pipefail

SCRIPT_DIR="$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(CDPATH='' cd -- "$SCRIPT_DIR/.." && pwd)"
BASE_REF="${1:?usage: tenkz_pixelpair.sh <base-commit-ish>}"
PAIR_MANIFEST="$REPO/tests/tenkz/pixelpair-sources.txt"
JOBS=${TENKZ_CORPUS_JOBS:-8}
if [[ ! "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "FAIL: TENKZ_CORPUS_JOBS must be a positive integer, got '$JOBS'" >&2
  exit 1
fi
for command in timeout xelatex pdftoppm; do
  command -v "$command" >/dev/null \
    || { echo "FAIL: $command not found" >&2; exit 1; }
done
[[ -s "$PAIR_MANIFEST" ]] \
  || { echo "FAIL: missing pixelpair source manifest" >&2; exit 1; }

WORK="$(mktemp -d "${TMPDIR:-/tmp}/tenkz-pixelpair-XXXXXX")"
BASE_TREE="$WORK/base-tree"
trap 'rm -rf "$WORK"' EXIT

# Detached true-legacy build: a clean worktree at the base ref, never a file
# copy inside the live tree (a stash guards only what it happens to catch).
git -C "$REPO" worktree add --detach --quiet "$BASE_TREE" "$BASE_REF"
cleanup_worktree() { git -C "$REPO" worktree remove --force "$BASE_TREE" 2>/dev/null || true; }
trap 'cleanup_worktree; rm -rf "$WORK"' EXIT

render_side() { # $1 package tree root, $2 output dir
  local root="$1" out="$2" src stem
  mkdir -p "$out/pdf" "$out/png" "$out/src"
  # Both package trees consume the same current renderer-only fixtures.  Keep
  # model-validation probes out: their assertions can require fields an older
  # package does not yet expose, obscuring the pixel comparison.
  while IFS= read -r src; do
    [[ -z "$src" || "$src" == \#* ]] && continue
    [[ "$src" == *.tex && "$src" != */* ]] \
      || { echo "FAIL: invalid pixelpair source '$src'" >&2; exit 1; }
    [[ -f "$REPO/tests/tenkz/$src" ]] \
      || { echo "FAIL: missing pixelpair source '$src'" >&2; exit 1; }
    cp "$REPO/tests/tenkz/$src" "$out/src/$src"
  done <"$PAIR_MANIFEST"
  ( CDPATH='' cd -- "$out/src"
    find . -maxdepth 1 -name '*.tex' -print0 | LC_ALL=C sort -z >sources.list
    [[ -s sources.list ]] \
      || { echo "FAIL: standalone corpus contains no .tex sources" >&2; exit 1; }
    compile_one() {
      # $1 = tree root (fixed arg), $2 = source path (appended by xargs)
      local name; name="$(basename "$2")"
      ( TEXINPUTS="$1/tex/tenkz//:$1/tex//:" timeout 180 \
          xelatex -interaction=nonstopmode -halt-on-error "$name" ) \
        >"${name%.tex}.pixelpair-transcript" 2>&1 \
        || { echo "FAIL: $name did not compile" >&2; return 1; }
    }
    export -f compile_one
    xargs -0 -n 1 -P "$JOBS" bash -c 'compile_one "$1" "$2"' _ "$root" <sources.list
    while IFS= read -r -d '' src; do
      stem="$(basename "${src%.tex}")"
      [[ -f "$stem.pdf" ]] || { echo "FAIL: $stem produced no pdf" >&2; exit 1; }
      mv "$stem.pdf" "../pdf/$stem.pdf"
      pdftoppm -r 300 -png "../pdf/$stem.pdf" "../png/$stem"
    done <sources.list
  )
}

echo "[pixelpair] rendering base ($BASE_REF)..."
render_side "$BASE_TREE" "$WORK/base"
echo "[pixelpair] rendering current tree..."
render_side "$REPO" "$WORK/head"

fail=0; pages=0
while IFS= read -r png; do
  rel="${png#"$WORK"/head/png/}"
  pages=$((pages + 1))
  if [[ ! -f "$WORK/base/png/$rel" ]]; then
    echo "DIFF: $rel exists only on head" >&2; fail=1; continue
  fi
  cmp -s "$png" "$WORK/base/png/$rel" || { echo "DIFF: $rel" >&2; fail=1; }
done < <(find "$WORK/head/png" -name '*.png' | LC_ALL=C sort)
while IFS= read -r png; do
  rel="${png#"$WORK"/base/png/}"
  [[ -f "$WORK/head/png/$rel" ]] || { echo "DIFF: $rel exists only on base" >&2; fail=1; }
done < <(find "$WORK/base/png" -name '*.png' | LC_ALL=C sort)

if [[ "$fail" -ne 0 ]]; then
  echo "FAIL: pixel divergence against $BASE_REF" >&2
  exit 1
fi
if [[ "$pages" -eq 0 ]]; then
  echo "FAIL: pixel sweep produced no pages" >&2
  exit 1
fi
echo "PASS: $pages pages byte-identical at 300 dpi against $BASE_REF"
