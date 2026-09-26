#!/usr/bin/env bash
# Check that every blueprint source is formatted to blueprint/latexindent.yaml.
#
# latexindent's -k mode remains nondeterministic on GitHub runners even at the
# pinned version (LionSR/TNLean#6878), so each file is formatted as a
# temporary copy with the stable -w mode and compared byte for byte; the
# sources are never touched. Files are independent, so several are checked
# at once (JOBS, default 4).
#
# Usage: scripts/check_latexindent_formatting.sh
#        scripts/check_latexindent_formatting.sh --one FILE   (internal)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

if [[ "${1:-}" == "--one" ]]; then
  f="$2"
  candidate_dir="$(mktemp -d "$CHECK_TMPDIR/XXXXXX")"
  candidate="$candidate_dir/$(basename "$f")"
  cp -- "$f" "$candidate"
  scripts/latexindent -w -s -l blueprint/latexindent.yaml "$candidate" > /dev/null
  if ! cmp -s -- "$f" "$candidate"; then
    echo "::warning file=$f::not formatted to blueprint/latexindent.yaml; run 'scripts/latexindent -l blueprint/latexindent.yaml -w -s \"$f\"' locally to fix"
    exit 1
  fi
  exit 0
fi

# The first call downloads and unpacks the packed executable; the concurrent
# calls below then reuse the unpacked copy instead of racing to create it.
scripts/latexindent --version

CHECK_TMPDIR="$(mktemp -d)"
export CHECK_TMPDIR
trap 'rm -rf "$CHECK_TMPDIR"' EXIT

# xargs exits nonzero when any file differs.
find blueprint/src -name '*.tex' -not -path '*/Packages/*' -print0 \
  | xargs -0 -P "${JOBS:-4}" -n 1 "$0" --one
