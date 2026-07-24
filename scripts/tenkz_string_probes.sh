#!/usr/bin/env bash
# Compile the string-engine probe fixtures and compare their event streams
# against the pinned baseline.  Self-contained: the shipping package and the
# main golden gate are untouched until the engine integrates at the wave-2
# landing.  Usage: tenkz_string_probes.sh [--snapshot]
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXDIR="$REPO/tests/tenkz/strings"
GOLDEN="$FIXDIR/golden.sha256"
MODE=check
[[ "${1:-}" == "--snapshot" ]] && MODE=snapshot
WORK="$(mktemp -d "${TMPDIR:-/tmp}/tenkz-strings.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
cp "$FIXDIR"/zz_string_*.tex "$WORK/"
CURRENT="$WORK/current.sha256"
(
  cd "$WORK"
  for src in zz_string_*.tex; do
    stem="${src%.tex}"
    if ! timeout 120 env TEXINPUTS="$REPO/tex/tenkz:" \
        xelatex -interaction=nonstopmode -halt-on-error "$src" \
        >"$stem.transcript" 2>&1; then
      echo "FAIL: $src did not compile" >&2
      exit 1
    fi
    if [[ ! -f "$stem.tnlog" ]]; then
      echo "FAIL: $stem compiled without emitting $stem.tnlog" >&2
      exit 1
    fi
    python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest(), "", sys.argv[1])' "$stem.tnlog"
  done | LC_ALL=C sort -k2
) >"$CURRENT"
count=$(wc -l <"$CURRENT" | tr -d ' ')
if [[ "$MODE" == snapshot ]]; then
  cp "$CURRENT" "$GOLDEN"
  echo "PASS: froze $count string-probe event streams"
  exit 0
fi
if diff -u "$GOLDEN" "$CURRENT"; then
  echo "PASS: $count string-probe event streams byte-identical"
else
  echo "FAIL: string-probe event streams diverged" >&2
  exit 1
fi
