#!/usr/bin/env bash
# Compile the string-engine probe fixtures and compare their event streams and
# rendered pixels against the pinned baseline.  Self-contained: the package and
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
command -v pdftoppm >/dev/null \
  || { echo "FAIL: pdftoppm is required for string pixel probes" >&2; exit 1; }
cp "$FIXDIR"/zz_string_*.tex "$FIXDIR"/xx_string_*.tex "$WORK/"
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
    pdftoppm -singlefile -r 144 -png "$stem.pdf" "$stem" >/dev/null 2>&1
    for artifact in "$stem.tnlog" "$stem.png"; do
      python3 - "$artifact" <<'PY'
import hashlib
import sys

path = sys.argv[1]
print(hashlib.sha256(open(path, "rb").read()).hexdigest(), "", path)
PY
    done
  done | LC_ALL=C sort -k2
) >"$CURRENT"

for src in "$WORK"/xx_string_*.tex; do
  stem="${src%.tex}"
  case "${src##*/}" in
    xx_string_adjacent_extra.tex) expected='[TKZ-CROSS-UNDECLARED]' ;;
    xx_string_duplicate_selector.tex) expected='[TKZ-CROSS-SELECTOR]' ;;
    xx_string_invalid_selector.tex) expected='[TKZ-CROSS-SELECTOR]' ;;
    xx_string_not_found.tex) expected='[TKZ-CROSS-NOT-FOUND]' ;;
    xx_string_join_interior.tex) expected='[TKZ-JOIN-NOT-ENDPOINT]' ;;
    xx_string_multiple_pair.tex) expected='[TKZ-CROSS-MULTIPLE]' ;;
    xx_string_single_curve_undeclared.tex) expected='[TKZ-CROSS-UNDECLARED]' ;;
    xx_string_self_undeclared.tex) expected='[TKZ-CROSS-UNDECLARED]' ;;
    xx_string_undeclared.tex) expected='[TKZ-CROSS-UNDECLARED]' ;;
    *) echo "FAIL: no expected diagnostic for ${src##*/}" >&2; exit 1 ;;
  esac
  if timeout 120 env TEXINPUTS="$REPO/tex/tenkz:" \
      xelatex -output-directory="$WORK" -interaction=nonstopmode \
      -halt-on-error "$src" >"$stem.transcript" 2>&1; then
    echo "FAIL: ${src##*/} unexpectedly compiled" >&2
    exit 1
  fi
  if ! grep -Fq "$expected" "$stem.transcript"; then
    echo "FAIL: ${src##*/} did not emit $expected" >&2
    exit 1
  fi
done

count=$(wc -l <"$CURRENT" | tr -d ' ')
if [[ "$MODE" == snapshot ]]; then
  cp "$CURRENT" "$GOLDEN"
  echo "PASS: froze $count string-probe event and pixel artifacts"
  exit 0
fi
if diff -u "$GOLDEN" "$CURRENT"; then
  echo "PASS: $count string-probe event and pixel artifacts byte-identical"
else
  echo "FAIL: string-probe event or pixel artifacts diverged" >&2
  exit 1
fi
