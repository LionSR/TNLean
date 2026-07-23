#!/usr/bin/env bash
# Golden event baselines for the tenkz regression corpus.
#
# snapshot (default): compile every tests/tenkz/*.tex standalone fixture and
# record the SHA-256 of each emitted .tnlog event stream in
# tests/tenkz/golden-events.sha256 (sorted, one "hash  stem.tnlog" line each).
#
# --check: recompile and compare against the stored baseline; exit 1 listing
# every fixture whose event stream changed.  This is the gate for the model
# and renderer rebuild stages: internal refactors must keep every stream
# byte-identical until a reviewed contract change re-baselines.
#
# Renders are deliberately not stored: event streams are the semantic
# contract; pixels are compared per-PR by scripts/tenkz_corpus.sh --render.

set -euo pipefail

REPO=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
CORPUS="$REPO/tests/tenkz"
GOLDEN="$CORPUS/golden-events.sha256"
JOBS=${TENKZ_CORPUS_JOBS:-8}
MODE=snapshot

case "${1:-}" in
  "") ;;
  --check) MODE=check ;;
  -h|--help)
    sed -n '2,14p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  *)
    echo "FAIL: unknown argument: $1" >&2
    exit 2
    ;;
esac

for command in timeout xelatex python3; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "FAIL: tenkz golden baseline requires $command" >&2
    exit 1
  fi
done

WORK=$(mktemp -d "${TMPDIR:-/tmp}/tenkz-golden.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
cp -R "$CORPUS/." "$WORK/"
TEXINPUTS_CORPUS="$REPO/tex/tenkz//:$WORK//:${TEXINPUTS:-}"
export WORK TEXINPUTS_CORPUS

compile_one() {
  local name
  name=${1##*/}
  if ! (
    cd "$WORK"
    timeout 120 env TEXINPUTS="$TEXINPUTS_CORPUS" \
      xelatex -interaction=nonstopmode -halt-on-error "$name"
  ) >"$WORK/${name%.tex}.golden-transcript" 2>&1; then
    echo "FAIL: $name did not compile" >&2
    return 1
  fi
}
export -f compile_one

find "$WORK" -maxdepth 1 -type f -name '*.tex' -print0 \
  | LC_ALL=C sort -z >"$WORK/sources.list"
# shellcheck disable=SC2016
xargs -0 -n 1 -P "$JOBS" bash -c 'compile_one "$1"' _ <"$WORK/sources.list"

CURRENT="$WORK/current.sha256"
(
  cd "$WORK"
  # Every compiled source must have produced its event log: a fixture that
  # compiles but emits no .tnlog would otherwise vanish from the baseline
  # silently (the corpus script guards the same invariant).
  while IFS= read -r -d '' src; do
    stem="$(basename "${src%.tex}")"
    if [[ ! -f "$stem.tnlog" ]]; then
      echo "FAIL: $stem compiled without emitting $stem.tnlog" >&2
      exit 1
    fi
    python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest(), "", sys.argv[1])' "$stem.tnlog"
  done <sources.list | LC_ALL=C sort -k2
) >"$CURRENT"

count=$(wc -l <"$CURRENT" | tr -d ' ')
if [[ "$MODE" == snapshot ]]; then
  cp "$CURRENT" "$GOLDEN"
  echo "PASS: froze $count golden event streams into ${GOLDEN#"$REPO"/}"
  exit 0
fi

if [[ ! -f "$GOLDEN" ]]; then
  echo "FAIL: no baseline at ${GOLDEN#"$REPO"/}; run scripts/tenkz_golden.sh first" >&2
  exit 1
fi
if diff -u "$GOLDEN" "$CURRENT" >"$WORK/golden.diff"; then
  echo "PASS: $count event streams byte-identical to the golden baseline"
else
  echo "FAIL: event streams diverged from the golden baseline:" >&2
  grep '^[+-][0-9a-f]' "$WORK/golden.diff" >&2 || cat "$WORK/golden.diff" >&2
  exit 1
fi
