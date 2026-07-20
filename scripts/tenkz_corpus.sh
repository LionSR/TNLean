#!/usr/bin/env bash

set -euo pipefail

REPO=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
CORPUS="$REPO/tests/tenkz"
JOBS=${TENKZ_CORPUS_JOBS:-4}

for command in timeout xelatex python3; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "FAIL: tenkz corpus requires $command" >&2
    exit 1
  fi
done

if ! [[ "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "FAIL: TENKZ_CORPUS_JOBS must be a positive integer (got '$JOBS')" >&2
  exit 1
fi

source_count=$(find "$CORPUS" -maxdepth 1 -type f -name '*.tex' | wc -l | tr -d ' ')
if [[ "$source_count" -eq 0 ]]; then
  echo "FAIL: no standalone corpus files found in $CORPUS" >&2
  exit 1
fi

metadata_failed=0
while IFS= read -r source; do
  first_line=$(sed -n '1p' "$source")
  if [[ "$first_line" != '% Regression:'* ]]; then
    echo "FAIL: ${source#"$REPO"/} needs a first-line % Regression: header" >&2
    metadata_failed=1
  fi
  if ! grep -q '^% Formula:' "$source"; then
    echo "FAIL: ${source#"$REPO"/} needs a % Formula: comment" >&2
    metadata_failed=1
  fi
done < <(find "$CORPUS" -maxdepth 1 -type f -name '*.tex' | LC_ALL=C sort)
if [[ "$metadata_failed" -ne 0 ]]; then
  exit 1
fi

WORK=$(mktemp -d "${TMPDIR:-/tmp}/tenkz-corpus.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
cp -R "$CORPUS/." "$WORK/"
mkdir -p "$WORK/results"

RESULTS="$WORK/results"
TEXINPUTS_CORPUS="$REPO/tex/tenkz//:$WORK//:${TEXINPUTS:-}"
export REPO WORK RESULTS TEXINPUTS_CORPUS

compile_one() {
  local source=$1
  local name stem transcript audit_report
  name=${source##*/}
  stem=${name%.tex}
  transcript="$RESULTS/$stem.xelatex"
  audit_report="$RESULTS/$stem.audit"

  echo "[tenkz corpus] $name"
  if ! (
    cd "$WORK"
    timeout 120 env TEXINPUTS="$TEXINPUTS_CORPUS" \
      xelatex -interaction=nonstopmode -halt-on-error "$name"
  ) >"$transcript" 2>&1; then
    {
      echo "FAIL: $name did not compile"
      tail -n 120 "$transcript"
    } >"$RESULTS/$stem.fail"
    return 1
  fi

  if [[ ! -f "$WORK/$stem.tnlog" ]]; then
    echo "FAIL: $name produced no $stem.tnlog" \
      >"$RESULTS/$stem.fail"
    return 1
  fi

  if ! python3 "$REPO/scripts/tenkz_audit.py" \
      "$WORK/$stem.tnlog" "$WORK/$name" >"$audit_report" 2>&1; then
    {
      echo "FAIL: $name failed tenkz_audit.py"
      cat "$audit_report"
    } >"$RESULTS/$stem.fail"
    return 1
  fi

  : >"$RESULTS/$stem.ok"
}
export -f compile_one

find "$WORK" -maxdepth 1 -type f -name '*.tex' -print0 \
  | LC_ALL=C sort -z >"$WORK/sources.list"

# The single quotes deliberately defer $1 expansion to each worker shell.
# shellcheck disable=SC2016
if ! xargs -0 -n 1 -P "$JOBS" bash -c 'compile_one "$1"' _ \
    <"$WORK/sources.list"; then
  for report in "$RESULTS"/*.fail; do
    [[ -e "$report" ]] || continue
    cat "$report" >&2
  done
  exit 1
fi

passed=$(find "$RESULTS" -maxdepth 1 -type f -name '*.ok' | wc -l | tr -d ' ')
if [[ "$passed" -ne "$source_count" ]]; then
  echo "FAIL: compiled and audited $passed of $source_count corpus files" >&2
  exit 1
fi

echo "PASS: compiled and audited $passed standalone tenkz corpus files"
