#!/usr/bin/env bash

set -euo pipefail

REPO=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
CORPUS="$REPO/tests/tenkz"
# Test seam for the isolated manifest-mutation regression.
PROVENANCE=${TENKZ_CORPUS_PROVENANCE:-"$CORPUS/PROVENANCE.tsv"}
LOCAL_FIXTURES="$CORPUS/LOCAL_FIXTURES.tsv"
JOBS=${TENKZ_CORPUS_JOBS:-4}
RENDER=0
RENDER_DIR="$REPO/build/tenkz-corpus-render"
RENDER_DIR_SET=0

usage() {
  cat <<'EOF'
Usage: scripts/tenkz_corpus.sh [--render] [--render-dir DIRECTORY]

Compile and audit the standalone tenkz regression corpus.  --render also
produces deterministic 200-dpi PNGs; its default output directory is
build/tenkz-corpus-render.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --render)
      if [[ "$RENDER" -eq 1 ]]; then
        echo "FAIL: --render may be specified only once" >&2
        exit 2
      fi
      RENDER=1
      shift
      ;;
    --render-dir)
      if [[ "$RENDER_DIR_SET" -eq 1 ]]; then
        echo "FAIL: --render-dir may be specified only once" >&2
        exit 2
      fi
      if [[ $# -lt 2 || -z "$2" || "$2" == -* ]]; then
        echo "FAIL: --render-dir requires a non-empty directory" >&2
        exit 2
      fi
      RENDER_DIR=$2
      RENDER_DIR_SET=1
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "FAIL: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ "$RENDER_DIR_SET" -eq 1 && "$RENDER" -ne 1 ]]; then
  echo "FAIL: --render-dir requires --render" >&2
  exit 2
fi
if [[ "$RENDER" -eq 1 && "$RENDER_DIR" != /* ]]; then
  RENDER_DIR="$REPO/$RENDER_DIR"
fi
if [[ "${TENKZ_CORPUS_VALIDATE_ONLY:-0}" == 1 && "$RENDER" -eq 1 ]]; then
  echo "FAIL: --render cannot be combined with TENKZ_CORPUS_VALIDATE_ONLY=1" >&2
  exit 2
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "FAIL: tenkz corpus requires python3" >&2
  exit 1
fi

if ! [[ "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "FAIL: TENKZ_CORPUS_JOBS must be a positive integer (got '$JOBS')" >&2
  exit 1
fi

python3 - "$REPO" "$PROVENANCE" "$LOCAL_FIXTURES" <<'PY'
import csv
import hashlib
import subprocess
import sys
from collections import Counter
from pathlib import Path


repo = Path(sys.argv[1])
corpus = repo / "tests" / "tenkz"
provenance = Path(sys.argv[2])
local_fixtures = Path(sys.argv[3])


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


try:
    with provenance.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, dialect="excel-tab"))
except OSError as exc:
    fail(f"cannot read {provenance}: {exc}")

header = ["source_file", "disposition", "adopted_path", "reason"]
if not rows or rows[0] != header:
    fail(f"PROVENANCE.tsv header must be exactly {header!r}")
if any(len(row) != len(header) for row in rows[1:]):
    bad = next(index for index, row in enumerate(rows[1:], 2)
               if len(row) != len(header))
    fail(f"PROVENANCE.tsv row {bad} must have exactly four tab-separated fields")

records = [dict(zip(header, row)) for row in rows[1:]]
source_names = [record["source_file"] for record in records]
duplicates = sorted(name for name, count in Counter(source_names).items() if count > 1)
if duplicates:
    fail("PROVENANCE.tsv repeats source_file entries: " + ", ".join(duplicates))
if any(not name or Path(name).name != name or not name.endswith(".tex")
       for name in source_names):
    fail("every PROVENANCE.tsv source_file must be a plain .tex basename")
if any(not record["reason"].strip() for record in records):
    fail("every PROVENANCE.tsv row needs a non-empty reason")

# Independent source-name invariant derived from tenkz/handoff-artifacts.
# Sorting and LF-delimiting make the digest insensitive to TSV row order.
expected_source_names_sha256 = (
    "ad2decb55da2410f6bfaea1a15dddff58d135ac5a2318091fb205dd0a620bdda"
)
source_names_payload = "".join(
    f"{name}\n" for name in sorted(source_names)
).encode("utf-8")
actual_source_names_sha256 = hashlib.sha256(source_names_payload).hexdigest()
if actual_source_names_sha256 != expected_source_names_sha256:
    fail(
        "PROVENANCE.tsv source-file census SHA-256 must be "
        f"{expected_source_names_sha256}, got {actual_source_names_sha256}"
    )

# Independent handoff-census invariant: do not derive these values from the TSV
# being checked.  A changed manifest must not redefine its own expected corpus.
expected_counts = {"standalone": 6, "excluded": 20}
actual_counts = Counter(record["disposition"] for record in records)
if actual_counts != expected_counts:
    fail(
        "PROVENANCE.tsv disposition census must be "
        + ", ".join(f"{value} {key}" for key, value in expected_counts.items())
        + "; got "
        + ", ".join(f"{key}={actual_counts.get(key, 0)}" for key in expected_counts)
    )

standalone = {
    record["source_file"]: record["adopted_path"]
    for record in records if record["disposition"] == "standalone"
}

# Repository-local probes are not part of the adopted handoff corpus.  Keep
# them in their own manifest so adding a regression never rewrites the
# independent handoff source-name or disposition invariants above.
try:
    with local_fixtures.open(encoding="utf-8", newline="") as stream:
        local_rows = list(csv.reader(stream, dialect="excel-tab"))
except OSError as exc:
    fail(f"cannot read {local_fixtures}: {exc}")
local_header = ["source_file", "adopted_path", "reason"]
if not local_rows or local_rows[0] != local_header:
    fail(f"LOCAL_FIXTURES.tsv header must be exactly {local_header!r}")
if any(len(row) != len(local_header) for row in local_rows[1:]):
    bad = next(index for index, row in enumerate(local_rows[1:], 2)
               if len(row) != len(local_header))
    fail(f"LOCAL_FIXTURES.tsv row {bad} must have exactly three tab-separated fields")
local_records = [dict(zip(local_header, row)) for row in local_rows[1:]]
local_names = [record["source_file"] for record in local_records]
local_duplicates = sorted(
    name for name, count in Counter(local_names).items() if count > 1
)
if local_duplicates:
    fail("LOCAL_FIXTURES.tsv repeats source_file entries: "
         + ", ".join(local_duplicates))
if set(local_names) & set(source_names):
    fail("local fixtures must not also appear in the handoff PROVENANCE.tsv")
if any(not name or Path(name).name != name or not name.endswith(".tex")
       for name in local_names):
    fail("every LOCAL_FIXTURES.tsv source_file must be a plain .tex basename")
if any(not record["reason"].strip() for record in local_records):
    fail("every LOCAL_FIXTURES.tsv row needs a non-empty reason")
standalone.update({
    record["source_file"]: record["adopted_path"]
    for record in local_records
})
actual_tex = {path.name for path in corpus.glob("*.tex") if path.is_file()}
if set(standalone) != actual_tex:
    missing = sorted(set(standalone) - actual_tex)
    extra = sorted(actual_tex - set(standalone))
    details = []
    if missing:
        details.append("missing tracked fixtures: " + ", ".join(missing))
    if extra:
        details.append("fixtures absent from provenance: " + ", ".join(extra))
    fail("standalone corpus disagrees with PROVENANCE.tsv (" + "; ".join(details) + ")")
for source_name, adopted_path in standalone.items():
    expected_path = f"tests/tenkz/{source_name}"
    if adopted_path != expected_path:
        fail(f"{source_name} adopted_path must be {expected_path}, got {adopted_path!r}")

support_records = [record for record in records if record["disposition"] == "support"]
support_paths = {record["adopted_path"] for record in support_records}
actual_support = {
    path.relative_to(repo).as_posix()
    for path in corpus.glob("*.inc") if path.is_file()
}
if support_paths != actual_support:
    fail(
        "support include census disagrees with PROVENANCE.tsv: expected "
        f"{sorted(support_paths)!r}, found {sorted(actual_support)!r}"
    )
if any(not path.startswith("tests/tenkz/") or not path.endswith(".inc")
       for path in support_paths):
    fail("support adopted_path must name a tests/tenkz/*.inc file")
if any(record["adopted_path"] != "-" for record in records
       if record["disposition"] == "excluded"):
    fail("excluded PROVENANCE.tsv rows must use '-' as adopted_path")

tracked = subprocess.run(
    ["git", "-C", str(repo), "ls-files", "--", "tests/tenkz"],
    check=False,
    text=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
)
if tracked.returncode != 0:
    fail("cannot verify tracked corpus files with git: " + tracked.stderr.strip())
tracked_fixtures = {
    line for line in tracked.stdout.splitlines()
    if Path(line).parent == Path("tests/tenkz")
    and line.endswith((".tex", ".inc"))
}
actual_fixtures = {
    f"tests/tenkz/{name}" for name in actual_tex
} | actual_support
if tracked_fixtures != actual_fixtures:
    missing = sorted(actual_fixtures - tracked_fixtures)
    stale = sorted(tracked_fixtures - actual_fixtures)
    details = []
    if missing:
        details.append("untracked fixtures: " + ", ".join(missing))
    if stale:
        details.append("tracked fixtures missing on disk: " + ", ".join(stale))
    fail("git fixture census mismatch (" + "; ".join(details) + ")")
PY

python3 "$REPO/scripts/tenkz_lint.py" --census
python3 "$REPO/scripts/test_tenkz_cubic.py"

source_count=$(find "$CORPUS" -maxdepth 1 -type f -name '*.tex' | wc -l | tr -d ' ')

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

if [[ "${TENKZ_CORPUS_VALIDATE_ONLY:-0}" == 1 ]]; then
  echo "PASS: validated provenance and metadata for $source_count standalone tenkz corpus files"
  exit 0
fi

required_commands=(timeout xelatex)
if [[ "$RENDER" -eq 1 ]]; then
  required_commands+=(pdfinfo pdftocairo)
fi
for command in "${required_commands[@]}"; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "FAIL: tenkz corpus requires $command" >&2
    exit 1
  fi
done

# These package-internal probes intentionally open the tenkz event log without
# creating a tenkz picture.  Keep the exception explicit: every other fixture
# must prove that the event instrumentation wrote at least one record.
is_zero_event_probe() {
  case "$1" in
    plane_experiment.tex) return 0 ;;
    *) return 1 ;;
  esac
}

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

  if ! grep -q '[^[:space:]]' "$WORK/$stem.tnlog" \
      && ! is_zero_event_probe "$name"; then
    echo "FAIL: $name produced an empty $stem.tnlog" \
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
export -f is_zero_event_probe

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

if [[ "$RENDER" -eq 1 ]]; then
  python3 "$REPO/scripts/tenkz_render_corpus.py" \
    --input-dir "$WORK" \
    --output-dir "$RENDER_DIR" \
    --protect "$REPO" \
    --protect "$CORPUS"
fi

echo "PASS: compiled and audited $passed standalone tenkz corpus files"
