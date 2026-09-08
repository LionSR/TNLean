#!/usr/bin/env bash
# Build the author-facing CPSV17 corrections note and its source references.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
bash scripts/generate_paper_aux.sh 1606.00608
# The paper repeats several main-text labels in unnumbered appendix restatements.
# Keep their first occurrence, which is the numbered main-text statement.
python3 - <<'PY'
from pathlib import Path
import re
folder = Path('build/paper-aux/1606.00608')
source = folder / 'MPDO-22-12-17-2.aux'
target = folder / 'MPDO-22-12-17-2-note.aux'
seen = set()
records = []
for line in source.read_text().splitlines():
    match = re.match(r'\\newlabel\{([^}]*)\}', line)
    if match and match.group(1) not in seen:
        seen.add(match.group(1))
        records.append(line)
target.write_text(
    '% Generated from the original paper; first occurrences resolve repeated labels.\n'
    '\\relax\n' + '\n'.join(records) + '\n')
PY
mkdir -p build/cpsv17-corrections
cd docs/paper-gaps
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir="$ROOT/build/cpsv17-corrections" cpsv17_corrections.tex
