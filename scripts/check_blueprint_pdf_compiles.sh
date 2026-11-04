#!/usr/bin/env bash
# Compile the print volume of the blueprint once with XeTeX and fail on TeX errors.
#
# The pull-request check exists to catch LaTeX that plasTeX accepts and XeTeX
# rejects. One typesetting pass sees every such error; the extra passes that
# `leanblueprint pdf` runs to settle cross-references and the bibliography
# roughly double the job without finding anything new, and converting the
# typeset pages to PDF takes seconds. So this script runs latexmk with the
# repository's latexmkrc (private format, memory budgets, tenkz paths) but
# allows a single XeTeX run and reads the TeX log for errors itself. It asks
# for .xdv output; latexmk 4.83 (Ubuntu 24.04) lets the latexmkrc's PDF mode
# win and writes print.pdf instead, so either file counts, provided this run
# wrote it. latexmk exits with status 12 when the one run leaves references
# unstable; that status is expected here.
#
# Usage: scripts/check_blueprint_pdf_compiles.sh
# Runs from any directory; the volume is blueprint/src/print.tex.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
src_dir="$repo_root/blueprint/src"
print_dir="$repo_root/blueprint/print"
log="$print_dir/print.log"
stamp="$print_dir/.check_started"

mkdir -p "$print_dir"
touch "$stamp"
cd "$src_dir"

status=0
latexmk -e '$max_repeat=1' -xdv -interaction=nonstopmode \
  -output-directory=../print print.tex || status=$?

if [[ ! -f "$log" ]]; then
  echo "::error::XeTeX wrote no log at blueprint/print/print.log (latexmk status $status)"
  exit 1
fi

if grep -q '^! ' "$log"; then
  echo "::error::TeX errors in the print volume (blueprint/print/print.log):"
  grep -n -A6 '^! ' "$log" | head -80
  exit 1
fi

output=""
for candidate in "$print_dir/print.xdv" "$print_dir/print.pdf"; do
  if [[ -s "$candidate" && "$candidate" -nt "$stamp" ]]; then
    output="$candidate"
  fi
done
if [[ -z "$output" ]]; then
  echo "::error::XeTeX wrote neither print.xdv nor print.pdf in this run (latexmk status $status)"
  exit 1
fi

if [[ $status -ne 0 && $status -ne 12 ]]; then
  echo "::error::latexmk exited with status $status without a TeX error in the log"
  exit "$status"
fi

echo "Print volume typeset in one XeTeX pass with no TeX errors (latexmk status $status)."
