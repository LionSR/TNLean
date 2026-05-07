#!/usr/bin/env bash
# Compile all proof-gap notes in docs/paper-gaps/ to PDF.
# Usage: ./scripts/build-paper-gaps.sh
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GAPS_DIR="$REPO_ROOT/docs/paper-gaps"

# Switch to the paper-gaps directory so \input{command} and \bibliography{references}
# resolve relative to docs/paper-gaps/.
cd "$GAPS_DIR"

for texfile in *.tex; do
  # Skip includes and the template
  if [ "$texfile" = "command.tex" ] || [ "$texfile" = "template.tex" ]; then
    continue
  fi

  base="${texfile%.tex}"
  echo "::group::Building $texfile"

  # Run latexmk non-interactively with pdf output.  Halt on error so the CI
  # catches bad runs, but allow warnings.
  latexmk -pdf -interaction=nonstopmode -halt-on-error "$texfile"

  # Clean auxiliary files
  latexmk -c "$texfile"

  echo "::endgroup::"
done

echo "::notice::Compiled $(ls *.pdf 2>/dev/null | wc -l) paper-gap PDFs"
