#!/usr/bin/env bash
# Generate auxiliary (.aux) files for paper sources under Papers/
# so external references in paper-gap notes resolve their source numbering.
#
# Usage:
#   ./scripts/generate_paper_aux.sh [paper_dir_or_id]
# Examples:
#   ./scripts/generate_paper_aux.sh               # build all papers under Papers/
#   ./scripts/generate_paper_aux.sh 1606.00608    # build only Papers/1606.00608
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPERS_DIR="$ROOT_DIR/Papers"

if [ ! -d "$PAPERS_DIR" ]; then
  echo "::error::Papers directory $PAPERS_DIR not found"
  exit 1
fi

target="${1:-}"

build_paper_dir() {
  local dir="$1"
  local tex_files=()
  while IFS= read -r -d '' f; do
    # check if file contains \documentclass
    if grep -q '\\documentclass' "$f" 2>/dev/null; then
      tex_files+=("$(basename "$f")")
    fi
  done < <(find "$dir" -maxdepth 1 -name "*.tex" -print0)

  if [ ${#tex_files[@]} -eq 0 ]; then
    return 0
  fi

  echo "==> Generating source aux in $dir..."
  (
    cd "$dir"
    for tex in "${tex_files[@]}"; do
      echo "  -> Compiling $tex..."
      if command -v latexmk >/dev/null 2>&1; then
        latexmk -pdf -interaction=nonstopmode "$tex"
      elif command -v pdflatex >/dev/null 2>&1; then
        pdflatex -interaction=nonstopmode "$tex"
        pdflatex -interaction=nonstopmode "$tex"
      else
        echo "::error::Neither latexmk nor pdflatex is available"
        exit 1
      fi
    done
  )
}

if [ -n "$target" ]; then
  if [ -d "$target" ]; then
    build_paper_dir "$target"
  elif [ -d "$PAPERS_DIR/$target" ]; then
    build_paper_dir "$PAPERS_DIR/$target"
  else
    echo "::error::Paper target not found: $target"
    exit 1
  fi
else
  # Build all subdirectories under Papers/
  for d in "$PAPERS_DIR"/*/; do
    if [ -d "$d" ]; then
      build_paper_dir "$d"
    fi
  done
fi

echo "==> Paper source aux generation complete."
