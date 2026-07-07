#!/usr/bin/env bash
# Build the paper-release blueprint PDF restricted to the first twelve
# chapters (ch01_intro through ch12_symmetry) as blueprint/print/print12.pdf.
#
# Run after scripts/blueprint_bibtex.py (which refreshes src/references.bib).
# The blueprint sources are copied to a temporary directory, content.tex is
# truncated there, and latexmk (XeLaTeX, via blueprint/latexmkrc) runs in the
# copy, so the checked-out blueprint directory is never modified; only the
# gitignored blueprint/print/print12.pdf artifact is written back.
#
# Cross-references from the kept chapters into dropped ones render as "??";
# these are expected (the full PDF remains the authoritative version).
set -euo pipefail

N_CHAPTERS="${N_CHAPTERS:-12}"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Copying blueprint sources..."
mkdir -p "$WORK_DIR/blueprint"
cp -R "$REPO_ROOT/blueprint/src" "$WORK_DIR/blueprint/src"

echo "==> Restricting content.tex to the first $N_CHAPTERS chapters..."
awk -v cap="$N_CHAPTERS" '
  /^[[:space:]]*\\input\{chapter\// {
    n++
    if (n > cap) { print "% [first-" cap "-chapters build] " $0; next }
  }
  { print }
' "$REPO_ROOT/blueprint/src/content.tex" > "$WORK_DIR/blueprint/src/content.tex"

kept="$(grep -c '^[[:space:]]*\\input{chapter/' "$WORK_DIR/blueprint/src/content.tex")"
if [ "$kept" -ne "$N_CHAPTERS" ]; then
  echo "::error::Expected $N_CHAPTERS active chapter inputs after truncation, found $kept"
  exit 1
fi

# Same engine and flags as the leanblueprint-generated latexmkrc
# ($pdflatex = 'xelatex -synctex=1'), stated explicitly because that rc is
# an untracked artifact not present on a fresh checkout.
echo "==> Building with latexmk (XeLaTeX)..."
(cd "$WORK_DIR/blueprint/src" \
  && latexmk -pdfxe -pdfxelatex='xelatex -synctex=1 %O %S' \
       -interaction=nonstopmode print.tex)

mkdir -p "$REPO_ROOT/blueprint/print"
cp "$WORK_DIR/blueprint/src/print.pdf" "$REPO_ROOT/blueprint/print/print12.pdf"
echo "==> Wrote blueprint/print/print12.pdf"
