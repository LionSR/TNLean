#!/usr/bin/env bash
# Build the paper-release blueprint PDF restricted to the first twelve
# chapters (ch01_intro through ch12_symmetry) as blueprint/print/print12.pdf.
#
# Run after scripts/blueprint_bibtex.py (which refreshes src/references.bib).
# The blueprint sources are copied to a temporary directory, content.tex is
# filtered there, and latexmk runs in the copy, so the checked-out blueprint
# directory is never modified; only the gitignored
# blueprint/print/print12.pdf artifact is written back.
#
# Cross-references from the kept chapters into dropped ones render as "??";
# these are expected (the full PDF remains the authoritative version).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Copying blueprint sources..."
mkdir -p "$WORK_DIR/blueprint"
cp -R "$REPO_ROOT/blueprint/src" "$WORK_DIR/blueprint/src"

# Keep exactly the ch01_* ... ch12_* chapter inputs, selected by chapter-name
# prefix rather than by position, so reordering or inserting chapters in
# content.tex cannot silently change what this volume contains.
echo "==> Restricting content.tex to chapters ch01-ch12..."
awk '
  /^[[:space:]]*\\input\{chapter\// {
    if ($0 !~ /\\input\{chapter\/ch(0[1-9]|1[0-2])_/) {
      print "% [ch01-12 release build] " $0
      next
    }
  }
  { print }
' "$REPO_ROOT/blueprint/src/content.tex" > "$WORK_DIR/blueprint/src/content.tex"

expected="$(printf 'ch%02d\n' $(seq 1 12))"
kept="$(grep '^[[:space:]]*\\input{chapter/' "$WORK_DIR/blueprint/src/content.tex" \
  | sed -E 's|.*chapter/(ch[0-9]{2})_.*|\1|' | sort -u)"
if [ "$kept" != "$expected" ]; then
  echo "::error::Active chapters after filtering are not exactly ch01..ch12; got:"
  echo "$kept"
  exit 1
fi

# Same engine and flags as the leanblueprint-generated latexmkrc
# ($pdflatex = 'xelatex -synctex=1'), passed explicitly because that rc is
# an untracked artifact not present on a fresh checkout.
echo "==> Building with latexmk (XeLaTeX)..."
(cd "$WORK_DIR/blueprint/src" \
  && latexmk -pdfxe -pdfxelatex='xelatex -synctex=1 %O %S' \
       -interaction=nonstopmode print.tex)

mkdir -p "$REPO_ROOT/blueprint/print"
cp "$WORK_DIR/blueprint/src/print.pdf" "$REPO_ROOT/blueprint/print/print12.pdf"
echo "==> Wrote blueprint/print/print12.pdf"
