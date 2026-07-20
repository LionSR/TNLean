#!/usr/bin/env bash
# Build the focused FT--MPS blueprint volume (ch01_intro through
# ch11_fundamental_theorem_proof) as blueprint/print/print12.pdf.
# The script and artifact retain their historical names for compatibility.
#
# Run after scripts/blueprint_bibtex.py (which refreshes src/references.bib).
# The blueprint sources are copied to a temporary directory and the dedicated
# FT--MPS entry point is built there, so the checked-out blueprint directory is
# never modified; only the gitignored
# blueprint/print/print12.pdf artifact is written back.
#
# The focused route ends at the proof itself.  Its retained prose must not
# depend on the downstream symmetry chapter; inspect any unresolved references.
# The full PDF remains the authoritative complete-blueprint version.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Copying blueprint sources..."
mkdir -p "$WORK_DIR/blueprint/src" "$WORK_DIR/tex"
rsync -a --exclude='.tn_svg_cache/' \
  "$REPO_ROOT/blueprint/src/" "$WORK_DIR/blueprint/src/"
cp -R "$REPO_ROOT/tex/tn" "$WORK_DIR/tex/tn"
cp -R "$REPO_ROOT/tex/tenkz" "$WORK_DIR/tex/tenkz"

# Verify that the dedicated router contains exactly the focused ch01_* through
# ch11_* sequence, in order and without duplicates.
echo "==> Checking the FT--MPS chapter router..."
expected="$(printf 'ch%02d\n' $(seq 1 11))"
kept="$(grep '^[[:space:]]*\\input{chapter/' \
  "$WORK_DIR/blueprint/src/content_ft_mps.tex" \
  | sed -E 's|.*chapter/(ch[0-9]{2})_.*|\1|')"
if [ "$kept" != "$expected" ]; then
  echo "::error::Active chapters are not exactly the focused ch01..ch11 sequence; got:"
  echo "$kept"
  exit 1
fi

# Same engine and flags as the leanblueprint-generated latexmkrc
# ($pdflatex = 'xelatex -synctex=1'), passed explicitly because that rc is
# an untracked artifact not present on a fresh checkout.
echo "==> Building with latexmk (XeLaTeX)..."
(cd "$WORK_DIR/blueprint/src" \
  && latexmk -pdfxe -pdfxelatex='xelatex -synctex=1 %O %S' \
       -interaction=nonstopmode print_ft_mps.tex)

mkdir -p "$REPO_ROOT/blueprint/print"
cp "$WORK_DIR/blueprint/src/print_ft_mps.pdf" \
  "$REPO_ROOT/blueprint/print/print12.pdf"
echo "==> Wrote blueprint/print/print12.pdf (focused Chapters 1--11 volume)"
