#!/usr/bin/env bash
# Build the FT--MPS blueprint volume (ch01_intro through ch12_symmetry, together
# with the auxiliary channel-theory chapter) as blueprint/print/print12.pdf.
#
# Run after scripts/blueprint_bibtex.py (which refreshes src/references.bib).
# The blueprint sources are copied to a temporary directory and the dedicated
# FT--MPS entry point is built there, so the checked-out blueprint directory is
# never modified; only the gitignored
# blueprint/print/print12.pdf artifact is written back.
#
# Cross-references from the kept chapters into dropped ones render as "??";
# these are expected (the full PDF remains the authoritative version).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Copying blueprint sources..."
mkdir -p "$WORK_DIR/blueprint/src" "$WORK_DIR/tex"
rsync -a --exclude='.tenkz_svg_cache/' \
  "$REPO_ROOT/blueprint/src/" "$WORK_DIR/blueprint/src/"
cp -R "$REPO_ROOT/tex/tenkz" "$WORK_DIR/tex/tenkz"

# Verify that the dedicated router contains the exact focused-volume chapter
# sequence, in order and without duplicates.
echo "==> Checking the FT--MPS chapter router..."
expected="ch01_intro
ch02_mps
ch03_single
ch04_channels
ch05_schwarz
ch06_qpf
ch07_spectral
ch08_wielandt
ch09_canonical
ch10_bnt
ch11_fundamental_theorem_proof
ch12_symmetry
ch12_auxiliary_channel_theory"
kept="$(grep '^[[:space:]]*\\input{chapter/' \
  "$WORK_DIR/blueprint/src/content_ft_mps.tex" \
  | sed -E 's|.*chapter/([^}]+).*|\1|')"
if [ "$kept" != "$expected" ]; then
  echo "::error::Active chapters do not match the focused-volume router; got:"
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
echo "==> Wrote blueprint/print/print12.pdf (Chapters 1--12 plus auxiliary channel theory)"
