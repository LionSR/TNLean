#!/usr/bin/env bash
# Package the paper-gap notes for the Pages site: PDFs, per-note landing
# pages, grouped index, and aggregate BibTeX. Thin wrapper over the
# generator so existing workflow calls keep their interface.
# Usage: package-paper-gaps.sh OUT_DIR
set -euo pipefail

OUT="$1"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

python3 "$REPO_ROOT/scripts/paper_gaps_site.py" "$OUT"
