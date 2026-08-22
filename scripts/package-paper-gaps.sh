#!/usr/bin/env bash
# Package the paper-gap notes for the Pages site (index, PDFs, BibTeX).
# Thin wrapper over the texra-blueprint CLI so workflow calls keep their
# interface. Usage: package-paper-gaps.sh OUT_DIR
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
texra-blueprint --root "$REPO_ROOT" paper-gaps site "$1"
