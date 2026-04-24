#!/usr/bin/env bash
# Deploy blueprint to gh-pages (preserves /docs/).
# Usage: ./scripts/deploy-blueprint.sh
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "==> Building blueprint..."
cd "$REPO_ROOT"
python3 scripts/blueprint_bibtex.py

cd "$REPO_ROOT/blueprint"
leanblueprint pdf
leanblueprint web

exec "$REPO_ROOT/scripts/deploy-to-gh-pages.sh"
