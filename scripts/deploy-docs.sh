#!/usr/bin/env bash
# Deploy blueprint + API docs to gh-pages.
# Usage: ./scripts/deploy-docs.sh
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "==> Building blueprint..."
cd "$REPO_ROOT"
python3 scripts/blueprint_bibtex.py

cd "$REPO_ROOT/blueprint"
leanblueprint pdf
leanblueprint web

echo "==> Building API docs (this may take a while)..."
cd "$REPO_ROOT/docbuild"
lake build TNLean:docs

exec "$REPO_ROOT/scripts/deploy-to-gh-pages.sh" --with-docs
