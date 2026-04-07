#!/usr/bin/env bash
# Deploy blueprint + API docs to gh-pages branch.
# Usage: ./scripts/deploy-docs.sh
#
# Builds everything locally, then pushes to gh-pages.
# For blueprint-only deploys, use deploy-blueprint.sh instead.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

echo "==> Building blueprint..."
cd "$REPO_ROOT/blueprint"
leanblueprint pdf
leanblueprint web

echo "==> Building API docs (this may take a while)..."
cd "$REPO_ROOT/docbuild"
lake update
lake build TNLean:docs

echo "==> Cloning gh-pages branch..."
git clone --branch gh-pages --single-branch --depth 1 \
  "$(git -C "$REPO_ROOT" remote get-url origin)" "$TMPDIR/site"

echo "==> Updating files..."
# Blueprint
rm -rf "$TMPDIR/site/blueprint"
mkdir -p "$TMPDIR/site/blueprint"
cp -r "$REPO_ROOT/blueprint/web/"* "$TMPDIR/site/blueprint/"
cp "$REPO_ROOT/blueprint/print/print.pdf" "$TMPDIR/site/blueprint.pdf"

# Homepage
cp "$REPO_ROOT/home_page/_config.yml" "$TMPDIR/site/"
cp "$REPO_ROOT/home_page/index.md" "$TMPDIR/site/"
cp "$REPO_ROOT/home_page/404.html" "$TMPDIR/site/" 2>/dev/null || true
cp "$REPO_ROOT/home_page/Gemfile" "$TMPDIR/site/" 2>/dev/null || true
cp -r "$REPO_ROOT/home_page/assets" "$TMPDIR/site/" 2>/dev/null || true
cp -r "$REPO_ROOT/home_page/_layouts" "$TMPDIR/site/" 2>/dev/null || true

# API docs
rm -rf "$TMPDIR/site/docs"
if [ -d "$REPO_ROOT/docbuild/.lake/build/doc" ]; then
  cp -r "$REPO_ROOT/docbuild/.lake/build/doc" "$TMPDIR/site/docs"
  echo "  Copied API docs to /docs/"
else
  echo "  Warning: docbuild/.lake/build/doc not found, skipping API docs"
fi

echo "==> Committing and pushing..."
cd "$TMPDIR/site"
git add -A
if git diff --cached --quiet; then
  echo "No changes to deploy."
else
  git commit -m "Full docs update ($(date -u '+%Y-%m-%d %H:%M UTC'))"
  git push origin gh-pages
  echo "==> Deployed!"
fi
