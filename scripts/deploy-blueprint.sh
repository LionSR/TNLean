#!/usr/bin/env bash
# Deploy blueprint to gh-pages branch.
# Usage: ./scripts/deploy-blueprint.sh
#
# Builds leanblueprint locally, then pushes only the blueprint
# and homepage files to gh-pages (preserving /docs/).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

echo "==> Building blueprint..."
cd "$REPO_ROOT/blueprint"
leanblueprint pdf
leanblueprint web

echo "==> Cloning gh-pages branch..."
git clone --branch gh-pages --single-branch --depth 1 \
  "$(git -C "$REPO_ROOT" remote get-url origin)" "$TMPDIR/site"

echo "==> Updating blueprint files..."
# Update blueprint
rm -rf "$TMPDIR/site/blueprint"
mkdir -p "$TMPDIR/site/blueprint"
cp -r "$REPO_ROOT/blueprint/web/"* "$TMPDIR/site/blueprint/"
cp "$REPO_ROOT/blueprint/print/print.pdf" "$TMPDIR/site/blueprint.pdf"

# Update homepage
cp "$REPO_ROOT/home_page/_config.yml" "$TMPDIR/site/"
cp "$REPO_ROOT/home_page/index.md" "$TMPDIR/site/"
cp "$REPO_ROOT/home_page/404.html" "$TMPDIR/site/" 2>/dev/null || true
cp "$REPO_ROOT/home_page/Gemfile" "$TMPDIR/site/" 2>/dev/null || true
cp -r "$REPO_ROOT/home_page/assets" "$TMPDIR/site/" 2>/dev/null || true
cp -r "$REPO_ROOT/home_page/_layouts" "$TMPDIR/site/" 2>/dev/null || true

echo "==> Committing and pushing..."
cd "$TMPDIR/site"
git add -A
if git diff --cached --quiet; then
  echo "No changes to deploy."
else
  git commit -m "Update blueprint ($(date -u '+%Y-%m-%d %H:%M UTC'))"
  git push origin gh-pages
  echo "==> Deployed!"
fi
