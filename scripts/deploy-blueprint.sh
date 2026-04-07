#!/usr/bin/env bash
# Deploy blueprint to gh-pages branch.
# Usage: ./scripts/deploy-blueprint.sh
#
# Builds leanblueprint locally, then pushes only the blueprint
# and homepage files to gh-pages (preserving /docs/).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Building blueprint..."
cd "$REPO_ROOT/blueprint"
leanblueprint pdf
leanblueprint web

echo "==> Cloning gh-pages branch..."
git clone --branch gh-pages --single-branch --depth 1 \
  "$(git -C "$REPO_ROOT" remote get-url origin)" "$WORK_DIR/site"

echo "==> Updating blueprint files..."
# Update blueprint
rm -rf "$WORK_DIR/site/blueprint"
mkdir -p "$WORK_DIR/site/blueprint"
cp -r "$REPO_ROOT/blueprint/web/"* "$WORK_DIR/site/blueprint/"
cp "$REPO_ROOT/blueprint/print/print.pdf" "$WORK_DIR/site/blueprint.pdf"

# Update homepage
cp "$REPO_ROOT/home_page/_config.yml" "$WORK_DIR/site/"
cp "$REPO_ROOT/home_page/index.md" "$WORK_DIR/site/"
cp "$REPO_ROOT/home_page/404.html" "$WORK_DIR/site/" 2>/dev/null || true
cp "$REPO_ROOT/home_page/Gemfile" "$WORK_DIR/site/" 2>/dev/null || true
cp -r "$REPO_ROOT/home_page/assets" "$WORK_DIR/site/" 2>/dev/null || true
cp -r "$REPO_ROOT/home_page/_layouts" "$WORK_DIR/site/" 2>/dev/null || true

echo "==> Committing and pushing..."
cd "$WORK_DIR/site"
git config user.name "$(git -C "$REPO_ROOT" config user.name || echo 'deploy-script')"
git config user.email "$(git -C "$REPO_ROOT" config user.email || echo 'deploy@local')"
git add -A
if git diff --cached --quiet; then
  echo "No changes to deploy."
else
  git commit -m "Update blueprint ($(date -u '+%Y-%m-%d %H:%M UTC'))"
  git push origin gh-pages
  echo "==> Deployed!"
fi
