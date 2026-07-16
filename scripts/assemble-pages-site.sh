#!/usr/bin/env bash
# Assemble the GitHub Pages site tree from downloaded component artifacts.
# Usage: assemble-pages-site.sh COMPONENTS_DIR OUT_DIR
#
# COMPONENTS_DIR may contain:
#   site-blueprint/  Jekyll-built homepage, blueprint web + PDFs  (required)
#   site-docs/       doc-gen4 API docs and paper-gap PDFs         (optional)
#   site-badges/     badge endpoint JSON                          (optional)
set -euo pipefail

COMPONENTS="$1"
OUT="$2"

if [ ! -d "$COMPONENTS/site-blueprint" ]; then
  echo "::error::site-blueprint component missing — cannot assemble site"
  exit 1
fi

mkdir -p "$OUT"

echo "==> Homepage..."
cp -r "$COMPONENTS/site-blueprint/homepage/." "$OUT/"
# Badge JSON committed under home_page/badges is stale; live values come from
# the site-badges component below.
rm -rf "$OUT/badges"

echo "==> Blueprint..."
mkdir -p "$OUT/blueprint"
cp -r "$COMPONENTS/site-blueprint/blueprint/." "$OUT/blueprint/"
cp "$COMPONENTS/site-blueprint/blueprint.pdf" "$OUT/blueprint.pdf"
if [ -f "$COMPONENTS/site-blueprint/blueprint-ch01-12.pdf" ]; then
  cp "$COMPONENTS/site-blueprint/blueprint-ch01-12.pdf" "$OUT/blueprint-ch01-12.pdf"
fi

if [ -d "$COMPONENTS/site-docs/docs" ]; then
  echo "==> API docs..."
  cp -r "$COMPONENTS/site-docs/docs" "$OUT/docs"
else
  echo "::warning::site-docs component missing — deploying without API docs (the next docgen run restores them)"
fi
if [ -d "$COMPONENTS/site-docs/paper-gaps" ]; then
  echo "==> Paper-gap PDFs..."
  cp -r "$COMPONENTS/site-docs/paper-gaps" "$OUT/paper-gaps"
fi

if [ -d "$COMPONENTS/site-badges" ]; then
  echo "==> Badges..."
  mkdir -p "$OUT/badges"
  cp "$COMPONENTS/site-badges"/*.json "$OUT/badges/"
else
  echo "::warning::site-badges component missing — deploying without badge endpoints"
fi

echo "==> Site assembled at $OUT"
du -sh "$OUT"
