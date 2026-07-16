#!/usr/bin/env bash
# Copy built paper-gap PDFs into OUT_DIR with a generated index page.
# Usage: package-paper-gaps.sh OUT_DIR
set -euo pipefail

OUT="$1"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

shopt -s nullglob
GAP_PDFS=("$REPO_ROOT"/docs/paper-gaps/*.pdf)
shopt -u nullglob

if [ ${#GAP_PDFS[@]} -eq 0 ]; then
  echo "No paper-gap PDFs found; skipping"
  exit 0
fi

mkdir -p "$OUT"
cp "${GAP_PDFS[@]}" "$OUT/"
{
  echo "<!doctype html>"
  echo "<html lang=\"en\">"
  echo "<head>"
  echo "  <meta charset=\"utf-8\">"
  echo "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
  echo "  <title>TNLean paper-gap notes</title>"
  echo "</head>"
  echo "<body>"
  echo "  <h1>TNLean paper-gap notes</h1>"
  echo "  <ul>"
  for pdf in "${GAP_PDFS[@]}"; do
    name="$(basename "$pdf")"
    echo "    <li><a href=\"$name\">$name</a></li>"
  done
  echo "  </ul>"
  echo "</body>"
  echo "</html>"
} > "$OUT/index.html"
echo "Copied ${#GAP_PDFS[@]} paper-gap PDFs"
