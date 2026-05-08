#!/usr/bin/env bash
# Shared deploy logic for pushing to gh-pages branch.
# Usage: ./scripts/deploy-to-gh-pages.sh [--with-docs] [--ci] [--badges-dir DIR] [--badges-only]
#
# --with-docs   Also deploy API docs from docbuild/.lake/build/doc (fails if missing)
# --ci          Use github-actions[bot] as committer instead of local git config
# --badges-dir DIR  Use pre-generated badge JSON from DIR instead of regenerating
# --badges-only     Only deploy badges (skip blueprint, homepage, docs, paper-gaps)
set -euo pipefail

WITH_DOCS=false
CI_MODE=false
BADGES_DIR=""
BADGES_ONLY=false
BADGES_DIR_NEXT=false
for arg in "$@"; do
  if [ "$BADGES_DIR_NEXT" = true ]; then
    BADGES_DIR="$arg"
    BADGES_DIR_NEXT=false
    continue
  fi
  case $arg in
    --with-docs) WITH_DOCS=true ;;
    --ci) CI_MODE=true ;;
    --badges-only) BADGES_ONLY=true ;;
    --badges-dir) BADGES_DIR_NEXT=true ;;
  esac
done

if [ "$BADGES_DIR_NEXT" = true ]; then
  echo "::error::--badges-dir requires a path argument"
  exit 1
fi

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Cloning gh-pages branch..."
if [ "$CI_MODE" = true ]; then
  REPO_URL="https://x-access-token:${GITHUB_TOKEN:-$GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
else
  REPO_URL="$(git -C "$REPO_ROOT" remote get-url origin)"
fi
git clone --branch gh-pages --single-branch --depth 1 "$REPO_URL" "$WORK_DIR/site"

if [ "$BADGES_ONLY" = true ]; then
  echo "==> Badges-only mode: skipping blueprint, homepage, docs, paper-gaps"

  # Deploy pre-generated badges
  if [ -n "$BADGES_DIR" ]; then
    echo "==> Copying pre-generated badges from $BADGES_DIR..."
    rm -rf "$WORK_DIR/site/badges"
    mkdir -p "$WORK_DIR/site/badges"
    cp -r "$BADGES_DIR"/*.json "$WORK_DIR/site/badges/" 2>/dev/null || {
      echo "::warning::No badge JSON files found in $BADGES_DIR"
    }
  else
    # Fall back to regenerating badges live
    echo "==> Regenerating badge endpoints..."
    mkdir -p "$WORK_DIR/site/badges"
    python3 "$REPO_ROOT/scripts/write_badges.py" "$WORK_DIR/site/badges"
  fi
else

# Update blueprint
echo "==> Updating blueprint..."
rm -rf "$WORK_DIR/site/blueprint"
mkdir -p "$WORK_DIR/site/blueprint"
cp -r "$REPO_ROOT/blueprint/web/"* "$WORK_DIR/site/blueprint/"
cp "$REPO_ROOT/blueprint/print/print.pdf" "$WORK_DIR/site/blueprint.pdf" 2>/dev/null || true

# Update homepage (remove all homepage files first, then copy fresh)
echo "==> Updating homepage..."
rm -rf "$WORK_DIR/site/_layouts" "$WORK_DIR/site/assets" \
       "$WORK_DIR/site/_config.yml" "$WORK_DIR/site/index.md" \
       "$WORK_DIR/site/404.html" "$WORK_DIR/site/Gemfile" \
       "$WORK_DIR/site/badges"
cp -r "$REPO_ROOT/home_page/"* "$WORK_DIR/site/"

# Regenerate badge endpoints directly into the site so published JSON reflects
# current sorry/axiom counts and toolchain versions, not committed (stale) values.
echo "==> Regenerating badge endpoints..."
python3 "$REPO_ROOT/scripts/write_badges.py" "$WORK_DIR/site/badges"

# Update API docs (only with --with-docs)
if [ "$WITH_DOCS" = true ]; then
  echo "==> Updating API docs..."
  if [ ! -d "$REPO_ROOT/docbuild/.lake/build/doc" ]; then
    echo "::error::API docs not found at docbuild/.lake/build/doc"
    echo "Run 'cd docbuild && lake build TNLean:docs' first."
    exit 1
  fi
  rm -rf "$WORK_DIR/site/docs"
  cp -r "$REPO_ROOT/docbuild/.lake/build/doc" "$WORK_DIR/site/docs"
fi

# Update paper-gap PDFs (only if built)
echo "==> Updating paper-gap PDFs..."
shopt -s nullglob
GAP_PDFS=("$REPO_ROOT"/docs/paper-gaps/*.pdf)
if [ ${#GAP_PDFS[@]} -gt 0 ]; then
  rm -rf "$WORK_DIR/site/paper-gaps"
  mkdir -p "$WORK_DIR/site/paper-gaps"
  cp "${GAP_PDFS[@]}" "$WORK_DIR/site/paper-gaps/"
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
  } > "$WORK_DIR/site/paper-gaps/index.html"
  echo "Copied ${#GAP_PDFS[@]} paper-gap PDFs"
else
  echo "No paper-gap PDFs found; keeping existing site content"
fi
shopt -u nullglob

fi  # end of if-not-BADGES_ONLY

# Commit and push
echo "==> Committing and pushing..."
cd "$WORK_DIR/site"
if [ "$CI_MODE" = true ]; then
  git config user.name "github-actions[bot]"
  git config user.email "github-actions[bot]@users.noreply.github.com"
else
  git config user.name "$(git -C "$REPO_ROOT" config user.name || echo 'deploy-script')"
  git config user.email "$(git -C "$REPO_ROOT" config user.email || echo 'deploy@local')"
fi
git add -A
if git diff --cached --quiet; then
  echo "No changes to deploy."
else
  MSG="Update blueprint"
  [ "$WITH_DOCS" = true ] && MSG="Full docs update"
  [ "$BADGES_ONLY" = true ] && MSG="Update badge endpoints"
  git commit -m "$MSG ($(date -u '+%Y-%m-%d %H:%M UTC'))"
  git push origin gh-pages
  echo "==> Deployed!"
fi
