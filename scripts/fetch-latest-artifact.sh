#!/usr/bin/env bash
# Download the newest non-expired GitHub Actions artifact with a given name.
# Usage: fetch-latest-artifact.sh NAME DEST_DIR
#
# Exits 0 with a warning (and without creating DEST_DIR) when no artifact is
# available; callers decide whether a missing component is fatal.
# Requires GH_TOKEN (or gh auth) with actions:read on GITHUB_REPOSITORY.
set -euo pipefail

NAME="$1"
DEST="$2"
REPO="${GITHUB_REPOSITORY:?GITHUB_REPOSITORY must be set}"

# The API returns newest-first; sort by created_at anyway to be explicit.
artifact_id="$(gh api "repos/${REPO}/actions/artifacts?name=${NAME}&per_page=100" \
  --jq '[.artifacts[] | select(.expired | not)] | sort_by(.created_at) | last | .id // empty')"

if [ -z "$artifact_id" ]; then
  echo "::warning::No artifact named '${NAME}' found"
  exit 0
fi

echo "==> Downloading artifact ${NAME} (id ${artifact_id})..."
tmp_zip="$(mktemp)"
trap 'rm -f "$tmp_zip"' EXIT
gh api "repos/${REPO}/actions/artifacts/${artifact_id}/zip" > "$tmp_zip"
mkdir -p "$DEST"
unzip -q "$tmp_zip" -d "$DEST"
echo "==> Extracted ${NAME} to ${DEST}"
