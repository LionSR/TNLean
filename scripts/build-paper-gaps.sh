#!/usr/bin/env bash
# Compile all paper-gap notes in docs/paper-gaps/ to PDF.
# Thin wrapper over the texra-blueprint CLI.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
texra-blueprint --root "$REPO_ROOT" paper-gaps build
