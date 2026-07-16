#!/usr/bin/env bash
# Trigger a blueprint build + Pages deployment.
# The site now deploys through GitHub Actions artifacts (see
# .github/workflows/deploy-pages.yml); there is no gh-pages branch to push,
# so local builds cannot publish directly.
set -euo pipefail
exec gh workflow run blueprint.yml --ref main
