#!/usr/bin/env bash

set -euo pipefail

REPO=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
exec python3 "$REPO/scripts/tenkz_rmp.py" "$@"
