#!/usr/bin/env bash
# Recompute the finite inputs of the L >= 60 route of the spin-one Haldane-gap
# formalization plan (docs/formalization/haldane-gap/README.md) with OpenAI's
# own verifier, from the pinned openai/math revision.
#
# Usage: scripts/haldane_gap/verify_openai_inputs.sh [WORKDIR]
# Needs git and python3 (with venv). Takes about ten minutes on four cores.
set -euo pipefail

REV=adc7f1241b42e322a6451854ab7e4b4c146bf78a
PAPER=preprints/The-periodic-spin-one-Haldane-gap-September-24-2026
WORK=${1:-$(mktemp -d)}
mkdir -p "$WORK"
cd "$WORK"

if [ ! -d math ]; then
  git clone --filter=blob:none --no-checkout https://github.com/openai/math.git math
fi
git -C math sparse-checkout set "$PAPER"
git -C math checkout --quiet "$REV"
echo "openai/math at $(git -C math rev-parse HEAD)"

python3 -m venv venv
venv/bin/pip install --quiet numpy==2.3.5 scipy==1.16.2

cd "math/$PAPER/verification"
# thermal2 = the b = 21/2 table (rings of 6, 8, 10 sites, twists 1, P, C);
# trial120 = the 120-site integer trial contraction; scalars = exact checks.
for sel in thermal2 trial120 scalars; do
  env -u PYTHONOPTIMIZE "$WORK/venv/bin/python" -B verify.py \
    --only "$sel" --workers 4 --output "$WORK/out-$sel"
done
