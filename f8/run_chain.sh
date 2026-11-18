#!/bin/bash
# Rebuild the F8 phase-2 (chain and domain) edit from the phase-1 head, in the current checkout.
set -e
S=/tmp/claude-0/-home-user-TNLean/a113a978-1f85-52c9-8773-a6b19c2e5dba/scratchpad
BASE=${1:-07ef45a}
git checkout -q "$BASE" -- TNLean blueprint docs
python3 $S/f8chain/hand_pre.py
python3 $S/f8chain/f8_chain.py --write > /dev/null
python3 $S/f8chain/f8_chain.py --write --docs > /dev/null
for f in $S/f8chain/hand_post_*.py; do [ -f "$f" ] && python3 "$f"; done
for k in 1 2 3 4 5 6; do python3 $S/f8chain/f8_chain.py --thread; done
python3 $S/f8chain/remove_params.py
python3 $S/f8chain/underscore_stmt.py
python3 $S/f8chain/fix_long_heads.py
for f in $S/f8chain/hand_post2_*.py; do [ -f "$f" ] && python3 "$f"; done
python3 $S/f8chain/gen_fix.py > /dev/null
python3 $S/f8hand/final_wrap.py "$BASE" > $S/f8chain/long_lines.txt
python3 scripts/generate_import_aggregators.py > /dev/null
