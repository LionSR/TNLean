"""Wrap the over-long lines that the hand edits and the threading pass introduced."""
import subprocess, sys, pathlib
sys.path.insert(0, '/tmp/claude-0/-home-user-TNLean/a113a978-1f85-52c9-8773-a6b19c2e5dba/scratchpad')
from leanwrap import wrap
BASE = sys.argv[1] if len(sys.argv) > 1 else '92f080b'
files = subprocess.run(['git', 'diff', '--name-only', BASE, '--', '*.lean'],
                       capture_output=True, text=True).stdout.split()
for f in files:
    p = pathlib.Path(f)
    if not p.exists():
        continue
    old = subprocess.run(['git', 'show', f'{BASE}:{f}'], capture_output=True, text=True).stdout
    t = p.read_text(); n = wrap(old, t)
    if n != t:
        p.write_text(n)
long = [f"{f}:{i}" for f in files if pathlib.Path(f).exists()
        for i, l in enumerate(pathlib.Path(f).read_text().split('\n'), 1) if len(l) > 100]
print('\n'.join(long))
