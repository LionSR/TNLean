import re,json
from pathlib import Path
roots={'TNLean':Path('/tmp/pin729-mps'),'QICLean':Path('/tmp/qic729-mps')}; memo={}
def deps(m):
 p=roots[m.split('.')[0]]/Path(m.replace('.','/')).with_suffix('.lean')
 if not p.exists():return []
 return [d for line in p.read_text().splitlines() if re.match(r'^(?:public |private )?import ',line) for d in line.split('import ',1)[1].split() if d.split('.')[0] in roots]
def closure(m,seen=None):
 if m in memo:return memo[m]
 c={m}
 for d in deps(m):c|=closure(d)
 memo[m]=c;return c
files=Path('docs/audits/2026-11-18_pin729_mps_shard/manifest.txt').read_text().splitlines()
a=sorted((len(closure(p[:-5].replace('/','.'))),p) for p in files)
print(a[:20]);print('total narrow project closure',len(set().union(*(closure(p[:-5].replace('/','.')) for p in files))))
Path('/tmp/mps-closures.json').write_text(json.dumps({p:sorted(closure(p[:-5].replace('/','.'))) for p in files}))
