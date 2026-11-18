from pathlib import Path
import json,hashlib
r=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
xs=[json.loads(l) for l in (r/'results.jsonl').read_text().splitlines()];seen={};fail=[]
for x in xs:
 d=json.loads((r/(x['dependency_fingerprint']+'.json')).read_text());assert sha(json.dumps(d,sort_keys=True).encode())==x['dependency_fingerprint']
 for a in [*d['artifacts'].values(),x['artifact']]:
  if a['path'] not in seen:seen[a['path']]=sha(Path(a['path']).read_bytes())
  if seen[a['path']]!=a['sha256']:fail.append(a['path'])
assert not fail,fail
(r/'fingerprint-audit.json').write_text(json.dumps(dict(commands=len(xs),unique_artifacts=len(seen),mismatches=fail),indent=2)+'\n');print((r/'summary.json').read_text());print('audited',len(seen))
