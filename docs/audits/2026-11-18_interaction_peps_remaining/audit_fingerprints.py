import pathlib,json,hashlib,tarfile,io
p=pathlib.Path('/workspace/reviews/interaction-peps-remaining');shared=pathlib.Path('/workspace/reviews/interaction-shared-validation');warm=pathlib.Path('/workspace/tn-pin729-other');q=warm/'.lake/packages/qiclean';g=json.loads((p/'imports.json').read_text());data=json.loads((p/'source-hashes.json').read_text());sources=data['sources'];packages=data['packages'];paths=[shared/'olean',warm/'.lake/build/lib/lean',q/'.lake/build/lib/lean',pathlib.Path('/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/lib/lean')]+[d/'.lake/build/lib/lean' for d in (warm/'.lake/packages').iterdir() if d.name!='qiclean'];records=[json.loads(s) for s in (p/'results.jsonl').read_text().splitlines()];cache={};memo={}
def sha(b):return hashlib.sha256(b).hexdigest()
def closure(m):
 if m not in memo:
  memo[m]={m}
  for d in g.get(m,[]):memo[m]|=closure(d)
 return memo[m]
def artifact(m):
 if m not in cache:
  for root in paths:
   file=root/(m.replace('.','/')+'.olean')
   if file.exists():cache[m]={'path':str(file),'sha256':sha(file.read_bytes())};break
  else:raise RuntimeError('missing artifact '+m)
 return cache[m]['sha256']
seen={};mismatches=[];checked=0
with tarfile.open(p/'dependency-fingerprints.tar.gz','w:gz') as tar:
 for row in records:
  if 'dependency_fingerprint' not in row:continue
  m=row['module'];obj={'sources':{d:sources[d] for d in sorted(closure(m)) if d in sources},'artifacts':{d:artifact(d) for d in sorted(closure(m)-{m})},'packages':packages};raw=json.dumps(obj,sort_keys=True).encode();fp=sha(raw);checked+=1
  if fp!=row['dependency_fingerprint']:mismatches.append({'module':m,'phase':row['phase'],'old':row['dependency_fingerprint'],'current':fp})
  if fp not in seen:
   seen[fp]=True;info=tarfile.TarInfo(fp+'.json');info.size=len(raw);tar.addfile(info,io.BytesIO(raw))
(p/'all-dependency-artifacts.json').write_text(json.dumps(cache,indent=2)+'\n');report={'checked_commands':checked,'unique_fingerprints':len(seen),'artifact_modules':len(cache),'mismatches':mismatches,'note':'Reconstructed fingerprints must exactly match original pre-command fingerprints. This does not count as compilation.'};(p/'fingerprint-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));raise SystemExit(bool(mismatches))
