import json,hashlib,re,subprocess,collections
from pathlib import Path
root=Path('/tmp/interaction-mps78'); old=Path('/tmp/pin729-mps'); aud=old/'docs/audits/2026-11-18_pin729_mps_shard'; out=root/'docs/audits/2026-11-18_interaction_combined_checks/mps78';out.mkdir(exist_ok=True)
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
coverage=json.loads((out.parent/'coverage.json').read_text()); allm=[x for x in coverage if x['lane']=='mps'];pending=sorted(x['path'] for x in allm if x['compile']!='PASS exact source' or x['strict']!='PASS exact source');done=sorted(x['path'] for x in allm if x['path'] not in pending)
assert len(allm)==86 and len(done)==8 and len(pending)==78
(out/'manifest.txt').write_text('\n'.join(pending)+'\n');(out/'already-verified8.txt').write_text('\n'.join(done)+'\n')
base='42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d';pin='729428582b78ab7529b3796099193649f947354a'
roots={'TNLean':root,'QICLean':Path('/tmp/qic729-mps'),'Cslib':Path('/tmp/pin729-cslib')};graph={};source={}
def src(m):return roots[m.split('.')[0]]/(m.replace('.','/')+'.lean')
def visit(m):
 if m in graph:return
 p=src(m);assert p.exists(),p
 source[m]=hashfile(p);ds=set()
 for line in p.read_text().splitlines():
  if re.match(r'^(?:public |private )?import ',line): ds|={t for t in line.split('import ',1)[1].split() if t.split('.')[0] in roots}
 graph[m]=ds
 for d in ds:visit(d)
for f in pending:visit(f[:-5].replace('/','.'))
cache=Path('/tmp/pin729-mps-olean');snapshot={r['file']:r for r in json.loads((aud/'cache-artifacts.json').read_text())}
rows=[json.loads(l) for l in (aud/'results.jsonl').read_text().splitlines()];records={r['file']:r for r in rows if r['phase']=='build' and r['exit_code']==0}
for r in [json.loads(l) for l in (aud/'cslib-results.jsonl').read_text().splitlines()]:
 # CSLib records handled separately below if absent from TN/QIC closure.
 records[r['file']]=r
usable={};reason={}
def check(m):
 if m in usable:return usable[m]
 f=m.replace('.','/')+'.lean';r=records.get(f,snapshot.get(f,{}));sha=r.get('source_sha256',snapshot.get(f,{}).get('source_sha256'));artifact=cache/(m.replace('.','/')+'.olean')
 deps=all([check(d) for d in graph[m]])
 if sha!=source[m]:reason[m]='source changed or no completed-source evidence'
 elif not artifact.exists() or hashfile(artifact)!=r.get('olean_sha256',snapshot.get(f,{}).get('olean_sha256')):reason[m]='artifact absent or hash mismatch'
 elif not deps:reason[m]='transitive dependency cannot be reused'
 else:reason[m]='exact source/artifact and all project dependencies match'
 usable[m]=reason[m].startswith('exact ');return usable[m]
for m in graph:check(m)
manifest=json.loads((root/'lake-manifest.json').read_text());oldmanifest=json.loads((old/'lake-manifest.json').read_text());assert manifest==oldmanifest,'package manifest differs'
assert (root/'lean-toolchain').read_bytes()==(old/'lean-toolchain').read_bytes()
plan={'head':base,'production_head':'42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d','qic_pin':pin,'manifest_sha256':hashfile(out/'manifest.txt'),'selected':78,'excluded_prior_passes':8,'project_closure':len(graph),'reusable':sum(usable.values()),'requires_compile':sum(not v for v in usable.values()),'reasons':dict(collections.Counter(reason[m] for m in graph)),'cache_action':'read-only inspection only; independent overlay not populated while old queue remains active','package_manifest_identical':True,'toolchain_identical':True,'old_queue_pid':412863,'new_compiler_started':False,'handoff_condition':'old queue finishes/drains all compiler writers; then refresh hash plan and copy only eligible completed artifacts to independent overlay. Retain 1 GiB disk guard; do not add workers to existing 2-worker queue.'}
(out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n');(out/'dependency-plan.json').write_text(json.dumps([{'module':m,'source_sha256':source[m],'dependencies':sorted(graph[m]),'reusable':usable[m],'reason':reason[m]} for m in sorted(graph)],indent=2)+'\n')
print(json.dumps(plan,indent=2))
