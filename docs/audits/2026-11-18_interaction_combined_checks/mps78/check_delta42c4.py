import re,subprocess,collections,json,hashlib,datetime
from pathlib import Path
root=Path('/tmp/interaction-mps78');out=root/'docs/audits/2026-11-18_interaction_combined_checks/mps78';delta='42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d';base='dccc85e5607077b51822664e9d475287d300d607';g={};rev=collections.defaultdict(set)
changed=subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',delta],cwd=root,text=True).splitlines()
for p in list(root.glob('TNLean/**/*.lean'))+[root/'TNLean.lean']:
 ds=set()
 for line in p.read_text().splitlines():
  if re.match(r'^(?:public |private )?import ',line):ds|={x for x in line.split('import ',1)[1].split() if x.startswith('TNLean.')}
 m=str(p.relative_to(root))[:-5].replace('/','.');g[m]=ds
 for d in ds:rev[d].add(m)
affected={x[:-5].replace('/','.') for x in changed};q=list(affected)
while q:
 for m in rev[q.pop()]:
  if m not in affected:affected.add(m);q.append(m)
assert len(affected)==25
manifest={p[:-5].replace('/','.') for p in (out/'manifest77.txt').read_text().splitlines()};intersection=sorted(affected&manifest)
load=lambda p:[json.loads(x) for x in p.read_text().splitlines()] if p.exists() else []
new=load(out/'results77.jsonl');passed={r['module'] for r in new if r['phase']=='strict' and r['exit_code']==0};old=load(Path('/tmp/pin729-mps/docs/audits/2026-11-18_pin729_mps_shard/results.jsonl'));oldpass={r['file'][:-5].replace('/','.') for r in old if r['phase']=='strict' and r['exit_code']==0};cov=json.loads((out.parent/'coverage.json').read_text());priorpass={r['path'][:-5].replace('/','.') for r in cov if r['lane']=='mps' and r['compile']=='PASS exact source' and r['strict']=='PASS exact source'}
paths=lambda ms:[m.replace('.','/')+'.lean' for m in sorted(ms)]
(out/'delta42c4-closure25.txt').write_text('\n'.join(paths(affected))+'\n');(out/'delta42c4-intersection.txt').write_text('\n'.join(paths(intersection))+'\n')
report={'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':base,'delta':delta,'method':'Independently reconstructed complete TNLean reverse-import closure from unchanged imports; exact 25. Author manifest is not present in the three-file commit.','changed_files':changed,'closure25_sha256':hashlib.sha256((out/'delta42c4-closure25.txt').read_bytes()).hexdigest(),'intersection_count':len(intersection),'intersection':paths(intersection),'outside77':paths(affected-manifest),'combined77_passed':paths(set(intersection)&passed),'combined77_pending':paths(set(intersection)-passed),'combined_prior8_passed':paths(affected&priorpass),'old865_passed_not_combined_validation':paths(affected&oldpass),'old865_pending':paths((affected&{x[:-5].replace('/','.') for x in Path('/tmp/pin729-mps/docs/audits/2026-11-18_pin729_mps_shard/manifest.txt').read_text().splitlines()})-oldpass),'execution':'No new source, cache or running coordinator changed. Delta not compiled.','future':'After old77 writers stop, let 695c integrate exact delta into final overlay. Invalidate changed owners and complete reverse dependency closure; rebuild required owners even outside77 as dependencies, then one build/strict pass for each intersection target. Keep delta evidence separate from dccc. Reuse other modules only when their complete transitive source/artifact hashes still match.'}
(out/'delta42c4-status.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
