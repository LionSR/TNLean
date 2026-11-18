import pathlib,json,shutil,tarfile,hashlib,datetime
src=pathlib.Path('/workspace/reviews/interaction-peps-remaining');out=pathlib.Path('/workspace/tn-peps-evidence/docs/audits/2026-11-18_interaction_peps_remaining');out.mkdir(parents=True,exist_ok=True)
for p in src.iterdir():
 if p.suffix in ['.json','.jsonl','.txt','.py','.stdout']:shutil.copy2(p,out/p.name)
rows=[json.loads(s) for s in (src/'results.jsonl').read_text().splitlines()];targetpaths=(src/'manifest.txt').read_text().splitlines();targets={p[:-5].replace('/','.') for p in targetpaths};status=[]
for path in targetpaths:
 m=path[:-5].replace('/','.');row={'path':path}
 for ph in ['compile','strict','blocked']:
  rs=[x for x in rows if x['module']==m and x['phase']==ph];row[ph]=rs[-1]['exit_code'] if rs else None
 status.append(row)
(out/'target-status.json').write_text(json.dumps(status,indent=2)+'\n')
summary={'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':'dccc85e5607077b51822664e9d475287d300d607','qic_pin':'729428582b78ab7529b3796099193649f947354a','manifest_count':90,'manifest_sha256':hashlib.sha256((src/'manifest.txt').read_bytes()).hexdigest(),'compile_pass_commands':sum(x['phase']=='compile' and x['exit_code']==0 for x in rows),'target_compile_pass':sum(x['compile']==0 for x in status),'target_strict_pass':sum(x['strict']==0 for x in status),'failures':sum(x['exit_code']!=0 for x in rows),'compiler_seconds':sum(x.get('seconds',0) for x in rows),'disk_free_bytes':shutil.disk_usage(src).free,'status':'LIVE CHECKPOINT; consult process status; not whole-lane clearance'}
(out/'snapshot.json').write_text(json.dumps(summary,indent=2)+'\n')
with tarfile.open(out/'logs.tar.gz','w:gz') as tar:
 for p in src.glob('*.log'):tar.add(p,arcname=p.name)
print(json.dumps(summary))
